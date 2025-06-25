// -*- mode: Bluespec; -*-

module consensus {
  import basicSpells.* from "./basicSpells"
  import alpenglow.* from "./alpenglow"
  export alpenglow.*

  /// This is all the information of the global state
  type Environment = {
    // The local state of each process
    system: ProcessID -> LocalState,
    //powers: ProcessID -> int, TODO
    
    // Global time, we can push to different views of slots later
    // now: Slot,

    // Messages sent so far, a.k.a. the message soup
    msgBuffer: Set[NetworkMsg],
    // Started timeouts per process
    activeTimeouts: ProcessID -> Set[TimeoutEventData],
  }

  /// Interface consensus algorithm / state machine: how consensus algorithm effects the environment
  pure def applyEffect(env: Environment, v: ProcessID, res: Result): Environment =
    val new = { ... env, system: env.system.set(v, res.post) } // update the state of the process
    res.output.fold(new, (s, o) =>
      match o {
        | Broadcast(msg) =>
          val nm = { sender: v, msg: msg }
          { ...s, msgBuffer: s.msgBuffer.union(Set(nm)) }
        | ScheduleEventTimeout(slot) =>
          { ...s, activeTimeouts: s.activeTimeouts.set(v, s.activeTimeouts.get(v).union(Set(slot))) }
      })

  //
  //
  // State Machine
  //
  //

  var s: Environment
//  var counter: int // Required for TLC

  /// all the messages that could be received, i.e., the ones sent by benevolent processes
  /// and the ones that byzantine processes may send. We use this in the actions to allow
  /// processes to respond to byzantine behavior. At the same time, we don't clutter
  /// msgBuffer with byzantine messages.
  val allMessages = s.msgBuffer.union(byzNetworkMsgs)

  action init = all {
  //  counter' = 0,
    s' = {
      system: benevolent.mapBy(_ => {
        state: [
          Set(ParentReady(-1)),
          Set(),
          Set(),
          Set(),
          Set(),
        ],
        pendingBlocks: [None, None, None, None, None]
      }),
      // now: 0,
      msgBuffer: Set(),
      activeTimeouts: benevolent.mapBy(v => Set()),
    }
  }

  action receiveSpecificBlock(v: ProcessID, b: Block): bool = all {
    allBlocks.contains(b),
    v.processInput(BlockInput(b))
  }

  /// Emit Block and process it
  /// Warning: The pseudo code uses s. Does this mean s is checked against the local
  /// view of the slot, and thus only "current" blocks can be received, or could BlockInput(block)
  /// could also be executed for blocks from future slots?
  /// This question applies to all "upon"s
  action receiveBlock(v: ProcessID, now: Slot): bool = all{
    nondet block = allBlocks.filter(b => b.slot == now).oneOf()
    receiveSpecificBlock(v, block)
  }

  /// Fire timeout for current slot
  action fireTimeoutEvent(v: ProcessID, now: Slot): bool = all {
    s.activeTimeouts.get(v).contains(now),
    val s2 = { ...s, activeTimeouts: s.activeTimeouts.set(v, s.activeTimeouts.get(v).exclude(Set(now))) }
    s' = applyEffect(s2, v, consensus(s2.system.get(v), TimeOutInput(now)))
  }

  //
  // auxiliary functions for actions below
  //


  action processInput(id: ProcessID, input: ConsensusInput): bool = {
    s' = applyEffect(s, id, consensus(s.system.get(id), input))
  }

  // Definition 15 (Pool events). The following events are emitted as input for
  // Algorithm 1:

  // • BlockNotarized(slot(b), hash(b)): Pool holds a notarization certificate for
  // block b.
  def notarizedBlocksCondition(v: ProcessID, b: BlockReference): bool =
    isCertified(NotarizationCertificate(b), allMessages)

  /// Emit BlockNotarized and process it. The structure of this actions is that we first
  /// build a set of data (blocks or slot numbers) for which a certain event is enabled,
  /// and then we pick one non-deterministically, process it, and updated the global state.
  action blockNotarizedAction(v: ProcessID, now: Slot): bool =
    val bs = allBlocks.filter(b =>
      notarizedBlocksCondition(v, { slot: now, hash: b.hash })
    )
    all {
      bs.size() > 0,
      nondet b = bs.oneOf()
      v.processInput(BlockNotarizedInput({ slot: b.slot, hash: b.hash }))
    }

  // • ParentReady(s, hash(b)): Slot s is the first of its leader window, and Pool
  // holds a notarization or notar-fallback certificate for a previous block b,
  // and skip certificates for every slot s′ since b, i.e., for slot(b) < s′ < s.
  //
  // Warning "notarization or notar-fallback": notar-fallback seems to imply notar
  // Warning: Previous block? Block for previous slot
  pure def parentReadyCondition(slot: Slot, hash: Blockhash, msgs: Set[NetworkMsg]): bool = all {
    firstSlotInLeaderWindow(slot),
    0.to(slot - 1).exists(s =>
      val b = { slot: s, hash: hash }
      and {
        or {
          isCertified(NotarizationCertificate(b), msgs),
          isCertified(NotarFallbackCertificate(b), msgs)
        },
        b.slot.to(slot).subseteq(slotsSkipCertified(msgs))
      }
    )
  }

  /// Emit ParentReady and process it
  action parentReadyAction(v: ProcessID, now: Slot): bool =
    val bs = allBlocks.filter(b => parentReadyCondition(now, b.hash, allMessages))
    all {
      bs.size() > 0,
      nondet b = bs.oneOf()
      v.processInput(ParentReadyInput({slot: now, hash: b.hash}))
    }

  /// Definition 16 (fallback events)

  pure def votedToSkip(s: Slot, msgs: Set[NetworkMsg]): Set[ProcessID] =
    msgs.filter(m =>  m.msg == SkipVoteMsg(s)).map(m => m.sender)

  // Warning: vote doesn't contain parent. Assumption about parent hashed in hash?
  pure def votedToNotar(b: BlockReference, msgs: Set[NetworkMsg]): Set[ProcessID] =
    msgs.filter(m => m.msg == NotarVoteMsg(b)).map(m => m.sender)

  // • SafeToNotar(s, hash(b)): The event is only issued if the node voted in
  // slot s already, but not to notarize b.
  def safeToNotarCondition(v: ProcessID, now: Slot, b: Block): bool = all {
    // Consider block b in slot s = slot(b).
    b.slot == now,

    val voted = allMessages.filter(m => m.sender == v and now == slotOf(m.msg))
    val notarVoted =
      voted.filter(m => match m.msg {
        | NotarVoteMsg(m) => true
        | _ => false
      })

    and {
      voted.size() > 0,
      notarVoted.size() == 0,
    },
    val notar = votedToNotar(b.reference(), allMessages)
    val skip = votedToSkip(now, allMessages)
    // notar(b) ≥ 40% or (skip(s) + notar(b) ≥ 60% and notar(b) ≥ 20%).
    // Question: is (+) here the sum of the sizes or the size of the union?
    or {
      surpassesThreshold(notar, 40),
      and {
        surpassesThreshold(skip.union(notar), 60),
        surpassesThreshold(notar, 20)
      }
    }
  }

  // Emit SafeToNotar and process it
  action safeToNotarAction(v: ProcessID, now: Slot): bool =
    val bs = allBlocks.filter(b => safeToNotarCondition(v, now, b))
    all {
      bs.size() > 0,
      nondet b = bs.oneOf()
      v.processInput(SafeToNotarInput({ slot: b.slot, hash: b.hash })),
    }

  // • SafeToSkip(s): The event is only issued if the node voted in slot s already,
  // but not to skip s.
  def safeToSkipCondition(v: ProcessID, now: Slot): bool = all {
    // node voted in slot s already, but not to skip s.
    allMessages.exists(m =>
      m.sender == v
      and slotOf(m.msg) == now
      and m.msg != SkipVoteMsg(now)
    ),

    // Moreover:
    // skip(s) + Σ_b notar(b) − max_b notar(b) ≥ 40%.
    val blocksWithNotarVotes =
      allMessages
        .filter(m => slotOf(m.msg) == now)
        .fold(Set(), (s, m) => match m.msg {
          | NotarVoteMsg(n) => s.setAdd(n)
          | _ => s
        })

    // Σ_b notar(b)
    val allNotarVotes = blocksWithNotarVotes.map(b =>
      votedToNotar(b, allMessages)
    ).flatten()

    // max_b
    val blockWithMostVotes = blocksWithNotarVotes.fold({ slot: -1, hash: -1 }, (res, x) => {
      if (votedToNotar(x, allMessages).size() > votedToNotar(res, allMessages).size())
        x
      else
        res
    })

    // skip(s) + Σ_b notar(b) − max_b notar(b) ≥ 40%.
    // Question: is (+) here the sum of the sizes or the size of the union?
    // same for (-)

    // skip(s)
    votedToSkip(now, allMessages)
      // + Σ_b notar(b)
      .union(allNotarVotes)
      // - max_b notar(b)
      .exclude(votedToNotar(blockWithMostVotes, allMessages))
      // ≥ 40%.
      .surpassesThreshold(40)
  }

  // Emit SafeToSkip and process it
  action safeToSkipAction(v: ProcessID, now: Slot): bool = all {
    safeToSkipCondition(v, now),
    v.processInput(SafeToSkipInput(now)),
  }

  /// Any upon that is triggered by messages
  action messageResponse =
    nondet v = oneOf(benevolent)
    nondet slot = oneOf(aliveSlots)
    // we pass the global time here, but we might also model that a validator is
    // ahead / behind time
    any {
      // Question: Are all of these fired only for now or can they also be fired
      // for future/past slots?
      receiveBlock(v, slot),
      blockNotarizedAction(v, slot),
      parentReadyAction(v, slot),
      safeToNotarAction(v, slot),
      safeToSkipAction(v, slot),
    }

  // /// increment the global time (slot number)
  // action tick = all {
  //   s.now < maxSlot, // make sure we don't enter a slot for which we don't have a block in the model
  //   s' = { ... s, now: s.now + 1 }
  // }

  /// Main step action. Includes all behavior
  action step = all {
  //  counter < 10,
  //  counter' = counter + 1,
    any {
      messageResponse,
      nondet v = oneOf(benevolent)
      nondet slot = oneOf(aliveSlots)
      fireTimeoutEvent(v, slot),
//      tick,
    }
  }

  /// Alternative step action. With this, no timeout ever expires
  action noTimeout = any {
    messageResponse,
  //  tick,
  }

  /// Alternative step action. With this, we never tick (leave slot 0)
  action oneSlot = any {
    messageResponse,
    nondet v = oneOf(benevolent)
    fireTimeoutEvent(v, 0),
  }

  /// Alternative step action. With this, no timeout ever expires and we never tick
  action oneSlotNoTimeout =
    messageResponse

  //
  //
  // Invariants and Witnesses
  //
  //

  val agreement =
    aliveSlots.forall(slot => finalized(slot, allMessages).size() <= 1)

  val fastAgreement =
    aliveSlots.forall(slot => fastFinalized(slot, allMessages).union(finalized(slot, allMessages)).size() <= 1)

  // Witness was used to find bug in safeToNotar encoding
  val noBad =
    benevolent.forall(v => not(s.system.get(v).state[1].contains(BadWindow)))

  /// Witness to find a run where a block is fast finalized
  val fastFinalizedWitness =
    allBlocks.forall(b => not(isCertified(FastFinalizationCertificate(b.reference()), allMessages)))


  /// Theorem 1 (safety). If any correct node finalizes a block b in slot s and any
  /// correct node finalizes any block b′ in any slot s′ ≥ s, b′ is a descendant of b.
  val safety = tuples(aliveSlots, allBlocks).forall(((slot, block)) => {
    val finalizedAtSlot = finalized(slot, allMessages)
    block.hash.in(finalizedAtSlot) implies tuples(
      aliveSlots.filter(s2 => s2 >= slot), allBlocks).forall(((slot2, block2)) => {
      block2.hash.in(finalized(slot2, allMessages)) implies block2.isDescendant(block)
    })
  })

  // TODO finalize ancestors
}

module some_byz {
  // For a trace where a value is fast finalized call
  // quint run statemachine.qnt --main some_byz --invariant fastFinalizedWitness
  // Same but one process reached ItsOver
  // quint run statemachine.qnt --main some_byz --invariant fastFinalizedWitness  --seed=0x11fa3a6ddd2666   
  import consensus(
    correct = Set("v1", "v2", "v3", "v4", "v5"),
    good = Set(),
    byzantine = Set("b1"),
    power = Set("v1", "v2", "v3", "v4", "v5", "b1").mapBy(_ => 1), 
    correctBlocks = Set(
      { slot: 0, hash: 42, parent: -1 },
      { slot: 1, hash: 43, parent: 42 },
      { slot: 2, hash: 44, parent: 43 },
    ),
    byzantineBlocks = Set(
      { slot: 1, hash: 46, parent: 42 },
      { slot: 1, hash: 47, parent: 45 },
      { slot: 2, hash: 48, parent: 43 },
      { slot: 2, hash: 49, parent: 45 },
    ),
    aliveSlots = 0.to(2),
    aliveHashes = 42.to(49),
  ).*

  run ffTest =
    init
    .then(receiveSpecificBlock("v1", { hash: 42, parent: -1, slot: 0 }))
    .then(receiveSpecificBlock("v2", { hash: 42, parent: -1, slot: 0 }))
    .then(receiveSpecificBlock("v3", { hash: 42, parent: -1, slot: 0 }))
    .then(receiveSpecificBlock("v4", { hash: 42, parent: -1, slot: 0 }))
    .expect(fastFinalized(0, allMessages) == Set(42))

}


module some_byz_vp {
  // For a trace where a value is fast finalized call
  // quint run statemachine.qnt --main some_byz --invariant fastFinalizedWitness
  // Same but one process reached ItsOver
  // quint run statemachine.qnt --main some_byz --invariant fastFinalizedWitness  --seed=0x11fa3a6ddd2666   
  import consensus(
    correct = Set("v1", "v2"),
    good = Set(),
    byzantine = Set("b1"),
    power = Map("v1" -> 3, "v2" -> 2, "b1"-> 1), 
    correctBlocks = Set(
      { slot: 0, hash: 42, parent: -1 },
      { slot: 1, hash: 43, parent: 42 },
      { slot: 2, hash: 44, parent: 43 },
    ),
    byzantineBlocks = Set(
      { slot: 1, hash: 46, parent: 42 },
      { slot: 1, hash: 47, parent: 45 },
      { slot: 2, hash: 48, parent: 43 },
      { slot: 2, hash: 49, parent: 45 },
    ),
    aliveSlots = 0.to(2),
    aliveHashes = 42.to(49),
  ).*

  run ffTest =
    init
    .then(receiveSpecificBlock("v1", { hash: 42, parent: -1, slot: 0 }))
    .then(receiveSpecificBlock("v2", { hash: 42, parent: -1, slot: 0 }))
    .expect(fastFinalized(0, allMessages) == Set(42))

}



module too_many_byz_1 {
  // to violate agreement, run
  // quint run statemachine.qnt --main too_many_byz_1 --step oneSlotNoTimeout  --invariant agreement

  import consensus(
    correct = Set("v1", "v2", "v3", "v4"),
    good = Set(),
    byzantine = Set("b1"),
    power = Set("v1", "v2", "v3", "v4", "b1").mapBy(_ => 1), 
    correctBlocks = Set(
      { slot: 0, hash: 42, parent: -1 },
      { slot: 1, hash: 43, parent: 42 },
      { slot: 2, hash: 44, parent: 43 },
    ),
    byzantineBlocks = Set(
      { slot: 0, hash: 45, parent: -1 },
      { slot: 1, hash: 46, parent: 42 },
      { slot: 1, hash: 47, parent: 45 },
      { slot: 2, hash: 48, parent: 43 },
      { slot: 2, hash: 49, parent: 45 },
    ),
    aliveSlots = 0.to(2),
    aliveHashes = 42.to(49),
  ).*
}

module too_many_byz {
  // to violate agreement, run
  // quint run statemachine.qnt --main too_many_byz --step oneSlotNoTimeout --invariant agreement

  import consensus(
    correct = Set("v1", "v2", "v3", "v4"),
    good = Set(),
    byzantine = Set("b1", "b2"),
    power = Set("v1", "v2", "v3", "v4", "b1", "b2").mapBy(_ => 1), 
    correctBlocks = Set({ slot: 0, hash: 42, parent: -1 }),
    byzantineBlocks = Set({ slot: 0, hash: 41, parent: -1 }),
    aliveSlots = Set(0),
    aliveHashes = 41.to(42),
  ).*
}
