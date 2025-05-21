// -*- mode: Bluespec; -*-

module consensus {
  import basicSpells.* from "./basicSpells"
  import alpenglow.* from "./alpenglow"

  type ProcessID = str

  /// Set of correct processes (non Byzantine)
  const correct: Set[ProcessID]

  /// Set of processes that follow the algorithm but might fail in a benign way
  const good: Set[ProcessID]

  /// Set of Byzantine processes
  const byzantine: Set[ProcessID]

  /// Set of blocks
  const correctBlocks: Set[Block]
  /// Set of Byzantine blocks
  const byzantineBlocks: Set[Block]

  /// Set of all blocks
  pure val allBlocks = correctBlocks.union(byzantineBlocks)

  /// Set of correct processes and processes that follow the algorithm but might fail in a benign way
  pure val benevolent = correct.union(good)

  pure val maxSlot = allBlocks.fold(-1, (s, x) => max(x.slot, s))

  /// Slots for which this model considers votes
  const aliveSlots: Set[Slot]
  /// Hashes for which this model considers votes
  const aliveHashes: Set[Blockhash]

  //
  // Constraints on the number of processes
  //

  assume uniqueRole = and {
    correct.intersect(byzantine) == Set(),
    correct.intersect(good) == Set(),
    good.intersect(byzantine) == Set(),
  }

  pure val numProcesses = correct.size() + good.size() + byzantine.size()

  // Assumption 1 and Assumption 2
  assume resilienceCondition = all {
    numProcesses > byzantine.size() * 5, // N > 5F
    numProcesses > good.size() * 5,
  }

  /// Checks for thresholds, using the known number of processes
  pure def surpassesThreshold(votes, threshold) =
    votes.size() * 100 >= numProcesses * threshold

  /// Messages on the network carry the sender (the broadcast call in the pseudo code
  /// doesn't carry the sender, so does our encoding of the consensus main loop)
  type NetworkMsg = {
    sender: ProcessID,
    msg: Message,
  }

  /// All votes that can be sent by the Byzantine processes (without senders)
  pure val byzMessages = tuples(aliveSlots, aliveHashes).map(((slot, hash)) =>
    Set(
      NotarVoteMsg({ slot: slot, hash: hash }),
      NotarFallBackVoteMsg({ slot: slot, hash: hash }),
      SkipVoteMsg(slot),
      SkipFallbackVoteMsg(slot),
      FinalVoteMsg(slot)
    )
  ).flatten()

  /// All votes that can be sent by the Byzantine processes
  pure val byzNetworkMsgs = tuples(byzantine, byzMessages).map(((sender, msg)) =>
    { sender: sender, msg: msg }
  )

  // Definition 5 (ancestor and descendant). An ancestor of a block b is any
  // block that can be reached from b by the parent links, i.e., b, b’s parent,
  // b’s parent’s parent, and so on. If b′ is an ancestor of b, b is a
  // descendant of b′ . Note that b is its own ancestor and descendant.
  pure def isDescendant(a: Block, b: Block): bool =
    // TODO: this can have better performance if we can make assumptions about slots
    allBlocks.fold(Set(b.hash), (s, x) =>
      allBlocks.fold(s, (s, x) =>
        if (s.exists(hash => x.parent == hash))
          s.union(Set(x.parent))
        else
          s
      )
    ).contains(a.hash)

  /// This is all the information of the global state
  type Environment = {
    // The local state of each process
    system: ProcessID -> LocalState,
    // Global time, we can push to different views of slots later
    now: Slot,
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


  // Definition 13 (certificates)
  // They are defined over a set of messages. Currently we evaluate this over the
  // message soup. But they can be also used over locally received messages if such
  // a semantics is needed.

  type Certificate =
    | FastFinalizationCertificate(BlockReference)
    | NotarizationCertificate(BlockReference)
    | NotarFallbackCertificate(BlockReference)
    | SkipCertificate(Slot)
    | FinalizationCertificate(Slot)

  /// Table 5: Apenglow's certificate messages.
  pure def isCertified(cert: Certificate, msgs: Set[NetworkMsg]): bool = {
    pure val aggregatedVotes = msgs.filter(m => {
      match cert {
        | FastFinalizationCertificate(b) =>
          m.msg == NotarVoteMsg(b)
        | NotarizationCertificate(b) =>
          m.msg == NotarVoteMsg(b)
        | NotarFallbackCertificate(b) =>
          m.msg == NotarVoteMsg(b) or m.msg == NotarFallBackVoteMsg(b)
        | SkipCertificate(s) =>
          m.msg == SkipVoteMsg(s) or m.msg == SkipFallbackVoteMsg(s)
        | FinalizationCertificate(s) =>
          m.msg == FinalVoteMsg(s)
      }
    })

    pure val threshold = match cert {
      | FastFinalizationCertificate => 80
      | NotarizationCertificate => 60
      | NotarFallbackCertificate => 60
      | SkipCertificate => 60
      | FinalizationCertificate => 60
    }

    aggregatedVotes.surpassesThreshold(threshold)
  }

  // Definition 14 (finalization). We have two ways to finalize a block:
  // Warning: definitions uses "unique" perhaps unclear in case of more faults

  /// If a finalization certificate on slot s is in Pool, the unique notarized block
  /// in slot s is finalized (we call this slow-finalized).
  pure def finalized(slot: Slot, msgs: Set[NetworkMsg]): Set[Blockhash] =
    notarizedBlocks(msgs) // we derive the blocks from the votes in msgs here
      .filter(b => b.slot == slot)
      .filter(b => {
        isCertified(FinalizationCertificate(b.slot), msgs)
          and isCertified(NotarizationCertificate(b), msgs)
      })
      .map(b => b.hash)

  /// If a fast-finalization certificate on block b is in Pool, the block b is
  /// finalized (fast-finalized).
  pure def fastFinalized(slot: Slot, msgs: Set[NetworkMsg]): Set[Blockhash] =
    notarizedBlocks(msgs)
      .filter(b => b.slot == slot)
      .filter(b => isCertified(FastFinalizationCertificate(b), msgs))
      .map(b => b.hash)

  //
  //
  // State Machine
  //
  //

  var s: Environment

  /// all the messages that could be received, i.e., the ones sent by benevolent processes
  /// and the ones that byzantine processes may send. We use this in the actions to allow
  /// processes to respond to byzantine behavior. At the same time, we don't clutter
  /// msgBuffer with byzantine messages.
  val allMessages = s.msgBuffer.union(byzNetworkMsgs)

  action init = all {
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
      now: 0,
      msgBuffer: Set(),
      activeTimeouts: benevolent.mapBy(v => Set()),
    }
  }

  /// Emit Block and process it
  /// Warning: The pseudo code uses s. Does this mean s is checked against the local
  /// view of the slot, and thus only "current" blocks can be received, or could BlockInput(block)
  /// could also be executed for blocks from future slots?
  /// This question applies to all "upon"s
  action receiveBlock(v: ProcessID, now: Slot): bool = all{
    nondet block = allBlocks.filter(b => b.slot == now).oneOf()
    v.processInput(BlockInput(block))
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

  pure def notarizedBlocks(msgs: Set[NetworkMsg]): Set[BlockReference] =
    msgs
      .fold(Set(), (s, x) => match x.msg {
        | NotarVoteMsg(m) => s.union(Set(m))
        | _ => s
      })
      .filter(b => isCertified(NotarizationCertificate(b), msgs))

  pure def notarFallbackBlocks(msgs: Set[NetworkMsg]): Set[BlockReference] =
    msgs
      .fold(Set(), (s, x) => match x.msg {
        | NotarVoteMsg(m) => s.union(Set(m))
        | NotarFallBackVoteMsg(m) => s.union(Set(m))
        | _ => s
      })
      .filter(b => isCertified(NotarFallbackCertificate(b), msgs))

  pure def slotsSkipCertified(msgs: Set[NetworkMsg]): Set[Slot] =
    msgs
      .fold(Set(), (s, x) => match x.msg {
        | SkipVoteMsg(m) => s.union(Set(m))
        | _ => s
      })
      .filter(s => isCertified(SkipCertificate(s), msgs))

  action processInput(id: ProcessID, input: ConsensusInput): bool = {
    s' = applyEffect(s, id, consensus(s.system.get(id), input))
  }

  // Definition 15 (Pool events). The following events are emitted as input for
  // Algorithm 1:

  // • BlockNotarized(slot(b), hash(b)): Pool holds a notarization certificate for
  // block b.
  def notarizedBlocksCondition(v: ProcessID, now: Slot, b: BlockReference): bool =
    notarizedBlocks(allMessages).contains(b)

  /// Emit BlockNotarized and process it. The structure of this actions is that we first
  /// build a set of data (blocks or slot numbers) for which a certain event is enabled,
  /// and then we pick one non-deterministically, process it, and updated the global state.
  action blockNotarizedAction(v: ProcessID, now: Slot): bool =
    val bs = allBlocks.filter(b => notarizedBlocksCondition(v, now, { slot: b.slot, hash: b.hash }))
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
    val pool = notarizedBlocks(msgs).filter(b => b.hash == hash and b.slot == slot)
    pool.exists(b =>
      and {
        b.slot < slot, // previous block
        or {
          isCertified(NotarizationCertificate(b), msgs),
          isCertified(NotarFallbackCertificate(b), msgs)
        },
        b.slot.to(slot).subseteq(slotsSkipCertified(msgs))
    })
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
    allBlocks.filter(b => b.slot == now).contains(b),
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
    allMessages
      .filter(m => m.sender == v and slotOf(m.msg) == now)
      .filter(m => match m.msg {
        | SkipVoteMsg(s) => false
        | _ => true
      })
      .size() > 0,

    val blocksWithNotarVotes =
      allMessages
        .filter(m => slotOf(m.msg) == now)
        .fold(Set(), (s, m) => match m.msg {
          | NotarVoteMsg(n) => s.setAdd(n)
          | _ => s
        })

    val maxNotar = blocksWithNotarVotes.fold({ slot: -1, hash: -1 }, (res, x) => {
      if (votedToNotar(x, allMessages).size() > votedToNotar(res, allMessages).size())
        x
      else
        res
    })

    val sumNotar = blocksWithNotarVotes.fold(Set(), (res, b) =>
      res.union(votedToNotar(b, allMessages)))

    votedToSkip(now, allMessages).union(sumNotar).exclude(
      votedToNotar(maxNotar, allMessages)
    ).surpassesThreshold(40)
  }

  // Emit SafeToSkip and process it
  action safeToSkipAction(v: ProcessID, now: Slot): bool = all {
    safeToSkipCondition(v, now),
    v.processInput(SafeToSkipInput(now)),
  }

  /// Any upon that is triggered by messages
  action messageResponse =
    nondet v = oneOf(benevolent)
    // we pass the global time here, but we might also model that a validator is ahead / behind time
    any {
      receiveBlock(v, s.now),
      blockNotarizedAction(v, s.now),
      parentReadyAction(v, s.now),
      safeToNotarAction(v, s.now),
      safeToSkipAction(v, s.now),
    }

  /// increment the global time (slot number)
  action tick = all {
    s.now < maxSlot, // make sure we don't enter a slot for which we don't have a block in the model
    s' = { ... s, now: s.now + 1 }
  }

  /// Main step action. Includes all behavior
  action step = any {
    messageResponse,
    nondet v = oneOf(benevolent)
    fireTimeoutEvent(v, s.now),
    tick,
  }

  /// Alternative step action. With this, no timeout ever expires
  action noTimeout = any {
    messageResponse,
    tick,
  }

  /// Alternative step action. With this, we never tick (leave slot 0)
  action oneSlot = any {
    messageResponse,
    nondet v = oneOf(benevolent)
    fireTimeoutEvent(v, s.now),
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
    0.to(s.now).forall(slot => finalized(slot, allMessages).size() <= 1)

  val fastAgreement =
    0.to(s.now).forall(slot => fastFinalized(slot, allMessages).union(finalized(slot, allMessages)).size() <= 1)

  // Witness was used to find bug in safeToNotar encoding
  val noBad =
    benevolent.forall(v => not(s.system.get(v).state[1].contains(BadWindow)))

  /// Witness to find a run where a block is fast finalized
  val fastFinalizedWitness =
    allBlocks.forall(b => not(isCertified(FastFinalizationCertificate(b.reference()), allMessages)))

  val slots = 0.to(s.now)

  /// Theorem 1 (safety). If any correct node finalizes a block b in slot s and any
  /// correct node finalizes any block b′ in any slot s′ ≥ s, b′ is a descendant of b.
  val safety = tuples(slots, allBlocks).forall(((slot, block)) => {
    val finalizedAtSlot = finalized(slot, allMessages)
    block.hash.in(finalizedAtSlot) implies tuples(slot.to(s.now), allBlocks).forall(((slot2, block2)) => {
      block2.hash.in(finalized(slot2, allMessages)) implies block2.isDescendant(block)
    })
  })

  // TODO finalize ancestors
}

module some_byz {
  // For a trace where a value is fast finalized call
  // quint run statemachine.qnt --main some_byz --invariant fastFinalizedWitness

  import consensus(
    correct = Set("v1", "v2", "v3", "v4", "v5"),
    good = Set(),
    byzantine = Set("b1"),
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
}

module too_many_byz_1 {
  // to violate agreement, run
  // quint run statemachine.qnt --main too_many_byz_1 --step oneSlotNoTimeout  --invariant agreement

  import consensus(
    correct = Set("v1", "v2", "v3", "v4"),
    good = Set(),
    byzantine = Set("b1"),
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
  // quint run statemachine.qnt --main too_many_byz --step oneSlotNoTimeout  --invariant agreement

  import consensus(
    correct = Set("v1", "v2", "v3", "v4"),
    good = Set(),
    byzantine = Set("b1", "b2"),
    correctBlocks = Set({ slot: 0, hash: 42, parent: -1 }),
    byzantineBlocks = Set({ slot: 0, hash: 41, parent: -1 }),
    aliveSlots = Set(0),
    aliveHashes = 41.to(42),
  ).*
}
