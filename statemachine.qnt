// -*- mode: Bluespec; -*-

module consensus {
  import basicSpells.* from "./basicSpells"
  import alpenglow.* from "./alpenglow"

  type ProcessID = str

  pure def initial_local_state: LocalState =
   {
     state: [
       Set(ParentReady(-1)),
       Set(),
       Set(),
       Set(),
       Set(),
     ],
     pendingBlocks: [None, None, None, None, None]
  }

  /// Set of correct processes (non Byzantine)
  const correct: Set[ProcessID]
  /// Set of Byzantine processes
  const byzantine: Set[ProcessID]

  /// Set of blocks
  const correct_blocks: Set[Block]
  /// Set of Byzantine blocks
  const byz_blocks: Set[Block]

  /// Set of all blocks
  pure val all_blocks = correct_blocks.union(byz_blocks)

  /// Slots for which this model considers votes
  const alive_slots: Set[Slot]
  /// Hashes for which this model considers votes
  const alive_hashes: Set[Blockhash]

  // Assumption 1
  assume resilience_condition = correct.size() > byzantine.size() * 4 // N > 5F

  // Assumption 2 on additional crashes: TODO

  /// Threshold 20% of votes (not considering voting power)
  val twenty = correct.union(byzantine).size() * 20 / 100 + 1
  /// Threshold 40% of votes (not considering voting power)
  val forty = correct.union(byzantine).size() * 40 / 100 + 1
  /// Threshold 60% of votes (not considering voting power)
  val sixty = correct.union(byzantine).size() * 60 / 100 + 1
  /// Threshold 80% of votes (not considering voting power)
  val eighty = correct.union(byzantine).size() * 80 / 100 + 1

  type NetWorkMsg = {
    sender: ProcessID,
    msg: Message,
  }

  /// All votes that can be sent by the Byzantine processes (without senders)
  pure val byz_messages = tuples(alive_slots, alive_hashes).map(((slot, hash)) =>
    Set(
      NotarVoteMsg({ slot: slot, hash: hash }),
      NotarFallBackVoteMsg({ slot: slot, hash: hash }),
      SkipVoteMsg(slot),
      SkipFallbackVoteMsg(slot),
      FinalVoteMsg(slot)
    )
  ).flatten()

  /// All votes that can be sent by the Byzantine processes
  pure val byz_network_msgs = tuples(byzantine, byz_messages).map(((sender, msg)) =>
    { sender: sender, msg: msg }
  )

  // Definition 5 (ancestor and descendant). An ancestor of a block b is any
  // block that can be reached from b by the parent links, i.e., b, b’s parent,
  // b’s parent’s parent, and so on. If b′ is an ancestor of b, b is a
  // descendant of b′ . Note that b is its own ancestor and descendant.
  pure def is_descendant(a: Block, b: Block): bool =
    // TODO: this can have better performance if we can make assumptions about slots
    all_blocks.fold(Set(b.hash), (s, x) =>
      all_blocks.fold(s, (s, x) =>
        if (s.exists(hash => x.parent == hash))
          s.union(Set(x.parent))
        else
          s
      )
    ).contains(a.hash)

  type Environment = {
    system: ProcessID -> LocalState,
    now: Slot, // we can push to different views of slots later
    msgBuffer: Set[NetWorkMsg],
    activeTimeouts: ProcessID -> Set[TimeoutEventData],
  }

  /// Interface consensus algorithm / state machine: how consensus algorithm effects the environment
  pure def apply_effect (env: Environment, v: ProcessID, res: Result): Environment =
    val new = { ... env, system: env.system.set(v, res.post) } // update the state of the process
    res.output.fold(new, (s, o) =>
      match o {
        | Broadcast(msg) =>
          val nm = { sender: v, msg: msg }
          { ...s, msgBuffer: s.msgBuffer.union(Set(nm)) }
        | ScheduleEventTimeout(slot) =>
          { ...s, activeTimeouts: s.activeTimeouts.set(v, s.activeTimeouts.get(v).union(Set(slot))) }
      })


  // Defnition 13 (certificates)

  pure def fast_finalization_certified(slot: Slot, hash: Blockhash, msgs: Set[NetWorkMsg]): bool =
    msgs.filter(m => m.msg == NotarVoteMsg({ slot: slot, hash: hash }))
        .size() >= eighty

  pure def notarization_certified(slot: Slot, hash: Blockhash, msgs: Set[NetWorkMsg]): bool =
    msgs.filter(m => m.msg == NotarVoteMsg({ slot: slot, hash: hash }))
        .size() >= sixty

  pure def notar_fallback_certified(slot: Slot, hash: Blockhash, msgs: Set[NetWorkMsg]): bool =
    msgs.filter(m => m.msg == NotarVoteMsg({ slot: slot, hash: hash }) or
                     m.msg == NotarFallBackVoteMsg({ slot: slot, hash: hash }) )
          .size() >= sixty

  pure def skip_certified(slot: Slot, msgs: Set[NetWorkMsg]): bool =
    msgs.filter(m => m.msg == SkipVoteMsg(slot) or
                     m.msg == SkipFallbackVoteMsg(slot) )
        .size() >= sixty

  pure def finalization_certified(slot: Slot, msgs: Set[NetWorkMsg]): bool =
    msgs.filter(m => m.msg == FinalVoteMsg(slot))
        .size() >= sixty


  // Definition 14 (finalization)
  // Warning definitions uses "unique" perhaps unclear in case of more faults

  pure def finalized(slot: Slot, msgs: Set[NetWorkMsg]): Set[Blockhash] =
    NotarizedBlocks(msgs)
      .filter(t => t.slot == slot)
      .filter(t => finalization_certified(t.slot, msgs) and
                   notarization_certified(t.slot, t.hash, msgs))
      .map(t => t.hash)

  pure def fast_finalized(slot: Slot, msgs: Set[NetWorkMsg]): Set[Blockhash] =
    NotarizedBlocks(msgs)
      .filter(t => t.slot == slot)
      .filter(t => fast_finalization_certified(t.slot, t.hash, msgs))
      .map(t => t.hash)

  //
  //
  // State Machine
  //
  //

  var s: Environment

  val all_messages = s.msgBuffer.union(byz_network_msgs)

  action init = all {
    s' = {
      system: correct.mapBy(_ => initial_local_state),
      now: 0,
      msgBuffer: Set(),
      activeTimeouts: correct.mapBy(v => Set()),
    }
  }

  /// Emit Block and process it
  action receive_block(v: ProcessID, now: Slot): bool = all{
    nondet block = all_blocks.filter(b => b.slot == now).oneOf()
    v.process_input(BlockCI(block))
  }

  /// Fire timeout for current slot (TODO: check if timeout can only fire for current slot)
  action fire_timeout_event(v: ProcessID, now: Slot): bool = all {
    s.activeTimeouts.get(v).contains(now),
    val s2 = { ...s, activeTimeouts: s.activeTimeouts.set(v, s.activeTimeouts.get(v).exclude(Set(now))) }
    s' = apply_effect(s2, v, consensus(s2.system.get(v), TimeOutCI(now)))
  }

  pure def NotarizedBlocks(msgs: Set[NetWorkMsg]): Set[{ slot: Slot, hash: Blockhash }] =
    msgs.fold(Set(), (s, x) => match x.msg {
                            | NotarVoteMsg(m) => s.union(Set(m))
                            | _ => s
                          })
                .filter(t => notarization_certified(t.slot, t.hash, msgs))

  pure def NotarFallBackBlocks(msgs: Set[NetWorkMsg]): Set[{ slot: Slot, hash: Blockhash }] =
    msgs.fold(Set(), (s, x) => match x.msg {
                            | NotarVoteMsg(m) => s.union(Set(m))
                            | NotarFallBackVoteMsg(m) => s.union(Set(m))
                            | _ => s
                          })
                .filter(t => notar_fallback_certified(t.slot, t.hash, msgs))

  pure def slots_skip_certified(msgs: Set[NetWorkMsg]): Set[Slot] =
    msgs.fold(Set(), (s, x) => match x.msg {
                            | SkipVoteMsg(m) => s.union(Set(m))
                            | _ => s
                          })
                .filter(t => skip_certified(t, msgs))

  action process_input(id: ProcessID, input: ConsensusInput): bool = {
    s' = apply_effect(s, id, consensus(s.system.get(id), input))
  }

  // Definition 15 (Pool events). The following events are emitted as input for
  // Algorithm 1:

  // • BlockNotarized(slot(b), hash(b)): Pool holds a notarization certificate for
  // block b.
  def NotarizedBlocksCondition(v: ProcessID, now: Slot, b: { slot: Slot, hash: Blockhash }): bool =
    NotarizedBlocks(all_messages).contains(b)

  // Emit BlockNotarized and process it
  action BlockNotarizedAction(v: ProcessID, now: Slot): bool =
    val bs = all_blocks.filter(b => NotarizedBlocksCondition(v, now, { slot: b.slot, hash: b.hash }))
    all {
      bs.size() > 0,
      nondet b = bs.oneOf()
      v.process_input(BlockNotarizedCI({ slot: b.slot, hash: b.hash }))
    }

  // • ParentReady(s, hash(b)): Slot s is the first of its leader window, and Pool
  // holds a notarization or notar-fallback certificate for a previous block b,
  // and skip certificates for every slot s′ since b, i.e., for slot(b) < s′ < s.
  //
  // Warning "notarization or notar-fallback": notar-fallback seems to imply notar
  // Warning: Previous block? Block for previous slot
  pure def ParentReadyCondition(slot: Slot, hash: Blockhash, msgs: Set[NetWorkMsg]): bool = all {
    first_slot_in_leader_window(slot),
    val pool = NotarizedBlocks(msgs).filter(t => t.hash == hash and t.slot == slot)
    pool.exists(b =>
      and {
        b.slot < slot, // previous block
        or {
          notarization_certified(b.slot, b.hash, msgs),
          notar_fallback_certified(b.slot, b.hash, msgs)
        },
        b.slot.to(slot).subseteq(slots_skip_certified(msgs))
    })
  }

  /// Emit ParentReady and process it
  action ParentReadyAction(v: ProcessID, now: Slot): bool =
    val bs = all_blocks.filter(b => ParentReadyCondition(now, b.hash, all_messages))
    all {
      bs.size() > 0,
      nondet b = bs.oneOf()
      v.process_input(ParentReadyCI({slot: now, hash: b.hash}))
    }

  /// Definition 16 (fallback events)

  pure def voted_to_skip(s: Slot, msgs: Set[NetWorkMsg]): Set[ProcessID] =
    msgs.filter(m => match m.msg {
      | SkipVoteMsg(slot) => slot == s
      | _ => false
    }).map(m => m.sender)

  pure def voted_to_notar_pair(slot: Slot, hash: Blockhash, msgs: Set[NetWorkMsg]): Set[ProcessID] =
    msgs.filter(m => match m.msg {
      | NotarVoteMsg(x) => x.slot == slot and x.hash == hash
      | _ => false
    }).map(m => m.sender)

  // Warning: vote doesn't contain parent. Assumption about parent hashed in hash?
  pure def voted_to_notar(b: Block, msgs: Set[NetWorkMsg]): Set[ProcessID] =
    voted_to_notar_pair(b.slot, b.hash, msgs)

  // • SafeToNotar(s, hash(b)): The event is only issued if the node voted in
  // slot s already, but not to notarize b.
  def SafeToNotarCondition(v: ProcessID, now: Slot, b: Block): bool = all {
    val voted = all_messages.filter(m => m.sender == v and now == m.msg.slot_of())
    val notar_voted = voted.filter(m => match m.msg {
                          | NotarVoteMsg(m) => true
                          | _ => false
                })
    and {
      voted.size() > 0,
      notar_voted.size() == 0,
    },
    all_blocks.filter(b => b.slot == now).contains(b),
    val notar = voted_to_notar(b, all_messages).size()
    val skip = voted_to_skip(now, all_messages).size()
    // notar(b) ≥ 40% or (skip(s) + notar(b) ≥ 60% and notar(b) ≥ 20%).
    // Question: is (+) here the sum of the sizes or the size of the union?
    notar >= forty or (notar + skip >= sixty and notar >= twenty)
  }

  // Emit SafeToNotar and process it
  action SafeToNotarAction(v: ProcessID, now: Slot): bool =
    val bs = all_blocks.filter(b => SafeToNotarCondition(v, now, b))
    all {
      bs.size() > 0,
      nondet b = bs.oneOf()
      v.process_input(SafeToNotarCI({ slot: b.slot, hash: b.hash })),
    }

  // • SafeToSkip(s): The event is only issued if the node voted in slot s already,
  // but not to skip s.
  def SafeToSkipCondition(v: ProcessID, now: Slot): bool = all {
    all_messages.filter(m => m.sender == v and now == m.msg.slot_of())
                .filter(m => match m.msg {
                          | SkipVoteMsg(s) => false
                          | _ => true
                          })
                .size() > 0,
    val blocks_with_notar_votes =
      all_messages.filter(m => slot_of(m.msg) == now)
        .map(m => m.msg)
        .fold(Set(), (s, m) => match m {
          | NotarVoteMsg(n) => s.union(Set(n))
          | _ => s
        }
      )
    val max_notar = blocks_with_notar_votes.fold({slot: -1, hash: -1}, (res, x) =>
      if (voted_to_notar_pair(x.slot, x.hash, all_messages).size() > voted_to_notar_pair(res.slot, res.hash, all_messages).size())
        x
      else
        res)
    val sum_notar = blocks_with_notar_votes.map(m => m.hash).fold(Set(), (res, x) =>
      res.union(voted_to_notar_pair(now, x, all_messages)))
    voted_to_skip(now, all_messages).union(sum_notar).size() -
    voted_to_notar_pair(max_notar.slot, max_notar.hash, all_messages).size() >= forty
  }

  // Emit SafeToSkip and process it
  action SafeToSkipAction(v: ProcessID, now: Slot): bool = all {
    SafeToSkipCondition(v, now),
    v.process_input(SafeToSkipCI(now)),
  }

  action tick =
    s' = { ... s, now: s.now + 1 }

  action step =
    nondet v = oneOf(correct)
    any {
      receive_block(v, s.now),
      // TODO: fire_timeout_event(v),
      BlockNotarizedAction(v, s.now), // we pass the global time here, but we might also model that a validator is ahead / behind time
      ParentReadyAction(v, s.now),
      SafeToNotarAction(v, s.now),
      SafeToSkipAction(v, s.now),
     // tick, // increment the slot
    }

  //
  //
  // Invariants and Witnesses
  //
  //

  val agreement =
    0.to(s.now).forall(slot => finalized(slot, all_messages).size() <= 1)

  val fast_agreement =
    0.to(s.now).forall(slot => fast_finalized(slot, all_messages).union(finalized(slot, all_messages)).size() <= 1)

  // Witness was used to find bug in safeToNotar encoding
  val nobad =
    correct.forall(v =>
    not(s.system.get(v).state[1].contains(BadWindow)))

  /// Witness to find a run where a block is fast finalized
  val fast_finalized_witness =
    all_blocks.forall(b => not(fast_finalization_certified(b.slot, b.hash, all_messages)))

  val slots = 0.to(s.now)

  /// Theorem 1 (safety). If any correct node finalizes a block b in slot s and any
  /// correct node finalizes any block b′ in any slot s′ ≥ s, b′ is a descendant of b.
  val safety = tuples(slots, all_blocks).forall(((slot, block)) => {
    val finalized_at_slot = finalized(slot, all_messages)
    block.hash.in(finalized_at_slot) implies tuples(slot.to(s.now), all_blocks).forall(((slot2, block2)) => {
      block2.hash.in(finalized(slot2, all_messages)) implies block2.is_descendant(block)
    })
  })

  // TODO finalize ancestors
}

module example {
  import consensus(
    correct_blocks = Set( {slot: 0, hash: 42, parent: -1}, 
                  {slot: 1, hash: 43, parent: 42}, 
                  {slot: 2, hash: 44, parent: 43}, 
                  {slot: 3, hash: 45, parent: 44}),
    byz_blocks = Set(),
    alive_slots = 1.to(4),
    alive_hashes = 42.to(50),
    correct = Set("v1", "v2", "v3", "v4", "v5"),
    byzantine = Set(),
  ).* 
}


module byz {
  import consensus(
    correct_blocks = Set( {slot: 0, hash: 42, parent: -1}, 
                  // {slot: 1, hash: 43, parent: 42}, 
                  // {slot: 2, hash: 44, parent: 43}, 
                  // {slot: 3, hash: 45, parent: 44}
    ),
    correct = Set("v1", "v2", "v3", "v4"),
    byz_blocks = Set( 
                   {slot: 0, hash: 41, parent: -1},
    //               {slot: 1, hash: 48, parent: 42}, 
    //               {slot: 2, hash: 49, parent: 43}, 
    //               {slot: 3, hash: 50, parent: 44}
    ),
    alive_slots = Set(0), // 0.to(4),
    alive_hashes = 41.to(42),
    byzantine = Set("v5", "v6"),
  ).* 
}
