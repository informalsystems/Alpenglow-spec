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
  val all_blocks = correct_blocks.union(byz_blocks)

  /// Slots for which this model considers votes
  const alive_slots: Set[Slot]
  /// Hashes for which this model considers votes
  const alive_hashes: Set[Blockhash]

  // Assumption 1
  assume resilience_condition = correct.size() > byzantine.size() * 4 // N > 5F

  // Assumption 2 on additional crashes: TODO

  val twenty = correct.union(byzantine).size() * 20 / 100
  val forty = correct.union(byzantine).size() * 40 / 100
  val sixty = correct.union(byzantine).size() * 60 / 100
  val eighty = correct.union(byzantine).size() * 80 / 100

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

  type Environment = {
    system: ProcessID -> LocalState,
    now: Slot, // we can push to different views of slots later
    msgBuffer: Set[NetWorkMsg],
    activeTimeouts: ProcessID -> Set[TimeoutEventData],
  }

  var s: Environment

  pure def initial_global_state: Environment =
    { system: correct.mapBy(_ => initial_local_state),
      now: 0,
      msgBuffer: Set(),
      activeTimeouts: correct.mapBy(v => Set()),
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

  //
  // General state machine
  //

  // Certificates

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


  /// Definition 15
  /// Warning definitions uses "unique" perhaps unclear in case of more faults
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
  // Invariants and Witnesses
  //
  //

  def agreement =
    0.to(s.now).forall(slot => finalized(slot, s.msgBuffer).size() <= 1)

  def fast_agreement =
    0.to(s.now).forall(slot => fast_finalized(slot, s.msgBuffer).union(finalized(slot, s.msgBuffer)).size() <= 1)

  // Witness was used to find bug in safeToNotar encoding
  def nobad =
    correct.forall(v =>
    not(s.system.get(v).state[1].contains(BadWindow)))

  def never_fast_finalized =
    all_blocks.forall(b => not(fast_finalization_certified(b.slot, b.hash, s.msgBuffer)))

  // TODO finalize ancestors

  action init = all {
    s' = initial_global_state
  }

  action receive_block(v: ProcessID, now: Slot): bool = all{
    nondet block = all_blocks.filter(b => b.slot == now).oneOf()
    val result = consensus(s.system.get(v), BlockCI(block))
    s' = apply_effect(s, v, result)
  }

  action fire_timeout_event(v: ProcessID, now: Slot): bool = all{
      s.activeTimeouts.get(v) != Set(),
      nondet timeout = oneOf(s.activeTimeouts.get(v).filter(t => t == now))
      val s2 = { ... s, activeTimeouts: s.activeTimeouts.set(v, s.activeTimeouts.get(v).exclude(Set(timeout))) }
      val result = consensus(s2.system.get(v), TimeOutCI(timeout))
      s' = apply_effect(s2, v, result)
  }

  pure def NotarizedBlocks(msgs: Set[NetWorkMsg]): Set[{slot: Slot, hash: Blockhash}]=
    msgs.fold(Set(), (s, x) => match x.msg {
                            | NotarVoteMsg(m) => s.union(Set(m))
                            | _ => s
                          })
                .filter(t => notarization_certified(t.slot, t.hash, msgs))

  pure def NotarFallBackBlocks(msgs: Set[NetWorkMsg]): Set[{slot: Slot, hash: Blockhash}]=
    msgs.fold(Set(), (s, x) => match x.msg {
                            | NotarVoteMsg(m) => s.union(Set(m))
                            | NotarFallBackVoteMsg(m) => s.union(Set(m))
                            | _ => s
                          })
                .filter(t => notar_fallback_certified(t.slot, t.hash, msgs))

  pure def SlotSkipCertified(msgs: Set[NetWorkMsg]): Set[Slot]=
    msgs.fold(Set(), (s, x) => match x.msg {
                            | SkipVoteMsg(m) => s.union(Set(m))
                            | _ => s
                          })
                .filter(t => skip_certified(t, msgs))



  def NotarizedBlocksCondition(v: ProcessID, now: Slot, b: {slot: Slot, hash: Blockhash}): bool =
    NotarizedBlocks(s.msgBuffer).contains(b)

  // BlockNotarized
  action BlockNotarizedAction(v: ProcessID, now: Slot): bool =
    val bs = all_blocks.filter(b => NotarizedBlocksCondition(v, now, { slot: b.slot, hash: b.hash }))
    all {
      bs.size() > 0,
      nondet b = bs.oneOf()
      s' = apply_effect(s, v, consensus(s.system.get(v), BlockNotarizedCI({slot: b.slot, hash: b.hash})))
    }


  /// Definition 16
  // Warning "notarization or notar-fallback": notar-fallback seems to imply notar
  // Warning: Previous block? Block for previous slot
  pure def ParentReadyCondition (slot: Slot, hash: Blockhash, msgs: Set[NetWorkMsg]): bool = all {
    first_slot_in_leader_window(slot),
    val pool = NotarizedBlocks(msgs).filter(t => t.hash == hash and t.slot == slot)
    pool.exists(b =>
      and {
        b.slot < slot, // previous block
        or {
          notarization_certified(b.slot, b.hash, msgs),
          notar_fallback_certified(b.slot, b.hash, msgs)
        },
        b.slot.to(slot).subseteq(SlotSkipCertified(msgs))
    })
  }

  // ParentReady
  action ParentReadyAction(v: ProcessID, now: Slot): bool =
    val bs = all_blocks.filter(b => ParentReadyCondition(now, b.hash, s.msgBuffer))
    all {
      bs.size() > 0,
      nondet b = bs.oneOf()
      s' = apply_effect(s, v, consensus(s.system.get(v), ParentReadyCI({slot: now, hash: b.hash})))
    }


  pure def voted_to_skip (s: Slot, msgs: Set[NetWorkMsg]): Set[ProcessID] =
    msgs.filter(m => match m.msg {
      | SkipVoteMsg(slot) => slot == s
      | _ => false}).map(m => m.sender)

  pure def voted_to_notar_pair (slot: Slot, hash: Blockhash, msgs: Set[NetWorkMsg]): Set[ProcessID] =
    msgs.filter(m => match m.msg {
      | NotarVoteMsg(x) => x.slot == slot and x.hash == hash
      | _ => false}).map(m => m.sender)

  // Warning: vote doesn't contain parent. Assumption about parent hashed in hash?
  pure def voted_to_notar (b: Block, msgs: Set[NetWorkMsg]): Set[ProcessID] =
    voted_to_notar_pair(b.slot, b.hash, msgs)



  def SafeToNotarCondition(v: ProcessID, now: Slot, b: Block): bool = all {
    // Definition 17: The event is only issued if the node voted in slot s already, but not to notarize b.
    val voted = s.msgBuffer.filter(m => m.sender == v and now == m.msg.slot_of())
    val notar_voted = voted.filter(m => match m.msg {
                          | NotarVoteMsg(m) => true
                          | _ => false
                })
    all {
      voted.size() > 0,
      notar_voted.size() == 0,
    },
    all_blocks.filter(b => b.slot == now).contains(b),
    all {
      or {
        voted_to_notar(b, s.msgBuffer).size() >= forty,
        and {
          voted_to_skip(now, s.msgBuffer).union(voted_to_notar(b, s.msgBuffer)).size() >= sixty,
          voted_to_notar(b, s.msgBuffer).size() >= twenty,
        }
      }
    }
  }

  // SafeToNotar
  action SafeToNotarAction(v: ProcessID, now: Slot): bool =
    val bs = all_blocks.filter(b => SafeToNotarCondition(v, now, b))
    all {
      bs.size() > 0,
      nondet b = bs.oneOf()
      s' = apply_effect(s, v, consensus(s.system.get(v), SafeToNotarCI({slot: b.slot, hash: b.hash})))
    }


  def SafeToSkipCondition(v: ProcessID, now: Slot): bool = all {
      // Definition 17: The event is only issued if the node voted in slot s already, but not to skip b.
    s.msgBuffer .filter(m => m.sender == v and now == m.msg.slot_of())
                .filter(m => match m.msg {
                          | SkipVoteMsg(s) => false
                          | _ => true
                          })
                .size() > 0,
    val blocks_with_notar_votes =
      s.msgBuffer.filter(m => slot_of(m.msg) == now)
        .map(m => m.msg)
        .fold(Set(), (s, m) => match m {
          | NotarVoteMsg(n) => s.union(Set(n))
          | _ => s
        }
      )
    val max_notar = blocks_with_notar_votes.fold({slot: -1, hash: -1}, (res, x) =>
      if (voted_to_notar_pair(x.slot, x.hash, s.msgBuffer).size() > voted_to_notar_pair(res.slot, res.hash, s.msgBuffer).size())
        x
      else
        res)
    val sum_notar = blocks_with_notar_votes.map(m => m.hash).fold(Set(), (res, x) =>
      res.union(voted_to_notar_pair(now, x, s.msgBuffer)))
    voted_to_skip(now, s.msgBuffer).union(sum_notar).size() -
    voted_to_notar_pair(max_notar.slot, max_notar.hash, s.msgBuffer).size() >= forty
  }

  // SafetToSkip
  action SafeToSkipAction(v: ProcessID, now: Slot): bool = all {
    SafeToSkipCondition(v, now),
    s' = apply_effect(s, v, consensus(s.system.get(v), SafeToSkipCI(now))),
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


module parent_not_proposed {
  import consensus(
    correct_blocks = Set( {slot: 0, hash: 42, parent: -1}, 
                  {slot: 1, hash: 43, parent: 42}, 
                  {slot: 2, hash: 44, parent: 43}, 
                  {slot: 3, hash: 45, parent: 44}),
    correct = Set("v1", "v2", "v3", "v4"),
    byz_blocks = Set( 
                  {slot: 1, hash: 48, parent: 42}, 
                  {slot: 2, hash: 49, parent: 43}, 
                  {slot: 3, hash: 50, parent: 44}),
    alive_slots = 1.to(4),
    alive_hashes = 42.to(50),
    byzantine = Set("v5", "v6"),
  ).* 
}
