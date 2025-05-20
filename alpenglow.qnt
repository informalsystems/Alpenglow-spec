// -*- mode: Bluespec; -*-

module anden {

c


  type Slot = int

  type Block = {
    slot: Slot, 
    hash: Blockhash, 
    parent: Blockhash,
  }

  type Blockhash = int

  type SlotState = {
    pendingBlock: Option[Block],
    state: Set[SlotObject],
  }

  pure val empty_slot_state =
    { pendingBlock: None, state: Set() }

  /// Definition 20 (Votor State)
  type SlotObject =
    | ParentReady(Blockhash)
    | Voted
    | VotedNotar(Blockhash)
    | BlockNotarized(Blockhash)
    | ItsOver
    | BadWindow

  type ConsensusInput = 
    | BlockCI(Block)
    | TimeOutCI(Slot)
    | BlockNotarizedCI({slot: Slot, hash: Blockhash})
    | ParentReadyCI({slot: Slot, hash: Blockhash})
    | SafeToNotarCI({slot: Slot, hash: Blockhash})
    | SafeToSkipCI(Slot)

// Consensus State Machine Interface (CSMI) definitions

  type LocalState = Slot -> SlotState

  /// Table 3
  type Message =
    | NotarVoteMsg({slot: Slot, hash: Blockhash})
    | NotarFallBackVoteMsg({slot: Slot, hash: Blockhash})
    | SkipVoteMsg(Slot)
    | SkipFallbackVoteMsg(Slot)
    | FinalVoteMsg(Slot)

  pure def slot_of(msg: Message): Slot =
    match msg {
      | NotarVoteMsg(m) => m.slot
      | NotarFallBackVoteMsg(m) => m.slot
      | SkipVoteMsg(slot) => slot
      | SkipFallbackVoteMsg(slot) => slot
      | FinalVoteMsg(slot) => slot
    }

  type TimeoutEventData = Slot // TODO not sure what timeouts they start

  type ConsensusOutput =
    | ScheduleEventTimeout(TimeoutEventData) // might be multiple from one function call
    | Broadcast(Message)

  type Bookkeeping

  type Result = {
    output: Set[ConsensusOutput],
    post: LocalState,
  }


  // Auxiliary functions

  pure def add_objects(ls: LocalState, slot: Slot, obj: Set[SlotObject]): LocalState =
    ls.put(slot, { ... ls.get(slot), state: ls.get(slot).state.union(obj) })

  pure def set_pending_block(ls: LocalState, slot: Slot, b: Option[Block]): LocalState =
    ls.put(slot, { ... ls.get(slot), pendingBlock: b })

  /// line 10 of TryNotar. TODO: Is there more to it?
  pure def first_slot_in_leader_window(slot: Slot): bool =
    slot % 4 == 0 // TODO implement

  // Algorithm 2

  pure def WindowSlots(slot: Slot): Set[Slot] =
    // TODO: Not sure this makes any sense
    if (slot % 4 == 0)
      Set(slot, slot + 1, slot + 2, slot + 3)
    else if (slot % 4 == 1)
      Set(slot - 1, slot, slot + 1, slot + 2)
    else if (slot % 4 == 2)
      Set(slot - 2, slot - 1, slot, slot + 1)
    else
      Set(slot - 3, slot - 2, slot - 1, slot)

  pure def SetTimeouts(ls: LocalState, slot: Slot): Result =
    { post: ls,
      output: WindowSlots(slot).map(i => (ScheduleEventTimeout(i))) } 

  pure def TryNotar(ls: LocalState, b: Block): { result: Result, success: bool } =
    if (ls.get(b.slot).state.contains(Voted))
      { result: { post: ls, output: Set() }, success: false }
    else 
      val firstSlot = first_slot_in_leader_window(b.slot) 
      if (any { // Warning: parentheses not matching in paper
        firstSlot and ls.get(b.slot).state.contains(ParentReady(b.parent)),
        not(firstSlot) and ls.get(b.slot - 1).state.contains(VotedNotar(b.parent))})
        val out = Set(Broadcast(NotarVoteMsg({slot:b.slot, hash: b.hash})))
        val s2 = ls.put(b.slot, {  state: ls.get(b.slot).state.union(Set(Voted, VotedNotar(b.hash))) ,
                                   pendingBlock: None })
        val tf = TryFinal(s2, b.slot, b.hash)
        { result: { post: tf.post, output: out.union(tf.output) }, success: true }
      else
        { result: { post: ls, output: Set() }, success: false }

  pure def TryFinal(ls: LocalState, slot: Slot, hash: Blockhash): Result =
    if (and{
      ls.get(slot).state.contains(BlockNotarized(hash)),
      ls.get(slot).state.contains(VotedNotar(hash)),
      not(ls.get(slot).state.contains(BadWindow)),
    })
      { output: Set(Broadcast(FinalVoteMsg(slot))), 
        post: add_objects(ls, slot, Set(ItsOver)) }
    else
      { output: Set(), post: ls } 




  pure def TrySkipWindow(ls: LocalState, slot: Slot): Result =
    WindowSlots(slot).fold({ output: Set(), post: ls } , (s, k) =>
      if (not(s.post.get(k).state.contains(Voted)))
        val update = Set(Broadcast(SkipVoteMsg(k)))
        val s2 = s.post.add_objects(k, Set(Voted, BadWindow))
                        .set_pending_block(k, None)
        { output: update, post: s2 }
      else
        s
    )
    
  pure def CheckPendingBlocks(ls: LocalState): Result =
    ls.values().fold({ output: Set(), post: ls }, (res, s) =>
      match s.pendingBlock {
        | Some(b) =>
          val tn = TryNotar(res.post, b)
          { output: res.output.union(tn.result.output), post: tn.result.post } // TODO implement
        | None =>
          res
      }
    )


// Algorithm 1

// Warning: Block vs. Blockevent a bit unclear
  pure def consensus(ls: LocalState, ci: ConsensusInput): Result =
    match ci {
      | BlockCI(b) =>
        val tn = TryNotar(ls, b) // looks like a function but has two side effects: changes state and broadcasts
        if (tn.success)
          val cpb = CheckPendingBlocks(tn.result.post)
          { post: cpb.post, output: cpb.output.union(tn.result.output) }
        else if (not(tn.result.post.get(b.slot).state.contains(Voted)))
            val s = tn.result.post.put(b.slot, { ... tn.result.post.get(b.slot), pendingBlock: Some(b) })
            { output: tn.result.output, post: s }
        else
          { output: tn.result.output, post: tn.result.post } // Warning: The state might have changed

      | TimeOutCI(slot) =>
        if (ls.get(slot).state.contains(Voted))
          TrySkipWindow(ls, slot)
        else
          { output: Set(), post: ls }

      | BlockNotarizedCI(sh) =>
        val s = add_objects(ls, sh.slot, Set(BlockNotarized(sh.hash)))
        TryFinal(s, sh.slot, sh.hash)

      | ParentReadyCI(sh) =>
        val s = add_objects(ls, sh.slot, Set(ParentReady(sh.hash)))
        val s1 = CheckPendingBlocks(s)
        val s2 = SetTimeouts(s1.post, sh.slot)
        { output: s1.output.union(s2.output), post: s2.post }

      | SafeToNotarCI(sh) =>
        val s = TrySkipWindow(ls, sh.slot)
        if (not(s.post.get(sh.slot).state.contains(ItsOver)))
          val output = s.output.union(Set(Broadcast(NotarFallBackVoteMsg(sh))))
          { output: output, post: add_objects(s.post, sh.slot, Set(BadWindow)) }
        else
          s

      | SafeToSkipCI(slot) =>
        val s = TrySkipWindow(ls, slot)
        if (not(s.post.get(slot).state.contains(ItsOver)))
          val output = s.output.union(Set(Broadcast(SkipVoteMsg(slot))))
          { output: output, post: add_objects(s.post, slot, Set(BadWindow)) }
        else
          s
    }



}
