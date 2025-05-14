// -*- mode: Bluespec; -*-

module anden {


  import basicSpells.* from "./basicSpells"


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

  type TimeoutEventData = Slot // TODO not sure what timeouts they start

  type ConsensusOutput =
    | ScheduleEventTimeout(TimeoutEventData) // might be multiple from one function call
    | Broadcast(Message)

  type Bookkeeping

  type Result = {
    output: Set[ConsensusOutput],
    res_ls: LocalState,
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
    { res_ls: ls,
      output: WindowSlots(slot).map(i => (ScheduleEventTimeout(i))) } 

  pure def TryNotar(ls: LocalState, b: Block): { result: Result, success: bool } =
    if (ls.get(b.slot).state.contains(Voted))
      { result: { res_ls: ls, output: Set() }, success: false }
    else 
      val firstSlot = first_slot_in_leader_window(b.slot) 
      if (any { // Warning: parentheses not matching in paper
        firstSlot and ls.get(b.slot).state.contains(ParentReady(b.parent)),
        not(firstSlot) and ls.get(b.slot - 1).state.contains(VotedNotar(b.parent))})
        val out = Set(Broadcast(NotarVoteMsg({slot:b.slot, hash: b.hash})))
        val s2 = ls.put(b.slot, {  state: ls.get(b.slot).state.union(Set(Voted, VotedNotar(b.hash))) ,
                                   pendingBlock: None })
        val tf = TryFinal(s2, b.slot, b.hash)
        { result: { res_ls: tf.res_ls, output: out.union(tf.output) }, success: true }
      else
        { result: { res_ls: ls, output: Set() }, success: false }

  pure def TryFinal(ls: LocalState, slot: Slot, hash: Blockhash): Result =
    if (and{
      ls.get(slot).state.contains(BlockNotarized(hash)),
      ls.get(slot).state.contains(VotedNotar(hash)),
      not(ls.get(slot).state.contains(BadWindow)),
    })
      { output: Set(Broadcast(FinalVoteMsg(slot))), 
        res_ls: add_objects(ls, slot, Set(ItsOver)) }
    else
      { output: Set(), res_ls: ls } 




  pure def TrySkipWindow(ls: LocalState, slot: Slot): Result =
    WindowSlots(slot).fold({ output: Set(), res_ls: ls } , (s, k) =>
      if (not(s.res_ls.get(k).state.contains(Voted)))
        val update = Set(Broadcast(SkipVoteMsg(k)))
        val s2 = s.res_ls.add_objects(k, Set(Voted, BadWindow))
                        .set_pending_block(k, None)
        { output: update, res_ls: s2 }
      else
        s
    )
    
  pure def CheckPendingBlocks(ls: LocalState): Result =
    ls.values().fold({ output: Set(), res_ls: ls }, (res, s) =>
      match s.pendingBlock {
        | Some(b) =>
          val tn = TryNotar(res.res_ls, b)
          { output: res.output.union(tn.result.output), res_ls: tn.result.res_ls } // TODO implement
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
          val cpb = CheckPendingBlocks(tn.result.res_ls)
          { res_ls: cpb.res_ls, output: cpb.output.union(tn.result.output) }
        else if (not(tn.result.res_ls.get(b.slot).state.contains(Voted)))
            val s = tn.result.res_ls.put(b.slot, { ... tn.result.res_ls.get(b.slot), pendingBlock: Some(b) })
            { output: tn.result.output, res_ls: s }
        else
          { output: tn.result.output, res_ls: tn.result.res_ls } // Warning: The state might have changed

      | TimeOutCI(slot) =>
        if (ls.get(slot).state.contains(Voted))
          TrySkipWindow(ls, slot)
        else
          { output: Set(), res_ls: ls }

      | BlockNotarizedCI(sh) =>
        val s = add_objects(ls, sh.slot, Set(BlockNotarized(sh.hash)))
        TryFinal(s, sh.slot, sh.hash)

      | ParentReadyCI(sh) =>
        val s = add_objects(ls, sh.slot, Set(ParentReady(sh.hash)))
        val s1 = CheckPendingBlocks(s)
        val s2 = SetTimeouts(s1.res_ls, sh.slot)
        { output: s1.output.union(s2.output), res_ls: s2.res_ls }

      | SafeToNotarCI(sh) =>
        val s = TrySkipWindow(ls, sh.slot)
        if (not(s.res_ls.get(sh.slot).state.contains(ItsOver)))
          val output = s.output.union(Set(Broadcast(NotarFallBackVoteMsg(sh))))
          { output: output, res_ls: add_objects(s.res_ls, sh.slot, Set(BadWindow)) }
        else
          s

      | SafeToSkipCI(slot) =>
        val s = TrySkipWindow(ls, slot)
        if (not(s.res_ls.get(slot).state.contains(ItsOver)))
          val output = s.output.union(Set(Broadcast(SkipVoteMsg(slot))))
          { output: output, res_ls: add_objects(s.res_ls, slot, Set(BadWindow)) }
        else
          s
    }



}
