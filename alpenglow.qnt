// -*- mode: Bluespec; -*-
/**
 * Specification of Alpenglow Consensus [1]
 *
 * [1]: https://drive.google.com/file/d/1y_7ddr8oNOknTQYHzXeeMD2ProQ0WjMs/view
 *
 * Josef Widder,
 * Informal Systems, 2025
 */

module alpenglow {
  import basicSpells.* from "./basicSpells"

  type Slot = int

  type Block = {
    slot: Slot,
    hash: Blockhash,
    parent: Blockhash,
  }

  type Blockhash = int

  /// Fields are lists indexed by slot
  type LocalState = {
    pendingBlocks: List[Option[Block]],
    state: List[Set[SlotObject]],
  }

  /// Definition 18 (Votor State)
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

  /// Table 4 (Alpenglow’s voting messages)
  type Message =
    | NotarVoteMsg({slot: Slot, hash: Blockhash})
    | NotarFallBackVoteMsg({slot: Slot, hash: Blockhash})
    | SkipVoteMsg(Slot)
    | SkipFallbackVoteMsg(Slot)
    | FinalVoteMsg(Slot)

  pure def slotOf(msg: Message): Slot =
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

  pure def addObjects(ls: LocalState, slot: Slot, obj: Set[SlotObject]): LocalState =
    { ...ls, state: ls.state.replaceAt(slot, ls.state[slot].union(obj)) }

  pure def setPendingBlock(ls: LocalState, slot: Slot, b: Option[Block]): LocalState =
    { ...ls, pendingBlocks: ls.pendingBlocks.replaceAt(slot, b) }

  /// line 10 of TryNotar. TODO: Is there more to it?
  pure def firstSlotInLeaderWindow(slot: Slot): bool =
    slot % 4 == 0 // TODO implement

  // Algorithm 2

  pure def windowSlots(slot: Slot): Set[Slot] =
    // TODO: Not sure this makes any sense
    if (slot % 4 == 0)
      Set(slot, slot + 1, slot + 2, slot + 3)
    else if (slot % 4 == 1)
      Set(slot - 1, slot, slot + 1, slot + 2)
    else if (slot % 4 == 2)
      Set(slot - 2, slot - 1, slot, slot + 1)
    else
      Set(slot - 3, slot - 2, slot - 1, slot)

  pure def setTimeouts(ls: LocalState, slot: Slot): Result =
    { post: ls,
      output: windowSlots(slot).map(i => (ScheduleEventTimeout(i))) }

  /// Check if a notarization vote can be cast
  pure def tryNotar(ls: LocalState, b: Block): { result: Result, success: bool } =
    if (ls.state[b.slot].contains(Voted))
      { result: { post: ls, output: Set() }, success: false }
    else
      val firstSlot = firstSlotInLeaderWindow(b.slot)
      if ((firstSlot and ParentReady(b.parent).in(ls.state[b.slot]))
        or (not(firstSlot) and VotedNotar(b.parent).in(ls.state[b.slot - 1])))
        // Warning: parentheses not matching in paper

        // Notarization vote
        val out = Set(Broadcast(NotarVoteMsg({ slot:b.slot, hash: b.hash })))
        val s2 =  ls
          .addObjects(b.slot, Set(Voted, VotedNotar(b.hash)))
          // Won't vote notar a second time
          .setPendingBlock(b.slot, None)

        // Maybe vote finalize as well
        val tf = tryFinal(s2, b.slot, b.hash)

        { result: { post: tf.post, output: out.union(tf.output) }, success: true }
      else
        { result: { post: ls, output: Set() }, success: false }

  pure def tryFinal(ls: LocalState, slot: Slot, hash: Blockhash): Result =
    if (BlockNotarized(hash).in(ls.state[slot]) and VotedNotar(hash).in(ls.state[slot])
        and not(BadWindow.in(ls.state[slot])))
      // Finalization vote
      { output: Set(Broadcast(FinalVoteMsg(slot))), post: ls.addObjects(slot, Set(ItsOver)) }
    else
      { output: Set(), post: ls }

  pure def trySkipWindow(ls: LocalState, slot: Slot): Result =
    // Skip unvoted slots
    windowSlots(slot).fold({ output: Set(), post: ls }, (s, k) => {
      if (not(Voted.in(s.post.state[k])))
        // Skip vote
        val update = Set(Broadcast(SkipVoteMsg(k)))
        val s2 = s.post
          .addObjects(k, Set(Voted, BadWindow))
          // Won't vote notar after skip
          .setPendingBlock(k, None)

        { output: s.output.union(update), post: s2 }
      else
        s
    })

  pure def checkPendingBlocks(ls: LocalState): Result =
    // Iterate with increasing slot
    // (left to right)
    ls.pendingBlocks.foldl({ output: Set(), post: ls }, (res, pendingBlock) =>
      match pendingBlock {
        | Some(b) =>
          val tn = tryNotar(res.post, b)
          { output: res.output.union(tn.result.output), post: tn.result.post } // TODO implement
        | None =>
          res
      }
    )


  /// Algorithm 1: each upon corresponds to one consensus input
  // Warning: Block vs. Blockevent a bit unclear
  pure def consensus(ls: LocalState, ci: ConsensusInput): Result =
    match ci {
      | BlockCI(b) =>
        val tn = tryNotar(ls, b) // looks like a function but has two side effects: changes state and broadcasts
        if (tn.success)
          val cpb = checkPendingBlocks(tn.result.post)
          // as tryNotar changed the local state, we pass it to checkPendingBlocks
          { post: cpb.post, output: cpb.output.union(tn.result.output) }
          // both, tryNotar and checkPendingBlocks have side effects of sending messages. Thus we build the union here.
        else if (not(Voted.in(tn.result.post.state[b.slot])))
            val s = tn.result.post.setPendingBlock(b.slot, Some(b))
            { output: tn.result.output, post: s }
        else
          // Even if all if conditions evaluate to false, tryNotar may have side effects and may change the local state
          { output: tn.result.output, post: tn.result.post } // Warning: The state might have changed

      | TimeOutCI(slot) =>
        if (Voted.in(ls.state[slot]))
          trySkipWindow(ls, slot)
        else
          // No change state, no messages sent
          { output: Set(), post: ls }

      | BlockNotarizedCI(sh) =>
        val s = ls.addObjects(sh.slot, Set(BlockNotarized(sh.hash)))
        tryFinal(s, sh.slot, sh.hash)

      | ParentReadyCI(sh) =>
        val s = ls.addObjects(sh.slot, Set(ParentReady(sh.hash)))
        val s1 = checkPendingBlocks(s)
        // Start time for all slots in this window
        val s2 = setTimeouts(s1.post, sh.slot)
        { output: s1.output.union(s2.output), post: s2.post }

      | SafeToNotarCI(sh) =>
        val s = trySkipWindow(ls, sh.slot)
        if (not(ItsOver.in(s.post.state[sh.slot])))
          // Notar-fallback vote
          val output = s.output.union(Set(Broadcast(NotarFallBackVoteMsg(sh))))
          { output: output, post: s.post.addObjects(sh.slot, Set(BadWindow)) }
        else
          s

      | SafeToSkipCI(slot) =>
        val s = trySkipWindow(ls, slot)
        if (not(ItsOver.in(s.post.state[slot])))
          // Skip-fallback vote
          val output = s.output.union(Set(Broadcast(SkipFallbackVoteMsg(slot))))
          { output: output, post: addObjects(s.post, slot, Set(BadWindow)) }
        else
          s
    }
}
