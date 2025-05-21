module lemmas {

  import basicSpells.* from "./basicSpells"
  import alpenglow.* from "./alpenglow"
  import consensus.* from "./statemachine"


  pure def skip_messages(msgs: Set[Message]): Set[Message] =
    msgs.fold(Set(), (s, x) => match x {
                            | SkipVoteMsg(m) => s.union(Set(x))
                            // | SkipFallbackVoteMsg(m) => s.union(Set(m))
                            | _ => s
                          })

  pure def notar_messages(msgs: Set[Message]): Set[Message] =
    msgs.fold(Set(), (s, x) => match x {
                            | NotarVoteMsg(m) => s.union(Set(x))
                            // | NotarFallBackVoteMsg(m) => s.union(Set(m))
                            | _ => s
                          })



  def lemma20 = 
    benevolent.forall(p =>
      slots.forall(slot =>
        val sent_in_slot = s.msgBuffer.filter(m => m.sender == p and m.msg.slot_of() == slot).map(m => m.msg)
        sent_in_slot.skip_messages().size() + sent_in_slot.notar_messages().size() <= 1
    ))

  def lemma21 =
    all_blocks.forall(b =>
      slots.forall(slot =>
        fast_finalization_certified(slot, b.hash, all_messages) implies
        all {
          all_blocks.exclude(Set(b)).forall(b2 =>
            not (notarization_certified(slot, b2.hash, all_messages))),
          all_blocks.exclude(Set(b)).forall(b2 =>
            not (notar_fallback_certified(slot, b2.hash, all_messages))),     
          not (skip_certified(slot, all_messages)),       
        }
      
      ))

}