// -*- mode: Bluespec; -*-

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

  pure def final_messages(msgs: Set[Message]): Set[Message] =
    msgs.fold(Set(), (s, x) => match x {
                            | FinalVoteMsg(m) => s.union(Set(x))
                            // | NotarFallBackVoteMsg(m) => s.union(Set(m))
                            | _ => s
                          })

  pure def notar_fallback_messages(msgs: Set[Message]): Set[Message] =
    msgs.fold(Set(), (s, x) => match x {
                            | NotarFallBackVoteMsg(m) => s.union(Set(x))
                            // | NotarFallBackVoteMsg(m) => s.union(Set(m))
                            | _ => s
                          })

  pure def skip_fallback_messages(msgs: Set[Message]): Set[Message] =
    msgs.fold(Set(), (s, x) => match x {
                            | SkipFallbackVoteMsg(m) => s.union(Set(x))
                            // | NotarFallBackVoteMsg(m) => s.union(Set(m))
                            | _ => s
                          })

  def lemma20 = 
    benevolent.forall(p =>
      slots.forall(slot =>
        val sent_in_slot = s.msgBuffer.filter(m => m.sender == p and m.msg.slotOf() == slot).map(m => m.msg)
        sent_in_slot.skip_messages().size() + sent_in_slot.notar_messages().size() <= 1
      )
    )

  def lemma21 =
    allBlocks.forall(b =>
      slots.forall(slot =>
        isCertified(FastFinalizationCertificate({ slot: slot, hash: b.hash }), allMessages) implies
        all {
          allBlocks.exclude(Set(b)).forall(b2 =>
            not (isCertified(NotarizationCertificate({ slot: slot, hash: b2.hash }), allMessages))),
          allBlocks.exclude(Set(b)).forall(b2 =>
            not (isCertified(NotarFallbackCertificate({ slot: slot, hash: b2.hash }), allMessages))),
          not (isCertified(SkipCertificate(slot), allMessages)),
        }
      )
    )

  def lemma22 = 
    benevolent.forall(p => 
      slots.forall(slot => 
      val sent_in_slot = s.msgBuffer.filter(m => m.sender == p and m.msg.slotOf() == slot).map(m => m.msg)
        sent_in_slot.final_messages().size() > 0 implies and {
          sent_in_slot.notar_fallback_messages().size() == 0,
          sent_in_slot.skip_fallback_messages().size() == 0
        }
      ))
      


}
