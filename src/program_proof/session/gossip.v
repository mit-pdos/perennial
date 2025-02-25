From Perennial.program_proof.session Require Export session_prelude coq_session.
From Perennial.program_proof.session Require Export versionVector sort.


Section heap.

  Context `{hG: !heapGS Σ}.

  Lemma wp_acknowledgeGossip (sv: u64*u64*Slice.t*Slice.t*Slice.t*Slice.t*Slice.t*Slice.t) (s: Server.t) (msgv: u64*u64*u64*u64*u64*Slice.t*u64*u64*Slice.t*u64*u64*u64*u64*u64*u64*Slice.t*u64*u64) (msg: Message.t) (n: nat) :
    {{{
          is_server sv s n ∗ 
          is_message msgv msg n
    }}}
      acknowledgeGossip (server_val sv) (message_val msgv)
      {{{
            r , RET r;
            is_server sv (coq_acknowledgeGossip s msg) n ∗
            is_message msgv msg n
      }}}.
  Proof.
    iIntros "%Φ (H1 & H2) H_ret".
    rewrite /acknowledgeGossip.
    iDestruct "H1" as "(%H1 & %H2 & H1 & %H3 & H4 & H5 & H6 & H7 & %H4 & H8)".
    iDestruct "H2" as "(%H5 & %H6 & %H7 & %H8 & %H9 & %H10 & H9 & %H11 & %H12 & H10 & %H13 & %H14 & %H15 & %H16 & %H17 & %H18 & %H19 & H11 & %H20 & %H21)".
    wp_pures.
    wp_apply (wp_slice_len).
    wp_if_destruct.
    { iModIntro. iApply "H_ret". iFrame. admit. }
    iDestruct (own_slice_small_sz with "H8") as "%H22". 
    assert (uint.nat msgv.1.1.1.1.1.1.1.2 < length s.(Server.GossipAcknowledgements))%nat
      by word.
    apply list_lookup_lt in H as [x H].
    wp_apply (wp_SliceGet with "[H8]"). { iFrame. auto. }
    iIntros "H8".
    wp_apply (wp_maxTwoInts with "[]"). { auto. }
    iIntros (r) "%H23".
    wp_pures.
    rewrite H23.
    wp_apply (slice.wp_SliceSet with "[H8]"). { iSplitL "H8".
                                                - iApply "H8".
                                                - iPureIntro. split; auto. admit. }
    iIntros "H". wp_pures. iModIntro.
    iApply "H_ret".
  Admitted.
    
    
End heap.
