From Perennial.program_proof.session Require Export session_prelude coq_session.
From Perennial.program_proof.session Require Export versionVector sort.

Section heap.

  Context `{hG: !heapGS Σ}.

  Lemma wp_getGossipOperations (sv: u64*u64*Slice.t*Slice.t*Slice.t*Slice.t*Slice.t*Slice.t) (s: Server.t)
    (serverId: w64) (n: nat) :
    {{{
          is_server sv s n 
    }}}
      getGossipOperations (server_val sv) #serverId
      {{{
            ns , RET slice_val (ns);
            operation_slice ns (coq_getGossipOperations s serverId) n ∗
            is_server sv s n 
      }}}.
  Proof.
    iIntros "%Φ H1 H_ret".
    iDestruct "H1" as "(%H1 & %H2 & H1 & %H3 & H4 & H5 & H6 & H7 & %H4 & H8)".
    rewrite /getGossipOperations.
    iDestruct (own_slice_small_sz with "H8") as "%H5".
    wp_pures.
    wp_apply (wp_NewSlice).
    iIntros (s') "H".
    wp_apply (wp_ref_to). { auto. }
    iIntros (ret) "H2".
    wp_apply (wp_slice_len). wp_pures.
    wp_bind (if: #(bool_decide (uint.Z (sv.2).(Slice.sz) ≤ uint.Z serverId)) then _ else _)%E.
    wp_if_destruct.
    - wp_pures. admit.
    - wp_pures. 
      wp_apply (wp_slice_len).
      assert (uint.nat serverId < length s.(Server.GossipAcknowledgements))%nat
        by word.
      apply list_lookup_lt in H as [x H].
      wp_apply (wp_SliceGet with "[H8]"). { iFrame. auto. }
      iIntros "H8". wp_if_destruct.
      + admit.
      + wp_apply (wp_SliceGet with "[H8]"). {iFrame. auto. }
        iIntros "H8". wp_pures.
        wp_apply (wp_SliceSkip). { word. }
        wp_load.
        rewrite /operation_slice. rewrite /operation_slice'.
        iDestruct "H6" as "(%ops & H6 & H9)".
        unfold own_slice. unfold slice.own_slice.
        iDestruct "H6" as "[H6 H10]".
        wp_apply (wp_SliceAppendSlice with "[H H6]"); eauto. {
          iFrame. simpl. unfold own_slice_small.
  Admitted.

  Lemma wp_acknowledgeGossip (sv: u64*u64*Slice.t*Slice.t*Slice.t*Slice.t*Slice.t*Slice.t) (s: Server.t)
    (msgv: u64*u64*u64*u64*u64*Slice.t*u64*u64*Slice.t*u64*u64*u64*u64*u64*u64*Slice.t*u64*u64)
    (msg: Message.t) (n: nat) :
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
    iDestruct (own_slice_small_sz with "H8") as "%H22". 
    wp_if_destruct.
    { iModIntro. iApply "H_ret". iFrame.
    assert (uint.Z msg.(Message.S2S_Acknowledge_Gossip_Sending_ServerId) >=? length s.(Server.GossipAcknowledgements) = true) by word.
      iSplitL.
      - unfold coq_acknowledgeGossip.
        rewrite H. iFrame. iPureIntro.
        repeat split; auto.
      - iPureIntro. repeat split; auto.
    } 
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
                                                - iPureIntro. split; auto.
                                                  unfold is_Some.
                                                  exists (u64_IntoVal.(to_val) x).
                                                  simpl. unfold list.untype.
                                                  simpl. rewrite list_lookup_fmap.
                                                  rewrite H. auto. }
    iIntros "H". wp_pures. iModIntro.
    iApply "H_ret".
    iSplitL "H H1 H4 H5 H6 H7".
    - unfold coq_acknowledgeGossip.
      assert (uint.Z msg.(Message.S2S_Acknowledge_Gossip_Sending_ServerId) >=?
                           length s.(Server.GossipAcknowledgements) = false) by word.
      rewrite H0. 
      iSplit. { auto. }
      iSplit. { auto. }
      iSplitL "H1". { auto. }
      iSplit. { auto. }
      iSplitL "H4". { auto. }
      iSplitL "H5". { auto. }
      iSplitL "H6". { auto. }
      iSplitL "H7". { auto. }
      iSplit. { simpl. iPureIntro.
                rewrite length_insert. auto. }
      simpl.
      rewrite <- H14.
      rewrite H. 
      unfold own_slice_small.
      assert ((<[uint.nat msgv.1.1.1.1.1.1.1.2:=#(coq_maxTwoInts x msgv.1.1.1.1.1.2)]>
                 (list.untype s.(Server.GossipAcknowledgements))) =
              (list.untype
                 (<[uint.nat msgv.1.1.1.1.1.1.1.2:=coq_maxTwoInts x msg.(Message.S2S_Acknowledge_Gossip_Index)]>
                    s.(Server.GossipAcknowledgements)))).
      { unfold list.untype. rewrite list_fmap_insert. simpl. rewrite H16. auto. }
      rewrite H24. iFrame.
    - unfold is_message. iFrame.
      iPureIntro.
      repeat split; auto.
  Qed.

End heap.
