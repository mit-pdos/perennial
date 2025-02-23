From Perennial.program_proof.session Require Export session_prelude.
From Perennial.program_proof.session Require Export coq_session.

Section heap.
  Context `{hG: !heapGS Σ}.

  Lemma wp_deleteAtIndexOperation (s: Slice.t) (index: w64) (l: list Operation.t) (n: nat) :
    {{{
        ⌜0 <= uint.nat index < length l⌝ ∗
        operation_slice s l n
    }}}
      deleteAtIndexOperation s #index
    {{{
        ns, RET slice_val (ns);
        operation_slice ns (coq_deleteAtIndexOperation l (uint.nat index)) n
    }}}.
  Proof.
    rewrite/ deleteAtIndexOperation. rename s into s1. iIntros (Φ) "[%H_index (%ops1 & H_s1 & H_ops1)] HΦ".
    iPoseProof (big_sepL2_length with "[$H_ops1]") as "%claim1".
    iPoseProof (own_slice_sz with "[$H_s1]") as "%claim2".
    wp_pures. wp_apply wp_NewSlice. iIntros "%s2 H_s2". wp_apply wp_ref_to; auto.
    iIntros "%ret H_ret". wp_pures.
    iAssert ⌜uint.Z index ≤ uint.Z s1 .(Slice.cap)⌝%I as "%H_s_cap".
    { iPoseProof (own_slice_wf with "[$H_s1]") as "%claim3".
      iPoseProof (big_sepL2_length with "[$H_ops1]") as "%claim4".
      iPoseProof (own_slice_sz with "[$H_s1]") as "%claim5".
      iPureIntro. word.
    }
    iPoseProof (own_slice_cap_wf with "[H_s1]") as "%claim3".
    { iDestruct "H_s1" as "[H1_s1 H2_s1]". iFrame. }
    iAssert ⌜uint.Z index ≤ length ops1⌝%I as "%H_ops1_len".
    { iPureIntro. word. }
    wp_apply (wp_SliceTake with "[H_s1 H_s2 H_ops1 H_ret HΦ]"); eauto.
    iModIntro. wp_load.
    iPoseProof (slice_small_split _ _ _ _ _ H_ops1_len with "[H_s1]") as "[H_s1_prefix H_s1_suffix]".
    { iApply (own_slice_to_small with "[$H_s1]"). }
    wp_apply (wp_SliceAppendSlice with "[H_s2 H_s1_prefix]"); eauto.
    { iFrame. }
    iIntros "%s3 [H_s3 H_s1_prefix]". simpl in *. replace (replicate (uint.nat (W64 0)) (Slice.nil, W64 0)) with (nil (A := Slice.t * w64)) by reflexivity.
    simpl. wp_store. wp_pures.
    iPoseProof (own_slice_small_sz with "[$H_s1_prefix]") as "%claim4".
    iPoseProof (own_slice_small_sz with "[$H_s1_suffix]") as "%claim5".
    iDestruct "H_s3" as "[H1_s3 H2_s3]".
    iPoseProof (own_slice_cap_wf with "[H2_s3]") as "%claim6".
    { unfold own_slice. unfold slice.own_slice. iFrame. }
    iAssert ⌜uint.Z (w64_word_instance .(word.add) index (W64 1)) ≤ uint.Z s1 .(Slice.sz)⌝%I as "%claim7".
    { iPureIntro. word. }
    wp_apply (wp_SliceSkip); eauto.
    wp_load. wp_apply (wp_SliceAppendSlice with "[H1_s3 H2_s3 H_s1_suffix]"); eauto.
    { iSplitR "H_s1_suffix".
      - iApply own_slice_split. iFrame.
      - iPoseProof (own_slice_small_take_drop with "[$H_s1_suffix]") as "[H_s1_suffix_hd H_s1_suffix_tl]".
        { instantiate (1 := W64 1). rewrite length_drop in claim5. rewrite length_take in claim4. word. }
        instantiate (2 := DfracOwn 1). instantiate (1 := (drop (uint.nat (W64 1)) (drop (uint.nat index) ops1))).
        erewrite slice_skip_skip with (n := w64_word_instance .(word.add) index (W64 1)) (m := index) (s := s1); simpl.
        + replace (w64_word_instance .(word.sub) (w64_word_instance .(word.add) index (W64 1)) index) with (W64 1) by word. iFrame.
        + word.
        + word.
    }
    iIntros "%s4 [H1_s4 H2_s4]". iApply "HΦ". simpl.
    replace (coq_deleteAtIndexOperation l (uint.nat index)) with (take (uint.nat index) l ++ drop (uint.nat (W64 1)) (drop (uint.nat index) l)).
    - iExists ((take (uint.nat index) ops1 ++ drop (uint.nat (W64 1)) (drop (uint.nat index) ops1)))%list. iSplitR "H_ops1".
      + iFrame.
      + iPoseProof (big_sepL2_app_equiv with "[H_ops1]") as "[H_prefix H_suffix]".
        { instantiate (1 := take (uint.nat index) l). instantiate (1 := take (uint.nat index) ops1).
          rewrite length_take. rewrite length_take. word.
        }
        { instantiate (2 := drop (uint.nat index) ops1). instantiate (1 := drop (uint.nat index) l).
          rewrite take_drop. rewrite take_drop. iExact "H_ops1".
        }
        simpl. iApply (big_sepL2_app with "[H_prefix]"). { iExact "H_prefix". }
        destruct (drop (uint.nat index) ops1) as [ | ops1_hd ops1_tl] eqn: H_ops1.
        { simpl in *. iPoseProof (big_sepL2_nil_inv_l with "[$H_suffix]") as "%NIL".
          rewrite NIL. iExact "H_suffix".
        }
        iPoseProof (big_sepL2_cons_inv_l with "[$H_suffix]") as "(%l_hd & %l_tl & %H_l & H_hd & H_tl)".
        rewrite H_l. iExact "H_tl".
    - unfold coq_deleteAtIndexOperation. replace (drop (uint.nat index + 1) l) with (drop (uint.nat (W64 1)) (drop (uint.nat index) l)); trivial.
      rewrite drop_drop. f_equal.
  Qed.

  (*
  Lemma wp_deleteAtIndexMessage (s: Slice.t) (index: w64) (l: list Message.t) (n: nat) :
    {{{
        ⌜0 <= uint.nat index < length l⌝ ∗   
        message_slice s l n
    }}}
      deleteAtIndexMessage s #index
    {{{
        (ns: Slice.t), RET slice_val (ns);
        message_slice ns (coq_deleteAtIndexMessage l (uint.nat index)) n
    }}}.
  Proof.
  Admitted.
  *)

  Lemma wp_getDataFromOperationLog (s: Slice.t) (l: list Operation.t) (n: nat) :
    {{{
        operation_slice s l n
    }}}
      getDataFromOperationLog s
    {{{
        r , RET #r;
        ⌜r = coq_getDataFromOperationLog l⌝
    }}}.
  Proof.
    rewrite/ getDataFromOperationLog. wp_pures. iIntros "%Φ Hl H1". wp_pures.
    wp_rec. iDestruct "Hl" as "(%ops & Hs & Hl)". wp_if_destruct.
    - wp_rec.
      iAssert (⌜is_Some (ops !! uint.nat (w64_word_instance .(word.sub) s .(Slice.sz) (W64 1)))⌝%I) with "[Hl Hs]" as "%Hl".
      { induction ops as [ | ? ? _] using List.rev_ind.
        - iAssert (⌜l = []⌝)%I with "[Hl]" as "%Hl".
          { iApply big_sepL2_nil_inv_l. iExact "Hl". }
          subst l. simpl. iPoseProof (own_slice_sz with "[$Hs]") as "%Hs".
          simpl in *. iPureIntro. word.
        - iPoseProof (own_slice_sz with "[$Hs]") as "%Hs".
          iPureIntro. red. exists x. eapply list_lookup_middle. rewrite length_app in Hs. simpl in Hs. word.
      }
      iAssert (⌜length ops = length l⌝)%I with "[Hl]" as "%Hlength".
      { iApply big_sepL2_length. iExact "Hl". }
      destruct Hl as (x & EQ).
      wp_apply (wp_SliceGet with "[Hs] [Hl H1]").
      + iSplitL "Hs".
        * simpl (struct.t Operation). iApply (own_slice_to_small with "[Hs]"). iExact "Hs".
        * iPureIntro. exact EQ.
      + iModIntro. iIntros "Hs".
        wp_pures. iModIntro. iApply "H1".
        unfold coq_getDataFromOperationLog.
        iPoseProof (own_slice_small_sz with "[$Hs]") as "%Hs".
        induction ops as [ | ops_last ops_init _] using List.rev_ind.
        { simpl in *. word. }
        induction l as [ | l_last l_init _] using List.rev_ind.
        { simpl in *. word. }
        iPoseProof big_sepL2_snoc as "LEMMA1". iApply "LEMMA1" in "Hl". iClear "LEMMA1".
        iDestruct "Hl" as "[H_init H_last]". rewrite length_app. rewrite length_app in Hs. simpl in *.
        iPoseProof (big_sepL2_length with "[$H_init]") as "%YES".
        replace (uint.nat (W64 ((length l_init + 1)%nat - 1))) with (length l_init) by (simpl; word).
        change (list_lookup (length l_init) (l_init ++ [l_last])) with ((l_init ++ [l_last]) !! (length l_init)).
        erewrite lookup_snoc with (l := l_init) (x := l_last).
        replace (uint.nat (w64_word_instance .(word.sub) s .(Slice.sz) (W64 1))) with (length ops_init) in EQ by word.
        rewrite lookup_snoc in EQ. assert (x = ops_last) as -> by congruence. clear EQ.
        iDestruct "H_last" as "[H H1]". iFrame.
    - iModIntro. iApply "H1". unfold coq_getDataFromOperationLog.
      iAssert (⌜uint.Z (W64 0) = uint.Z s .(Slice.sz)⌝)%I as "%NIL".
      { word. }
      destruct l as [ | ? ?].
      { simpl. iPureIntro. done. }
      simpl. destruct ops as [ | ? ?].
      { iPoseProof (big_sepL2_nil_inv_l with "[$Hl]") as "%Hl". congruence. }
      iPoseProof (own_slice_sz with "[$Hs]") as "%Hs".
      simpl in Hs. word.
  Qed.

  Lemma wp_equalOperations (opv1: Slice.t*u64) (o1: Operation.t) (opv2: Slice.t*u64) (o2: Operation.t) (n: nat) :
    {{{
        is_operation opv1 o1 n ∗
        is_operation opv2 o2 n
    }}}
      equalOperations (operation_val opv1) (operation_val opv2)
    {{{
        r, RET #r;
        ⌜r = coq_equalOperations o1 o2⌝
    }}}.
  Proof. (*
    rewrite /equalOperations. iIntros "%Φ [Ho1 Ho2] HΦ".
    iDestruct "Ho1" as "(%Hopv1snd & %Hlen1 & Ho1)". iDestruct "Ho2" as "(%Hopv2snd & %Hlen2 & Ho2)".
    wp_rec. wp_pures. wp_apply (wp_equalSlices with "[Ho1 Ho2]").
    
    iIntros "%r (%OBS & Hopv1 & Hopv2 & %LEN1 & %LEN2)". wp_if_destruct.
    - wp_pures. iModIntro. iApply "Hret". unfold coq_equalOperations.
      rewrite <- OBS. simpl. rewrite Hopv1snd Hopv2snd.
      iPureIntro. destruct (_ =? _) as [ | ] eqn: H_compare.
      + rewrite Z.eqb_eq in H_compare.
        assert (EQ : o1.(Operation.Data) = o2.(Operation.Data)) by word.
        eapply bool_decide_eq_true_2. congruence.
      + rewrite Z.eqb_neq in H_compare.
        assert (NE : o1.(Operation.Data) ≠ o2.(Operation.Data)) by word.
        eapply bool_decide_eq_false_2. congruence.
    - iModIntro. iApply "Hret". unfold coq_equalOperations.
      rewrite <- OBS. simpl. iPureIntro. done. *)
  Admitted.

  Lemma wp_mergeOperations (s1 s2: Slice.t) (l1 l2: list Operation.t) (n: nat) :
    {{{
        operation_slice s1 l1 n ∗
        operation_slice s2 l2 n 
    }}}
      mergeOperations s1 s2 
    {{{
        ns, RET slice_val (ns);
        ∃ nxs, operation_slice ns nxs n ∗ ⌜nxs = coq_mergeOperations l1 l2⌝
    }}}.
  Proof.
  Admitted.

End heap.
