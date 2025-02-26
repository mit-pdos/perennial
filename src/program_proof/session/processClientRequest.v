From Perennial.program_proof.session Require Export session_prelude coq_session.
From Perennial.program_proof.session Require Export versionVector sort.

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
    rewrite/ deleteAtIndexMessage. rename s into s1. iIntros (Φ) "[%H_index (%ops1 & H_s1 & H_ops1)] HΦ".
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
    iAssert ⌜uint.Z (w64_word_instance .(word.add) index (W64 1)) ≤ length ops1⌝%I as "%YES". { word. }
    iPoseProof (slice_small_split _ _ _ _ _ YES with "[H_s1]") as "[H1_s1 H3_s1]".
    { iApply (own_slice_to_small with "[$H_s1]"). }
    assert (forall A : Type, forall x : A, replicate (uint.nat (W64 0)) x = []) as YES1 by reflexivity.
    rewrite YES1. simpl. clear YES1.
    assert (uint.Z index ≤ length (take (uint.nat (w64_word_instance .(word.add) index (W64 1))) ops1)) as YES2. { rewrite length_take. word. }
    iPoseProof (slice_small_split _ _ _ _ _ YES2 with "[$H1_s1]") as "[H1_s1 H2_s1]".
    wp_apply (wp_SliceAppendSlice with "[H_s2 H1_s1]"); eauto.
    { done. } { iFrame. } iIntros "%s' [H1_s' H2_s']". wp_pures. wp_store.
    wp_apply (wp_SliceSkip); eauto. { word. } wp_load. wp_apply (wp_SliceAppendSlice with "[H1_s' H3_s1]"). { done. }
    { simpl in *. iFrame. } iIntros "%s'' [H1_s'' H2_s'']". iApply "HΦ".
    unfold message_slice, message_slice'. iExists (take (uint.nat index) ops1 ++ drop (uint.nat index + 1)%nat ops1). iSplitR "H_ops1".
    - remember (uint.nat index) as k eqn: H_k in *.
      replace (uint.nat (w64_word_instance .(word.add) index (W64 1))) with (k + 1)%nat in * by word.
      rewrite take_take. replace (k `min` (k + 1))%nat with k by word. iFrame.
    - unfold coq_deleteAtIndexMessage. iPoseProof (big_sepL2_length with "[$H_ops1]") as "%YES1".
      iApply big_sepL2_app_equiv. { do 2 rewrite length_take; word. }
      rewrite <- take_drop with (l := ops1) (i := uint.nat index) at 1.
      rewrite <- take_drop with (l := l) (i := uint.nat index) at 1.
      iAssert (([∗ list] mv;m ∈ take (uint.nat index) ops1;take (uint.nat index) l, is_message mv m n) ∗ ([∗ list] mv;m ∈ drop (uint.nat index) ops1;drop (uint.nat index) l, is_message mv m n))%I with "[H_ops1]" as "[H_prefix H_suffix]".
      { iApply (big_sepL2_app_equiv with "[$H_ops1]"). do 2 rewrite length_take. word. }
      iFrame. destruct (drop (uint.nat index) ops1) as [ | hd tl] eqn: H_obs.
      + iPoseProof (big_sepL2_nil_inv_l with "[$H_suffix]") as "%H_obs'".
        do 2 rewrite <- drop_drop. rewrite H_obs H_obs'. simpl. done.
      + iPoseProof (big_sepL2_cons_inv_l with "[$H_suffix]") as "(%hd' & %tl' & %H_obs' & H1 & H2)".
        do 2 rewrite <- drop_drop. rewrite H_obs H_obs'. simpl. done.
  Qed.

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
  Proof.
    rewrite /equalOperations. iIntros "%Φ [Ho1 Ho2] HΦ".
    iDestruct "Ho1" as "(%Hopv1snd & %Hlen1 & Ho1)". iDestruct "Ho2" as "(%Hopv2snd & %Hlen2 & Ho2)".
    wp_rec. wp_pures. wp_apply (wp_equalSlices with "[Ho1 Ho2]"). { iFrame. iPureIntro. word. }
    iIntros "%r (-> & Hopv1 & Hopv2 & %LEN)". wp_if_destruct.
    - wp_pures. iModIntro. iApply "HΦ". unfold coq_equalOperations.
      simpl. rewrite Hopv1snd Hopv2snd.
      iPureIntro. destruct (_ =? _) as [ | ] eqn: H_compare.
      + rewrite Z.eqb_eq in H_compare.
        assert (EQ : o1.(Operation.Data) = o2.(Operation.Data)) by word.
        rewrite andb_true_r. rewrite Heqb. eapply bool_decide_eq_true_2. congruence.
      + rewrite Z.eqb_neq in H_compare.
        assert (NE : o1.(Operation.Data) ≠ o2.(Operation.Data)) by word.
        rewrite andb_false_r. eapply bool_decide_eq_false_2. congruence.
    - iModIntro. iApply "HΦ". unfold coq_equalOperations.
      simpl. rewrite Heqb. simpl. iPureIntro. done.
  Qed.

  Lemma wp_mergeOperations (s1 s2: Slice.t) (l1 l2: list Operation.t) (n: nat) :
    {{{
        operation_slice s1 l1 n ∗
        operation_slice s2 l2 n ∗
        ⌜is_sorted l1⌝
    }}}
      mergeOperations s1 s2 
    {{{
        ns, RET slice_val (ns);
        ∃ nxs, operation_slice ns nxs n ∗
        ⌜nxs = coq_mergeOperations l1 l2⌝ ∗
        ⌜is_sorted nxs⌝
    }}}.
  Proof.
    rewrite /mergeOperations. iIntros "%Φ ((%l1_ops & H_s1 & H_l1_ops) & (%l2_ops & H_s2 & H_l2_ops) & %l1_sorted) HΦ".
    iPoseProof (own_slice_sz with "[$H_s1]") as "%H_l1_len".
    iPoseProof (own_slice_sz with "[$H_s2]") as "%H_l2_len".
    wp_apply wp_slice_len. wp_pures. destruct (bool_decide (#s1 .(Slice.sz) = #(W64 0))) as [ | ] eqn: decide_s1.
    - wp_pures. wp_apply wp_slice_len. wp_pures. destruct (bool_decide (#s2 .(Slice.sz) = #(W64 0))) as [ | ] eqn: decide_s2.
      + wp_pures. rewrite -> bool_decide_eq_true in decide_s1, decide_s2.
        assert (s1 .(Slice.sz) = W64 0) as s1_sz_eq_0 by congruence.
        assert (s2 .(Slice.sz) = W64 0) as s2_sz_eq_0 by congruence.
        rewrite s1_sz_eq_0 in H_l1_len. rewrite s2_sz_eq_0 in H_l2_len. simpl in *.
        replace (uint.nat (W64 0)) with 0%nat in H_l1_len by reflexivity.
        replace (uint.nat (W64 0)) with 0%nat in H_l2_len by reflexivity.
        apply nil_length_inv in H_l1_len. apply nil_length_inv in H_l2_len. subst l1_ops l2_ops.
        iPoseProof (big_sepL2_nil_inv_l with "[$H_l1_ops]") as "->".
        iPoseProof (big_sepL2_nil_inv_l with "[$H_l2_ops]") as "->".
        wp_apply wp_NewSlice. iIntros "%s3 H_s3". replace (replicate (uint.nat (W64 0)) operation_into_val .(IntoVal_def (Slice.t * w64))) with (@nil (Slice.t * w64)) by reflexivity.
        iApply "HΦ". iExists []. iFrame. done.
      + wp_pures. rewrite -> bool_decide_eq_true in decide_s1. rewrite -> bool_decide_eq_false in decide_s2.
        assert (s1 .(Slice.sz) = W64 0) as s1_sz_eq_0 by congruence.
        assert (s2 .(Slice.sz) ≠ W64 0) as s2_sz_ne_0 by congruence.
        rewrite s1_sz_eq_0 in H_l1_len. simpl in *.
        replace (uint.nat (W64 0)) with 0%nat in H_l1_len by reflexivity.
        apply nil_length_inv in H_l1_len. subst l1_ops.
        iPoseProof (big_sepL2_nil_inv_l with "[$H_l1_ops]") as "->". iPoseProof (big_sepL2_length with "[$H_l2_ops]") as "%H_l2_length". iPoseProof (own_slice_sz with "[$H_s2]") as "%H_s2_sz". simpl in *.
        wp_apply wp_NewSlice. iIntros "%s3 H_s3". replace (replicate (uint.nat (W64 0)) operation_into_val .(IntoVal_def (Slice.t * w64))) with (@nil (Slice.t * w64)) by reflexivity.
        iDestruct "H_s1" as "[H1_s1 H2_s1]". wp_apply (wp_SliceAppendSlice with "[$H_s3 $H1_s1]"); auto. simpl. iIntros "%s4 [H_s4 H1_s1]".
        wp_apply wp_ref_to; auto. iIntros "%intermediate H_intermediate". wp_pures. wp_apply wp_ref_to; auto.
        wp_pures. iIntros "%i H_i". wp_pures. wp_apply wp_slice_len. wp_apply wp_ref_to; auto. iIntros "%l H_l". wp_pures.
        clear s3 l1_sorted decide_s1 decide_s2.
        wp_apply (wp_forBreak_cond
          ( λ continue, ∃ s4 : Slice.t, ∃ l3_ops : list (Slice.t * w64), ∃ l2_prevs : list Operation.t, ∃ l2_nexts : list Operation.t,
            "H_s2" ∷ own_slice_small s2 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l2_ops ∗
            "H_s4" ∷ own_slice s4 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l3_ops ∗
            ([∗ list] opv;o ∈ drop (length l2_prevs) l2_ops;l2_nexts, is_operation opv o n) ∗
            ([∗ list] opv;o ∈ l3_ops;fold_left coq_sortedInsert l2_prevs [], is_operation opv o n) ∗
            ⌜l2 = l2_prevs ++ l2_nexts⌝ ∗
            i ↦[uint64T] #(W64 (length l2_prevs)) ∗
            l ↦[uint64T] #s2 .(Slice.sz) ∗
            intermediate ↦[slice.T (slice.T uint64T * (uint64T * unitT)%ht)] s4 ∗
            ⌜is_sorted (fold_left coq_sortedInsert l2_prevs [])⌝ ∗
            ⌜Forall (Operation_wf n) (fold_left SessionPrelude.sortedInsert l2_prevs [])⌝ ∗
            ⌜length (fold_left SessionPrelude.sortedInsert l2_prevs []) = length l2_prevs⌝ ∗
            ⌜continue = false -> l2_nexts = []⌝
          )%I
        with "[] [H_l2_ops H_s2 H_s4 H_intermediate H_i H_l]").
        { clear Φ s4. iIntros "%Φ". iModIntro. iIntros "(%s4 & %l3_ops & %l2_prevs & %l2_nexts & H_s2 & H_s4 & H_l2_ops & H_l3_ops & %l2_eq & H_i & H_l & H_intermediate & %H_is_sorted & %H_wf & %H_length & %H_continue) HΦ".
          wp_load. wp_load. wp_if_destruct.
          - wp_pures. wp_load. destruct l2_nexts as [ | l2_cur l2_nexts].
            + rewrite app_nil_r in l2_eq. subst l2_prevs. word.
            + iNamed "H_s2". iNamed "H_s4". iPoseProof (big_sepL2_cons_inv_r with "[$H_l2_ops]") as "(%l2_ops_cur & %l2_ops_nexts & %H_OBS & H_l2_cur & H_l2_nexts)".
              pose proof (take_drop (length l2_prevs) l2_ops) as H2_l2_ops.
              rewrite H_OBS in H2_l2_ops.
              iAssert ⌜Operation_wf n l2_cur⌝%I as "%H2_wf".
              { iDestruct "H_l2_cur" as "(%H1 & %H2 & H3)". iPureIntro. split.
                - eapply SessionPrelude.Forall_True.
                - done.
              }
              iAssert ⌜Forall (Operation_wf n) l2_nexts⌝%I as "%H1_wf".
              { iApply Forall_Operation_wf; done. }
              wp_apply (wp_SliceGet with "[H_s2]").
              { iSplitL "H_s2".
                - iExact "H_s2".
                - rewrite l2_eq in H_l2_length. rewrite length_app in H_l2_length. simpl in *.
                  iPureIntro. replace (uint.nat (W64 (length l2_prevs))) with (length l2_prevs) by word.
                  rewrite <- H2_l2_ops. eapply list_lookup_middle. rewrite length_take. word.
              }
              iIntros "H_s2". wp_load. wp_apply (wp_sortedInsert with "[$H_s4 $H_l2_cur $H_l3_ops]"); auto.
              iIntros "%ns (%nxs & H_ns & %H_nxs)". wp_store. wp_load. wp_store. iModIntro. iApply "HΦ".
              iDestruct "H_ns" as "(%ns_ops & H_ns & H_ns_ops)". subst nxs.
              iExists ns. iExists ns_ops. iExists (l2_prevs ++ [l2_cur])%list. iExists l2_nexts. iFrame.
              iSplitL "H_l2_nexts". { rewrite length_app. simpl in *. rewrite <- drop_drop. rewrite H_OBS. simpl. done. }
              iSplitL "H_ns_ops". { rewrite fold_left_app. simpl in *. done. }
              iSplitL "". { rewrite <- app_assoc. done. }
              iSplitL "H_i". { rewrite length_app. simpl. rewrite l2_eq in H_l2_length. rewrite length_app in H_l2_length. simpl in *. replace ((w64_word_instance .(word.add) (W64 (length l2_prevs)) (W64 1))) with (W64 (length l2_prevs + 1)%nat) by word. done. }
              iSplit. { rewrite fold_left_app. simpl in *. iPureIntro. replace is_sorted with (SessionPrelude.isSorted (hsOrd := hsOrd_Operation n)) by reflexivity. rewrite -> redefine_coq_sortedInsert with (len := n). eapply SessionPrelude.sortedInsert_isSorted; eauto. }
              pose proof (SessionPrelude.sortedInsert_spec (hsOrd := hsOrd_Operation n) _ _ H_wf H2_wf H_is_sorted) as (prefix & suffix & H1 & H2 & H3 & H4 & YES).
              iSplit. { rewrite fold_left_app. simpl in *. iPureIntro. done. }
              iSplit. { rewrite fold_left_app. simpl in *. iPureIntro. rewrite -> H2. rewrite length_app. simpl. apply f_equal with (f := length) in H1. rewrite length_app in H1. rewrite length_app. simpl. rewrite H1 in H_length. word. }
              { iPureIntro. congruence. }
          - iNamed "H_s2". iNamed "H_s4".
            iAssert ⌜l2_nexts = []⌝%I as "%l2_nexts_nil".
            { rewrite l2_eq in H_l2_length. rewrite length_app in H_l2_length.
              assert (uint.Z (W64 (length l2_prevs)) = uint.Z s2 .(Slice.sz)) as YES1 by word.
              assert (length l2_nexts = 0%nat) as YES2 by word.
              iPureIntro. destruct l2_nexts as [ | ? ?]; [done | simpl in *; word].
            }
            subst l2_nexts. rewrite app_nil_r in l2_eq. subst l2.
            iApply "HΦ". iModIntro. iExists s4. iExists l3_ops. iExists l2_prevs. iExists []. iFrame. rewrite app_nil_r. done.
        }
        { iExists s4. iExists []. iExists []. iExists l2. simpl in *. iFrame. iSplitL "H_s2".
          - iApply own_slice_to_small; done.
          - iSplit. { done. } iSplit. { done. } iSplit. { done. } iSplit. { done. } { iPureIntro. congruence. }
        }
        clear s4. iIntros "(%s4 & %l3_ops & %l2_prevs & %l2_nexts & H_s2 & H_s4 & H_l2_ops_nexts & H_l3_ops & %H_l2_obs & H_i & H_l & H_intermediate & %H2_is_sorted & %H2_wf & %H3_length & %H_continue)".
        specialize (H_continue eq_refl). subst l2_nexts. rewrite app_nil_r in H_l2_obs. subst l2_prevs.
        iNamed "H_s2". iNamed "H_s4". wp_pures. wp_apply wp_ref_to; eauto. iIntros "%prev H_prev". wp_pures. wp_apply wp_ref_to; auto. iIntros "%curr H_curr". wp_pures.
        replace SessionPrelude.sortedInsert with coq_sortedInsert in H2_wf by reflexivity. remember (fold_left coq_sortedInsert l2 []) as l3 eqn: H_l3 in *.
        set (loop_step := λ (acc: nat * list Operation.t) (element : Operation.t),
          let (index, acc) := acc in
            match (l3 !! (index + 1)%nat) with
            | Some v => if (coq_equalOperations element v) then ((index + 1)%nat, acc) else ((index + 1)%nat, acc ++ [element])
            | None => ((index + 1)%nat, acc ++ [element])
            end
        ).
        set (loop_init := (0%nat, @nil Operation.t)).
        iRename "H_s4" into "H_s3". rename s4 into s3.
        iPoseProof (big_sepL2_length with "[$H_l3_ops]") as "%YES1".
        wp_apply (wp_forBreak_cond
          ( λ continue, ∃ index : nat, ∃ acc : list Operation.t, ∃ peek_l : Operation.t, ∃ l3_ops : list (Slice.t * w64),
            own_slice_small s3 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l3_ops ∗
            ([∗ list] opv;o ∈ l3_ops;acc ++ [peek_l] ++ drop (length acc + 1)%nat l3, is_operation opv o n) ∗
            i ↦[uint64T] #(W64 (length l2)) ∗
            l ↦[uint64T] #s2 .(Slice.sz) ∗
            intermediate ↦[slice.T (slice.T uint64T * (uint64T * unitT)%ht)] s3 ∗
            prev ↦[uint64T] #(length acc + 1)%nat ∗
            curr ↦[uint64T] #(index + 1)%nat ∗
            ⌜l3 !! index = Some peek_l⌝ ∗
            ⌜(index, acc) = fold_left loop_step (take index l3) loop_init⌝ ∗
            ⌜continue = false -> drop (index + 1)%nat l3 = []⌝ ∗
            ⌜is_sorted (acc ++ [peek_l])⌝ ∗
            ⌜Forall (Operation_wf n) (acc ++ [peek_l])⌝ ∗
            ⌜length l3 = length l3_ops⌝ ∗
            ⌜(length acc <= index)%nat⌝ ∗
            ⌜(index + 1 <= length l3)%nat⌝
          )%I
        with "[] [H_l3_ops H1_s1 H_s2 H_s3 H_intermediate H_prev H_curr H_i H_l]").
        { clear Φ l3_ops YES1. iIntros "%Φ". iModIntro. iIntros "(%index & %acc & %peek_l & %l3_ops & H_s3 & H_l3_ops & H_i & H_l & H_intermediate & H_prev & H_curr & %H) HΦ".
          destruct H as (H_peek_l' & H_loop & H_continue & H3_is_sorted & H_wf & LENGTH & H1_index & H2_index).
          wp_pures. wp_load. wp_load. wp_apply (wp_slice_len). wp_if_destruct.
          - iPoseProof (pers_big_sepL2_is_operation with "[$H_l3_ops]") as "#YES".
            iPoseProof (big_sepL2_length with "[$H_l3_ops]") as "%H_l3_ops_len".
            iPoseProof (own_slice_small_sz with "[$H_s3]") as "%H_s3_sz".
            rewrite app_assoc. rewrite <- take_drop with (l := l3_ops) (i := (length acc + 1)%nat).
            iPoseProof (big_sepL2_app_equiv with "[$H_l3_ops]") as "[H_l3_ops_prefix H_l3_ops_suffix]".
            { rewrite length_app. simpl. rewrite length_take. rewrite H_l3_ops_len. repeat rewrite length_app. simpl in *. word. }
            assert (index + 1 < uint.nat s3 .(Slice.sz))%nat as NE_NIL.
            { assert (uint.nat (W64 (index + 1)%nat) < uint.nat s3 .(Slice.sz))%nat as YES1 by word.
              assert (index < length l3)%nat as YES2 by now eapply lookup_lt_is_Some_1.
              word.
            }
            clear Heqb.
            assert (is_Some (l3 !! (index + 1)%nat)) as [peek_r H_peek_r].
            { eapply lookup_lt_is_Some_2. word. }
            induction (take (length acc + 1) l3_ops) as [ | peek_l_ops acc_ops _] eqn: H_l3_ops_prefix_obs using rev_ind.
            { pose proof (f_equal length H_l3_ops_prefix_obs) as H_contra. simpl in *.
              rewrite length_take in H_contra. rewrite H_l3_ops_len in H_contra. rewrite length_app in H_contra. simpl in *. word.
            }
            iAssert (([∗ list] y1;y2 ∈ acc_ops;acc, is_operation y1 y2 n) ∗ (is_operation peek_l_ops peek_l n))%I with "[H_l3_ops_prefix]" as "[H_peek_l_ops H_acc_ops]".
            { iApply (big_sepL2_snoc with "H_l3_ops_prefix"). }
            iPoseProof (big_sepL2_length with "[$H_peek_l_ops]") as "%H_acc_length".
            iAssert ⌜is_Some (((acc_ops ++ [peek_l_ops]) ++ drop (length acc + 1) l3_ops) !! uint.nat (W64 (index + 1)%nat))⌝%I as "[%peek_r_ops %H_peek_r_ops]".
            { iPureIntro. eapply lookup_lt_is_Some_2. rewrite <- H_l3_ops_prefix_obs. rewrite take_drop. word. }
            iAssert ⌜is_Some (((acc_ops ++ [peek_l_ops]) ++ drop (length acc + 1) l3_ops) !! uint.nat (w64_word_instance .(word.sub) (W64 (index + 1)%nat) (W64 1)))⌝%I as "[%peek_l_ops' %H_peek_l_ops']".
            { iPureIntro. eapply lookup_lt_is_Some_2. rewrite <- H_l3_ops_prefix_obs. rewrite take_drop. word. }
            wp_pures. wp_load. wp_load. wp_apply (wp_SliceGet with "[$H_s3]"); auto. iIntros "H_s3".
            wp_pures. wp_load. wp_load. wp_apply (wp_SliceGet with "[$H_s3]"); auto. iIntros "H_s3".
            rewrite <- H_l3_ops_prefix_obs in H_peek_l_ops', H_peek_r_ops. rewrite take_drop in H_peek_l_ops', H_peek_r_ops.
            replace (uint.nat (W64 (index + 1)%nat)) with (index + 1)%nat in H_peek_r_ops by word.
            replace (uint.nat (w64_word_instance .(word.sub) (W64 (index + 1)%nat) (W64 1))) with index in H_peek_l_ops' by word.
            simpl. wp_apply (wp_equalOperations with "[]").
            { assert (length acc <= index)%nat as YES1 by word. iSplitL.
              - iApply big_sepL2_is_operation_elim; cycle 1.
                + exact H_peek_l_ops'.
                + rewrite <- H_l3_ops_prefix_obs. rewrite take_drop. iExact "YES".
                + instantiate (1 := peek_l).
                  rewrite <- app_assoc. rewrite -> lookup_app_r; auto.
                  replace (length acc) with (length (take (length acc) l3)); cycle 1.
                  { rewrite length_take. word. }
                  erewrite <- lookup_app_r; cycle 1.
                  { rewrite length_take. word. }
                  assert (length acc < index \/ length acc = index)%nat as [H1 | H1] by word.
                  * rewrite lookup_app_r; cycle 1.
                    { rewrite length_take. word. }
                    rewrite lookup_app_r; cycle 1.
                    { rewrite length_take. simpl. word. }
                    rewrite <- take_drop with (l := l3) (i := (length (take (length acc) l3) + 1)%nat) in H_peek_l'.
                    rewrite lookup_app_r in H_peek_l'; cycle 1.
                    { do 2 rewrite length_take. word. }
                    simpl in *. replace (index - length (take (length acc) l3) - 1)%nat with (index - length (take (length (take (length acc) l3) + 1) l3))%nat; eauto.
                    { rewrite length_take. word. }
                  * rewrite lookup_app_r; cycle 1.
                    { rewrite length_take. word. }
                    replace (index - length (take (length acc) l3))%nat with 0%nat; eauto.
                    { rewrite length_take; word. }
              - iApply big_sepL2_is_operation_elim; cycle 1.
                + exact H_peek_r_ops.
                + rewrite <- H_l3_ops_prefix_obs. rewrite take_drop. iExact "YES".
                + instantiate (1 := peek_r).
                  rewrite lookup_app_r; cycle 1.
                  { rewrite length_app. simpl. word. }
                  rewrite <- take_drop with (l := l3) (i := length (acc ++ [peek_l])) in H_peek_r.
                  rewrite lookup_app_r in H_peek_r; cycle 1.
                  { rewrite length_take. rewrite length_app. simpl. word. }
                  rewrite length_app in H_peek_r. simpl in *.
                  replace (index + 1 - length (acc ++ [peek_l]))%nat with (index + 1 - length (take (length acc + 1) l3))%nat; eauto.
                  { rewrite length_take. rewrite length_app. simpl in *. word. }
            }
            iIntros "%r %Hr". wp_if_destruct.
            + wp_load. wp_load. wp_apply (wp_SliceGet with "[$H_s3]").
              { iPureIntro. rewrite <- H_l3_ops_prefix_obs. rewrite take_drop. replace (uint.nat (W64 (index + 1)%nat)) with (index + 1)%nat by word. exact H_peek_r_ops. }
              iIntros "H_s3". wp_load. wp_load. wp_apply (wp_SliceSet with "[$H_s3]").
              { iPureIntro. replace (uint.nat (W64 (length acc + 1)%nat)) with (length (acc_ops ++ [peek_l_ops])).
                - rewrite lookup_app_r.
                  + replace (length (acc_ops ++ [peek_l_ops]) - length (acc_ops ++ [peek_l_ops]))%nat with 0%nat by word.
                    eapply lookup_lt_is_Some_2. rewrite length_drop. word.
                  + word.
                - rewrite length_app. simpl. word.
              }
              iIntros "H_s3". wp_pures. wp_load. wp_store. wp_pures. wp_load. wp_store. iModIntro. iApply "HΦ".
              iExists (index + 1)%nat. iExists (acc ++ [peek_l])%list. iExists peek_r. iExists ((<[uint.nat (W64 (length acc + 1)%nat):=peek_r_ops]> ((acc_ops ++ [peek_l_ops]) ++ drop (length acc + 1) l3_ops)))%list. iFrame.
              iSplitL "".
              { iApply big_sepL2_is_operation_intro.
                - rewrite length_insert. repeat rewrite length_app. simpl in *.
                  rewrite H_acc_length. do 2 rewrite length_drop. rewrite LENGTH. word.
                - clear i. iIntros "%i %l_i %ops_i [%H1 %H2]".
                  assert (i = uint.nat (W64 (length acc + 1)%nat) \/ i ≠ uint.nat (W64 (length acc + 1)%nat)) as [EQ | NE] by word.
                  + iApply big_sepL2_is_operation_elim; cycle -1.
                    * iExact "YES".
                    * instantiate (1 := (index + 1)%nat). subst i.
                      rewrite lookup_app_r; cycle 1.
                      { rewrite length_app. simpl in *. word. }
                      rewrite length_app. simpl in *.
                      rewrite lookup_app_r in H1; cycle 1.
                      { rewrite length_app. simpl in *. word. }
                      rewrite length_app in H1. simpl in *.
                      rewrite lookup_cons in H1. destruct (uint.nat (W64 (length acc + 1)%nat) - (length acc + 1))%nat as [ | i] eqn: H_i.
                      { simpl. rewrite <- H1. rewrite <- take_drop with (l := fold_left coq_sortedInsert l2 []) (i := (length acc + 1)%nat) in H_peek_r. rewrite lookup_app_r in H_peek_r.
                        - rewrite length_take in H_peek_r. replace (index + 1 - (length acc + 1) `min` length (fold_left coq_sortedInsert l2 []))%nat with (index + 1 - (length acc + 1))%nat in H_peek_r; eauto. word.
                        - rewrite length_take. word.
                      }
                      { simpl in *. word. }
                    * subst i. rewrite -> list_lookup_insert in H2.
                      { rewrite <- H2. rewrite <- take_drop with (l := l3_ops) (i := (length acc + 1)%nat) in H_peek_r_ops. rewrite lookup_app_r in H_peek_r_ops.
                        - rewrite lookup_app_r.
                          + rewrite length_app. simpl in *. rewrite length_take in H_peek_r_ops.
                            replace (index + 1 - (length acc_ops + 1))%nat with (index + 1 - (length acc + 1) `min` length l3_ops)%nat; eauto. word.
                          + rewrite length_app. simpl. word.
                        - rewrite length_take. word.
                      }
                      { rewrite length_app. rewrite length_drop. rewrite length_app. simpl. word. }
                  + iApply big_sepL2_is_operation_elim; cycle -1.
                    * iExact "YES".
                    * instantiate (1 := i). assert (i < uint.nat (W64 (length acc + 1)%nat) \/ i > uint.nat (W64 (length acc + 1)%nat))%nat as [LT | GT] by word.
                      { rewrite lookup_app_l.
                        - rewrite lookup_app_l in H1; eauto. rewrite length_app; simpl; word.
                        - rewrite length_app; simpl; word.
                      }
                      { rewrite lookup_app_r; cycle 1. { rewrite length_app. simpl. word. }
                        rewrite lookup_app_r in H1; cycle 1. { rewrite length_app. simpl. word. } rewrite lookup_cons in H1.
                        destruct (i - length (acc ++ [peek_l]))%nat as [ | i'] eqn: H_i'.
                        - rewrite length_app in H_i'. simpl in *; word.
                        - rewrite length_app in H1. simpl in *. rewrite <- drop_drop in H1.
                          rewrite lookup_drop in H1. replace (S i') with (1 + i')%nat by word; eauto.
                      }
                    * rewrite list_lookup_insert_ne in H2; cycle 1. { word. } eauto.
              }
              iSplitL "H_prev".
              { replace (W64 (length (acc ++ [peek_l]) + 1)%nat) with (w64_word_instance .(word.add) (W64 (length acc + 1)%nat) (W64 1)). { done. }
                rewrite length_app. simpl in *. word.
              }
              iSplitL "H_curr".
              { replace (W64 (index + 1 + 1)%nat) with (w64_word_instance .(word.add) (W64 (index + 1)%nat) (W64 1)). { done. }
                word.
              }
              iClear "H_l3_ops_suffix". iClear "H_peek_l_ops". iClear "H_acc_ops". iSplit.
              { iPureIntro. eauto. }
              iSplit.
              { assert ((take (index + 1) (fold_left coq_sortedInsert l2 [])) = take index (fold_left coq_sortedInsert l2 []) ++ [peek_l]) as LOOK.
                - rewrite <- take_drop with (l := take (index + 1) (fold_left coq_sortedInsert l2 [])) (i := index).
                  rewrite take_take. replace (index `min` (index + 1))%nat with index by word. f_equal.
                  rewrite skipn_firstn_comm. replace (index + 1 - index)%nat with 1%nat by word.
                  rewrite <- take_drop with (l := fold_left coq_sortedInsert l2 []) (i := index) in H_peek_l'.
                  rewrite lookup_app_r in H_peek_l'; cycle 1. { rewrite length_take. word. }
                  replace (index - length (take index (fold_left coq_sortedInsert l2 [])))%nat with 0%nat in H_peek_l'; cycle 1. { rewrite length_take. word. }
                  destruct (drop index (fold_left coq_sortedInsert l2 [])) as [ | hd tl] eqn: H_OBS.
                  + rewrite lookup_nil in H_peek_l'. congruence.
                  + simpl in *. replace (take 0 tl) with (@nil Operation.t) by reflexivity. congruence.
                - rewrite LOOK. rewrite fold_left_app. simpl. iPureIntro.
                  unfold loop_step at 1. rewrite <- H_loop. 
                  rewrite H_peek_r. rewrite Heqb. reflexivity.
              }
              iSplit.
              { iPureIntro. congruence. }
              assert (Operation_wf n peek_r) as H_wf'.
              { eapply Forall_lookup_1 with (l := fold_left coq_sortedInsert l2 []); eauto. }
              iSplit.
              { iPureIntro. replace is_sorted with (SessionPrelude.isSorted (hsOrd := hsOrd_Operation n)) in * by reflexivity.
                rewrite -> SessionPrelude.isSorted_iff_isSorted' in H3_is_sorted; auto.
                red in H3_is_sorted |- *. clear i. intros i j i_le_j x1 x2 H_x1 H_x2.
                assert (i = length (acc ++ [peek_l]) \/ i < length (acc ++ [peek_l]))%nat as i_RANGE.
                { enough (i < length ((acc ++ [peek_l]) ++ [peek_r]))%nat as YES.
                  - rewrite length_app in YES. simpl in *. word.
                  - eapply lookup_lt_is_Some_1. exists x1. done.
                }
                assert (j = length (acc ++ [peek_l]) \/ j < length (acc ++ [peek_l]))%nat as j_RANGE.
                { enough (j < length ((acc ++ [peek_l]) ++ [peek_r]))%nat as YES.
                  - rewrite length_app in YES. simpl in *. word.
                  - eapply lookup_lt_is_Some_1. exists x2. done.
                }
                destruct i_RANGE as [EQ1 | LT1], j_RANGE as [EQ2 | LT2].
                - subst i j. rewrite -> lookup_snoc in H_x1, H_x2. right. replace x2 with peek_r by congruence. replace x1 with peek_r by congruence. rewrite SessionPrelude.eqb_eq; eauto.
                  eapply SessionPrelude.eqProp_reflexivity; eauto.
                - word.
                - subst j. rewrite -> lookup_snoc in H_x2. replace x2 with peek_r by congruence.
                  rewrite lookup_app_l in H_x1; cycle 1. { word. }
                  assert ((hsOrd_Operation n) .(SessionPrelude.ltb) x1 peek_l = true ∨ (hsEq_Operation n) .(SessionPrelude.eqb) peek_l x1 = true) as H1.
                  { eapply H3_is_sorted with (i := i) (j := length acc).
                    - rewrite length_app in i_le_j. simpl in *. word.
                    - eauto.
                    - rewrite lookup_snoc. reflexivity.
                  }
                  assert ((hsOrd_Operation n) .(SessionPrelude.ltb) peek_l peek_r = true ∨ (hsEq_Operation n) .(SessionPrelude.eqb) peek_r peek_l = true) as H2.
                  { eapply H2_is_sorted with (i := index) (j := (index + 1)%nat).
                    - word.
                    - eauto.
                    - eauto.
                  }
                  assert (Operation_wf n x1) as H.
                  { eapply Forall_lookup_1; eauto. }
                  assert (Operation_wf n peek_l) as H0.
                  { eapply Forall_lookup_1; eauto. eapply lookup_snoc. }
                  destruct H1 as [H1 | H1], H2 as [H2 | H2].
                  + left. rewrite SessionPrelude.ltb_lt in H1; trivial. rewrite SessionPrelude.ltb_lt in H2; trivial. rewrite SessionPrelude.ltb_lt; trivial. eapply SessionPrelude.ltProp_transitivity; eauto.
                  + left. rewrite SessionPrelude.ltb_lt in H1; trivial. rewrite SessionPrelude.eqb_eq in H2; trivial. rewrite SessionPrelude.ltb_lt; trivial. pose proof (SessionPrelude.ltProp_trichotomy (hsOrd := hsOrd_Operation n) x1 peek_r) as [H3 | [H3 | H3]]; trivial.
                    * contradiction (SessionPrelude.ltProp_irreflexivity (hsOrd := hsOrd_Operation n) x1 peek_l).
                      eapply SessionPrelude.eqProp_transitivity with (y := peek_r); eauto.
                    * contradiction (SessionPrelude.ltProp_irreflexivity (hsOrd := hsOrd_Operation n) peek_r peek_l).
                      eapply SessionPrelude.ltProp_transitivity with (y := x1); eauto.
                  + left. rewrite SessionPrelude.ltb_lt in H2; trivial. rewrite SessionPrelude.eqb_eq in H1; trivial. rewrite SessionPrelude.ltb_lt; trivial. pose proof (SessionPrelude.ltProp_trichotomy (hsOrd := hsOrd_Operation n) x1 peek_r) as [H3 | [H3 | H3]]; trivial.
                    * contradiction (SessionPrelude.ltProp_irreflexivity (hsOrd := hsOrd_Operation n) peek_l peek_r).
                      eapply SessionPrelude.eqProp_transitivity with (y := x1); eauto.
                    * contradiction (SessionPrelude.ltProp_irreflexivity (hsOrd := hsOrd_Operation n) peek_l x1).
                      eapply SessionPrelude.ltProp_transitivity with (y := peek_r); eauto.
                  + right. rewrite -> SessionPrelude.eqb_eq in H1, H2 |- *; trivial. eapply SessionPrelude.eqProp_transitivity with (y := peek_l); eauto.
                - eapply H3_is_sorted with (i := i) (j := j).
                  + word.
                  + rewrite lookup_app_l in H_x1; trivial.
                  + rewrite lookup_app_l in H_x2; trivial.
              }
              iSplit.
              { iPureIntro. eapply Forall_app; split; trivial. econstructor; eauto. }
              iSplit.
              { iPureIntro. rewrite length_insert. rewrite length_app. rewrite length_drop. rewrite length_app. simpl. word. }
              { iPureIntro. rewrite length_app. simpl. word. }
            + wp_pures. wp_load. wp_store. iModIntro. iApply "HΦ".
              assert (Operation_wf n peek_l) as H_wf'.
              { eapply Forall_lookup_1 with (l := fold_left coq_sortedInsert l2 []); eauto. }
              assert (Operation_wf n peek_r) as H_wf''.
              { eapply Forall_lookup_1 with (l := fold_left coq_sortedInsert l2 []); eauto. }
              iExists (index + 1)%nat. iExists acc. iExists peek_r. iExists ((acc_ops ++ [peek_l_ops]) ++ drop (length acc + 1) l3_ops)%list. iFrame. iSplitL "".
              { replace peek_l with peek_r. { rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. done. }
                destruct peek_l as [vl dl], peek_r as [vr dr]. unfold coq_equalOperations in Heqb. simpl in *.
                destruct (uint.nat dl =? uint.nat dr) as [ | ] eqn: H_obs; [rewrite Z.eqb_eq in H_obs | rewrite Z.eqb_neq in H_obs].
                - rewrite andb_true_r in Heqb. rewrite redefine_coq_equalSlices in Heqb. change (SessionPrelude.eqb (hsEq := SessionPrelude.hsEq_vector n) vl vr = true) in Heqb.
                  rewrite SessionPrelude.eqb_eq in Heqb; eauto. simpl in Heqb. replace dl with dr by word. f_equal.
                  unfold Operation_wf in H_wf', H_wf''. destruct H_wf' as [_ H_wf'], H_wf'' as [_ H_wf'']; simpl in *.
                  revert Heqb H_wf' H_wf''. clear. revert vr n. induction vl as [ | hd tl IH], vr as [ | hd' tl']; intros ? EXT <- LENGTH; simpl in *; try congruence. f_equal.
                  + change (SessionPrelude.eqProp hd' hd). eapply SessionPrelude.eqProp_symmetry; eauto. rewrite <- SessionPrelude.eqb_eq; trivial. eapply EXT with (i := 0%nat); eauto. word.
                  + eapply IH; eauto. intros. eapply EXT with (i := S i); eauto. word.
                - rewrite andb_false_r in Heqb. congruence.
              }
              iSplitL "H_curr".
              { replace (W64 (index + 1 + 1)%nat) with (w64_word_instance .(word.add) (W64 (index + 1)%nat) (W64 1)) by word. done. }
              iClear "H_l3_ops_suffix". iClear "H_peek_l_ops". iClear "H_acc_ops". iSplit.
              { iPureIntro. eauto. }
              iSplit.
              { assert ((take (index + 1) (fold_left coq_sortedInsert l2 [])) = take index (fold_left coq_sortedInsert l2 []) ++ [peek_l]) as LOOK.
                - rewrite <- take_drop with (l := take (index + 1) (fold_left coq_sortedInsert l2 [])) (i := index).
                  rewrite take_take. replace (index `min` (index + 1))%nat with index by word. f_equal.
                  rewrite skipn_firstn_comm. replace (index + 1 - index)%nat with 1%nat by word.
                  rewrite <- take_drop with (l := fold_left coq_sortedInsert l2 []) (i := index) in H_peek_l'.
                  rewrite lookup_app_r in H_peek_l'; cycle 1. { rewrite length_take. word. }
                  replace (index - length (take index (fold_left coq_sortedInsert l2 [])))%nat with 0%nat in H_peek_l'; cycle 1. { rewrite length_take. word. }
                  destruct (drop index (fold_left coq_sortedInsert l2 [])) as [ | hd tl] eqn: H_OBS.
                  + rewrite lookup_nil in H_peek_l'. congruence.
                  + simpl in *. replace (take 0 tl) with (@nil Operation.t) by reflexivity. congruence.
                - rewrite LOOK. rewrite fold_left_app. simpl. iPureIntro.
                  unfold loop_step at 1. rewrite <- H_loop. 
                  rewrite H_peek_r. rewrite Heqb. reflexivity.
              }
              iSplit. { iPureIntro. congruence. }
              iSplit.
              { iPureIntro. replace is_sorted with (SessionPrelude.isSorted (hsOrd := hsOrd_Operation n)) in * by reflexivity.
                rewrite -> SessionPrelude.isSorted_iff_isSorted' in H3_is_sorted; auto.
                red in H3_is_sorted |- *. clear i. intros i j i_le_j x1 x2 H_x1 H_x2.
                assert (i = length acc \/ i < length acc)%nat as i_RANGE.
                { enough (i < length (acc ++ [peek_r]))%nat as YES.
                  - rewrite length_app in YES. simpl in *. word.
                  - eapply lookup_lt_is_Some_1. exists x1. done.
                }
                assert (j = length acc \/ j < length acc)%nat as j_RANGE.
                { enough (j < length (acc ++ [peek_r]))%nat as YES.
                  - rewrite length_app in YES. simpl in *. word.
                  - eapply lookup_lt_is_Some_1. exists x2. done.
                }
                destruct i_RANGE as [EQ1 | LT1], j_RANGE as [EQ2 | LT2].
                - subst i j. rewrite -> lookup_snoc in H_x1, H_x2. right. replace x2 with peek_r by congruence. replace x1 with peek_r by congruence. rewrite SessionPrelude.eqb_eq; eauto.
                  eapply SessionPrelude.eqProp_reflexivity; eauto.
                - word.
                - subst j. rewrite -> lookup_snoc in H_x2. replace x2 with peek_r by congruence.
                  rewrite lookup_app_l in H_x1; cycle 1. { word. }
                  assert ((hsOrd_Operation n) .(SessionPrelude.ltb) x1 peek_l = true ∨ (hsEq_Operation n) .(SessionPrelude.eqb) peek_l x1 = true) as H1.
                  { eapply H3_is_sorted with (i := i) (j := length acc).
                    - word.
                    - rewrite lookup_app_l; eauto.
                    - rewrite lookup_snoc. reflexivity.
                  }
                  assert ((hsOrd_Operation n) .(SessionPrelude.ltb) peek_l peek_r = true ∨ (hsEq_Operation n) .(SessionPrelude.eqb) peek_r peek_l = true) as H2.
                  { eapply H2_is_sorted with (i := index) (j := (index + 1)%nat).
                    - word.
                    - eauto.
                    - eauto.
                  }
                  assert (Operation_wf n x1) as H.
                  { eapply Forall_lookup_1; eauto. rewrite lookup_app_l; eauto. }
                  assert (Operation_wf n peek_l) as H0.
                  { eapply Forall_lookup_1; eauto. eapply lookup_snoc. }
                  destruct H1 as [H1 | H1], H2 as [H2 | H2].
                  + left. rewrite SessionPrelude.ltb_lt in H1; trivial. rewrite SessionPrelude.ltb_lt in H2; trivial. rewrite SessionPrelude.ltb_lt; trivial. eapply SessionPrelude.ltProp_transitivity; eauto.
                  + left. rewrite SessionPrelude.ltb_lt in H1; trivial. rewrite SessionPrelude.eqb_eq in H2; trivial. rewrite SessionPrelude.ltb_lt; trivial. pose proof (SessionPrelude.ltProp_trichotomy (hsOrd := hsOrd_Operation n) x1 peek_r) as [H3 | [H3 | H3]]; trivial.
                    * contradiction (SessionPrelude.ltProp_irreflexivity (hsOrd := hsOrd_Operation n) x1 peek_l).
                      eapply SessionPrelude.eqProp_transitivity with (y := peek_r); eauto.
                    * contradiction (SessionPrelude.ltProp_irreflexivity (hsOrd := hsOrd_Operation n) peek_r peek_l).
                      eapply SessionPrelude.ltProp_transitivity with (y := x1); eauto.
                  + left. rewrite SessionPrelude.ltb_lt in H2; trivial. rewrite SessionPrelude.eqb_eq in H1; trivial. rewrite SessionPrelude.ltb_lt; trivial. pose proof (SessionPrelude.ltProp_trichotomy (hsOrd := hsOrd_Operation n) x1 peek_r) as [H3 | [H3 | H3]]; trivial.
                    * contradiction (SessionPrelude.ltProp_irreflexivity (hsOrd := hsOrd_Operation n) peek_l peek_r).
                      eapply SessionPrelude.eqProp_transitivity with (y := x1); eauto.
                    * contradiction (SessionPrelude.ltProp_irreflexivity (hsOrd := hsOrd_Operation n) peek_l x1).
                      eapply SessionPrelude.ltProp_transitivity with (y := peek_r); eauto.
                  + right. rewrite -> SessionPrelude.eqb_eq in H1, H2 |- *; trivial. eapply SessionPrelude.eqProp_transitivity with (y := peek_l); eauto.
                - eapply H3_is_sorted with (i := i) (j := j).
                  + word.
                  + rewrite lookup_app_l in H_x1; trivial. rewrite lookup_app_l; eauto.
                  + rewrite lookup_app_l in H_x2; trivial. rewrite lookup_app_l; eauto.
              }
              iSplit.
              { iPureIntro. eapply Forall_app; split; eauto. rewrite Forall_app in H_wf. tauto. }
              iSplit.
              { iPureIntro. rewrite length_app. rewrite length_app. rewrite length_drop. simpl. word. }
              { iPureIntro. simpl. word. }
          - iModIntro. iApply "HΦ". iExists (length l3_ops - 1)%nat. iExists acc. iExists peek_l. iExists l3_ops.
            iPoseProof (big_sepL2_length with "[$H_l3_ops]") as "%YES1".
            iPoseProof (own_slice_small_sz with "[$H_s3]") as "%YES2".
            assert (length l3_ops = index + 1)%nat as YES3 by word.
            iFrame. iSplitL "H_curr".
            { replace (W64 (length l3_ops - 1 + 1)%nat) with (W64 (index + 1)%nat) by word. done. }
            iSplit. { iPureIntro. rewrite YES3. replace (index + 1 - 1)%nat with index by word. done. }
            rewrite YES3. replace (index + 1 - 1)%nat with index by word. iSplit.
            { iPureIntro. done. }
            iSplit. { iPureIntro. intros _. rewrite <- YES3. rewrite <- LENGTH. apply nil_length_inv. rewrite length_drop. word. }
            iSplit. { done. }
            iSplit. { done. }
            iSplit. { word. }
            iSplit. { done. }
            word.
        }
        { destruct (fold_left SessionPrelude.sortedInsert l2 []) as [ | l3_hd l3_tl] eqn: H_l3_obs.
          { simpl in *. word. }
          subst l3. rename H_l3_obs into H_l3.
          iExists 0%nat. iExists []%list. iExists l3_hd. iExists l3_ops. iFrame. iSplitL "H_s3".
          { iApply own_slice_to_small; eauto. }
          simpl in *. rewrite H_l3. simpl. replace (drop 0 l3_tl) with l3_tl by reflexivity. iFrame.
          iClear "H1_s1". iClear "H_s2". iSplit. { iPureIntro. done. }
          iSplit. { iPureIntro. done. }
          iSplit. { iPureIntro. done. }
          iSplit.
          { iPureIntro. red. clear i. intros. rewrite -> lookup_cons in H0, H1. destruct i as [ | i'], j as [ | j'].
            - right. replace o2 with o1 by congruence. change (SessionPrelude.eqb (hsEq := hsEq_Operation n) o1 o1 = true). rewrite SessionPrelude.eqb_eq.
              + eapply SessionPrelude.eqProp_reflexivity; try done. eapply Forall_lookup_1 with (l := fold_left SessionPrelude.sortedInsert l2 []) (i := 0%nat); eauto.
                rewrite -> H_l3. exact H0.
              + eapply Forall_lookup_1 with (l := fold_left SessionPrelude.sortedInsert l2 []) (i := 0%nat); eauto.
                rewrite -> H_l3. exact H0.
              + eapply Forall_lookup_1 with (l := fold_left SessionPrelude.sortedInsert l2 []) (i := 0%nat); eauto.
                rewrite -> H_l3. exact H0.
            - rewrite lookup_nil in H1. congruence.
            - rewrite lookup_nil in H0. congruence.
            - rewrite lookup_nil in H1. congruence.
          }
          iSplit. { iPureIntro. econstructor; eauto. eapply Forall_lookup_1 with (l := fold_left SessionPrelude.sortedInsert l2 []) (i := 0%nat); eauto. rewrite -> H_l3. reflexivity. }
          rewrite H3_length. rewrite YES1. rewrite -> redefine_coq_sortedInsert with (len := n). rewrite -> H_l3. simpl. word.
        }
        { clear l3_ops YES1. iIntros "(%index & %acc & %peek_l & %l3_ops & H_s3 & H_l3_ops & H_i & H_l & H_intermediate & H_prev & H_curr & %H)".
          wp_pures. wp_apply wp_NewSlice. iIntros "%s4 H_s4". wp_apply wp_ref_to; eauto. iIntros "%output H_output". wp_pures. wp_store. wp_load. wp_store. wp_pures.
          replace (replicate (uint.nat (W64 0)) operation_into_val .(IntoVal_def (Slice.t * w64))) with (@nil (Slice.t * w64)) by reflexivity. destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8). specialize (H3 eq_refl).
          apply f_equal with (f := length) in H3. simpl in *. rewrite length_drop in H3. assert (length l3 = index + 1)%nat as YES by word.
          wp_apply (wp_forBreak_cond
            ( λ continue, ∃ s4 : Slice.t, ∃ l4_ops : list (Slice.t * w64),
              own_slice_small s3 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l3_ops ∗
              own_slice s4 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l4_ops ∗
              intermediate ↦[slice.T (slice.T uint64T * (uint64T * unitT)%ht)] s3 ∗
              output ↦[slice.T (slice.T uint64T * (uint64T * unitT)%ht)] s4 ∗
              i ↦[uint64T] #(W64 (length l4_ops)) ∗
              l ↦[uint64T] #(W64 (length acc + 1)%nat) ∗
              prev ↦[uint64T] #(W64 (length acc + 1)%nat) ∗
              ([∗ list] opv;o ∈ l3_ops;(acc ++ [peek_l] ++ drop (length acc + 1) l3), is_operation opv o n) ∗
              ([∗ list] opv;o ∈ l4_ops;take (length l4_ops) (acc ++ [peek_l] ++ drop (length acc + 1) l3), is_operation opv o n) ∗
              ⌜(length l4_ops <= (length acc + 1))%nat⌝ ∗
              ⌜continue = false -> length l4_ops = (length acc + 1)%nat⌝ 
            )%I
          with "[] [H_s3 H_s4 H_l3_ops H_prev H_i H_l H_intermediate H_output]").
          { clear Φ s4. iIntros "%Φ". iModIntro. iIntros "(%s4 & %l4_ops & H_s3 & H_s4 & H_intermediate & H_output & H_i & H_l & H_prev & H_l3 & H_l4 & %H_bound & %H_continue) HΦ".
            iPoseProof (own_slice_small_sz with "[$H_s3]") as "%claim1".
            wp_pures. wp_load. wp_load. wp_if_destruct.
            - iAssert ⌜is_Some (l3_ops !! uint.nat (W64 (length l4_ops)))⌝%I with "[H_l3]" as "[%x %H_x]".
              { iPoseProof (big_sepL2_length with "[$H_l3]") as "%YES1". iPureIntro. eapply lookup_lt_is_Some_2. word. }
              wp_pures. wp_load. wp_load. wp_apply (wp_SliceGet with "[$H_s3]"); eauto. iIntros "H_s3". wp_load. wp_apply (wp_SliceAppend with "[$H_s4]").
              iIntros "%s5 H_s5". wp_store. wp_load. wp_store. iModIntro. iApply "HΦ".
              iPoseProof (pers_big_sepL2_is_operation with "[$H_l3]") as "#H_l3_pers".
              iPoseProof (pers_big_sepL2_is_operation with "[$H_l4]") as "#H_l4_pers".
              iExists s5. iExists (l4_ops ++ [x])%list. iFrame.
              iPoseProof (big_sepL2_length with "[$H_l3_pers]") as "%YES1".
              iPoseProof (big_sepL2_length with "[$H_l4_pers]") as "%YES2".
              iSplitL "H_i". { rewrite length_app; simpl. replace (W64 (length l4_ops + 1)%nat) with (w64_word_instance .(word.add) (W64 (length l4_ops)) (W64 1)); eauto. word. }
              iSplitL "".
              { iApply big_sepL2_is_operation_intro.
                - rewrite length_take. rewrite <- YES1. rewrite length_app. simpl.
                  do 2 rewrite length_app in YES1. rewrite length_take in YES2. do 2 rewrite length_app in YES2. simpl in *.
                  enough ((length l4_ops + 1) <= length l3_ops)%nat by word.
                  rewrite <- H6. rewrite <- YES1 in YES2. rewrite <- H6 in YES2. word.
                - clear i. iIntros "%i %l_i %ops_i [%YES3 %YES4]". assert (i < length (l4_ops ++ [x]))%nat as H by now eapply lookup_lt_is_Some_1.
                  assert (i = length l4_ops \/ i < length l4_ops)%nat as [EQ | LT] by now rewrite length_app in H; simpl in H; word.
                  + subst i. iApply (big_sepL2_is_operation_elim); cycle -1.
                    * iExact "H_l3_pers".
                    * instantiate (1 := length l4_ops).
                      rewrite lookup_take in YES3; trivial.
                    * replace (length l4_ops) with (uint.nat (W64 (length l4_ops))). { rewrite lookup_snoc in YES4. congruence. }
                      rewrite length_take in YES2. rewrite <- YES1 in YES2. word.
                  + iApply (big_sepL2_is_operation_elim); cycle -1.
                    * iExact "H_l4_pers".
                    * instantiate (1 := i). rewrite lookup_take in YES3; trivial. rewrite lookup_take; trivial.
                    * rewrite lookup_app_l in YES4; trivial.
              }
              iClear "H_l4". iSplit.
              { iPureIntro. rewrite length_app. simpl. word. }
              { iPureIntro. congruence. }
            - iApply "HΦ". iExists s4. iExists l4_ops. iModIntro.
              iPoseProof (big_sepL2_length with "[$H_l4]") as "%claim3".
              iPoseProof (big_sepL2_length with "[$H_l3]") as "%claim4".
              iFrame. iPureIntro. split. { word. } intros _. rewrite length_take in claim3. rewrite <- claim4 in claim3.
              do 2 rewrite length_app in claim4. simpl in *. rewrite length_drop in claim4. word.
          }
          { iExists s4. iExists []%list. iFrame. simpl. iSplit. { done. } iPureIntro. split. { word. } { congruence. } }
          { clear s4. iIntros "(%s4 & %l4_ops & H_s3 & H_s4 & H_intermediate & H_output & H_i & H_l & H_prev & H_l3_ops & H_l4_ops & %H_bound & %H_continue)".
            specialize (H_continue eq_refl). wp_pures. wp_load. iModIntro. iApply "HΦ".
            assert (l3 = take index l3 ++ [peek_l]) as claim4.
            { rewrite <- take_drop with (l := l3) (i := index) at 1. f_equal.
              destruct (drop index l3) as [ | hd tl] eqn: H_OBS.
              - apply f_equal with (f := length) in H_OBS. simpl in *. rewrite length_drop in H_OBS. word.
              - f_equal.
                + rewrite <- take_drop with (l := l3) (i := index) in H1. rewrite lookup_app_r in H1.
                  * rewrite length_take in H1. replace (index - index `min` length l3)%nat with 0%nat in H1 by word. rewrite H_OBS in H1. simpl in *. congruence.
                  * rewrite length_take. word.
                + apply f_equal with (f := length) in H_OBS. simpl in *. rewrite length_drop in H_OBS. eapply nil_length_inv. word.
            }
            assert (fold_left coq_sortedInsert l2 [] !! (index + 1)%nat = None) as claim5.
            { eapply lookup_ge_None. rewrite -> redefine_coq_sortedInsert with (len := n). rewrite H3_length. subst l3. rewrite <- redefine_coq_sortedInsert with (len := n) in *. word. }
            iExists (coq_mergeOperations [] l2). iSplitL "H_s4 H_l4_ops".
            - iPoseProof (pers_big_sepL2_is_operation with "[$H_l4_ops]") as "#H_l4_ops_pers".
              subst l3. iExists l4_ops. iFrame. iApply big_sepL2_is_operation_intro.
              + unfold coq_mergeOperations. replace (fun acc => fun element => coq_sortedInsert acc element) with coq_sortedInsert by reflexivity.
                fold loop_step. fold loop_init. rewrite claim4. rewrite fold_left_app. simpl. rewrite <- H2. simpl.
                rewrite claim5. simpl. rewrite length_app. done.
              + clear i. iIntros "%i %l_i %ops_i [%H_l_i %H_ops_i]".
                iApply big_sepL2_is_operation_elim; cycle -1.
                * iExact "H_l4_ops".
                * instantiate (1 := i).
                  assert ((acc ++ [peek_l]) !! i = Some l_i) as claim6.
                  { unfold coq_mergeOperations in H_l_i. replace (fun acc => fun element => coq_sortedInsert acc element) with coq_sortedInsert in H_l_i by reflexivity.
                    fold loop_step in H_l_i. fold loop_init in H_l_i. rewrite claim4 in H_l_i. rewrite fold_left_app in H_l_i. simpl in *.
                    rewrite <- H2 in H_l_i. simpl in H_l_i. rewrite claim5 in H_l_i. simpl in *. done.
                  }
                  rewrite lookup_take. { rewrite app_assoc. rewrite lookup_app_l; eauto. eapply lookup_lt_is_Some_1. eauto. }
                  eapply lookup_lt_is_Some_1. eauto.
                * eauto.
            - iPureIntro. split; trivial. unfold coq_mergeOperations. replace (fun acc => fun element => coq_sortedInsert acc element) with coq_sortedInsert by reflexivity.
              subst l3. fold loop_step. fold loop_init. rewrite claim4. rewrite fold_left_app. simpl in *.
              rewrite <- H2. simpl. rewrite claim5. simpl in *. done.
          }
        }
    - rewrite bool_decide_eq_false in decide_s1. assert (s1 .(Slice.sz) ≠ (W64 0)) as H_NE_NIL by congruence. clear decide_s1. iPoseProof (big_sepL2_length with "[$H_l1_ops]") as "%H2_NE_NIL".
      iPoseProof (big_sepL2_length with "[$H_l2_ops]") as "%H_l2_length". iPoseProof (own_slice_sz with "[$H_s2]") as "%H_s2_sz". simpl in *.
      wp_apply wp_NewSlice. iIntros "%s3 H_s3". replace (replicate (uint.nat (W64 0)) operation_into_val .(IntoVal_def (Slice.t * w64))) with (@nil (Slice.t * w64)) by reflexivity.
      iDestruct "H_s1" as "[H1_s1 H2_s1]". wp_apply (wp_SliceAppendSlice with "[$H_s3 $H1_s1]"); auto. simpl. iIntros "%s4 [H_s4 H1_s1]".
      wp_pures. wp_apply wp_ref_to; auto. iIntros "%intermediate H_intermediate". wp_pures. wp_apply wp_ref_to; auto.
      wp_pures. iIntros "%i H_i". wp_pures. wp_apply wp_slice_len. wp_apply wp_ref_to; auto. iIntros "%l H_l". wp_pures.
      wp_apply (wp_forBreak_cond
        ( λ continue, ∃ s4 : Slice.t, ∃ l3_ops : list (Slice.t * w64), ∃ l2_prevs : list Operation.t, ∃ l2_nexts : list Operation.t,
          "H_s2" ∷ own_slice_small s2 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l2_ops ∗
          "H_s4" ∷ own_slice s4 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l3_ops ∗
          ([∗ list] opv;o ∈ drop (length l2_prevs) l2_ops;l2_nexts, is_operation opv o n) ∗
          ([∗ list] opv;o ∈ l3_ops;fold_left coq_sortedInsert l2_prevs l1, is_operation opv o n) ∗
          ⌜l2 = l2_prevs ++ l2_nexts⌝ ∗
          i ↦[uint64T] #(W64 (length l2_prevs)) ∗
          l ↦[uint64T] #s2 .(Slice.sz) ∗
          intermediate ↦[slice.T (slice.T uint64T * (uint64T * unitT)%ht)] s4 ∗
          ⌜is_sorted (fold_left coq_sortedInsert l2_prevs l1)⌝ ∗
          ⌜Forall (Operation_wf n) (fold_left SessionPrelude.sortedInsert l2_prevs l1)⌝ ∗
          ⌜length (fold_left SessionPrelude.sortedInsert l2_prevs l1) = (length l1 + length l2_prevs)%nat⌝ ∗
          ⌜continue = false -> l2_nexts = []⌝
        )%I
      with "[] [H1_s1 H_s2 H_s4 H_l1_ops H_l2_ops H_intermediate H_i H_l]").
      { clear Φ s4. iIntros "%Φ". iModIntro. iIntros "(%s4 & %l3_ops & %l2_prevs & %l2_nexts & H_s2 & H_s4 & H_l2_ops & H_l3_ops & %l2_eq & H_i & H_l & H_intermediate & %H_is_sorted & %H_wf & %H_length & %H_continue) HΦ".
        wp_load. wp_load. wp_if_destruct.
        - wp_pures. wp_load. destruct l2_nexts as [ | l2_cur l2_nexts].
          + rewrite app_nil_r in l2_eq. subst l2_prevs. word.
          + iNamed "H_s2". iNamed "H_s4". iPoseProof (big_sepL2_cons_inv_r with "[$H_l2_ops]") as "(%l2_ops_cur & %l2_ops_nexts & %H_OBS & H_l2_cur & H_l2_nexts)".
            pose proof (take_drop (length l2_prevs) l2_ops) as H2_l2_ops.
            rewrite H_OBS in H2_l2_ops.
            iAssert ⌜Operation_wf n l2_cur⌝%I as "%H2_wf".
            { iDestruct "H_l2_cur" as "(%H1 & %H2 & H3)". iPureIntro. split.
              - eapply SessionPrelude.Forall_True.
              - done.
            }
            iAssert ⌜Forall (Operation_wf n) l2_nexts⌝%I as "%H1_wf".
            { iApply Forall_Operation_wf; done. }
            wp_apply (wp_SliceGet with "[H_s2]").
            { iSplitL "H_s2".
              - iExact "H_s2".
              - rewrite l2_eq in H_l2_length. rewrite length_app in H_l2_length. simpl in *.
                iPureIntro. replace (uint.nat (W64 (length l2_prevs))) with (length l2_prevs) by word.
                rewrite <- H2_l2_ops. eapply list_lookup_middle. rewrite length_take. word.
            }
            iIntros "H_s2". wp_load. wp_apply (wp_sortedInsert with "[$H_s4 $H_l2_cur $H_l3_ops]"); auto.
            iIntros "%ns (%nxs & H_ns & %H_nxs)". wp_store. wp_load. wp_store. iModIntro. iApply "HΦ".
            iDestruct "H_ns" as "(%ns_ops & H_ns & H_ns_ops)". subst nxs.
            iExists ns. iExists ns_ops. iExists (l2_prevs ++ [l2_cur])%list. iExists l2_nexts. iFrame.
            iSplitL "H_l2_nexts". { rewrite length_app. simpl in *. rewrite <- drop_drop. rewrite H_OBS. simpl. done. }
            iSplitL "H_ns_ops". { rewrite fold_left_app. simpl in *. done. }
            iSplitL "". { rewrite <- app_assoc. done. }
            iSplitL "H_i". { rewrite length_app. simpl. rewrite l2_eq in H_l2_length. rewrite length_app in H_l2_length. simpl in *. replace ((w64_word_instance .(word.add) (W64 (length l2_prevs)) (W64 1))) with (W64 (length l2_prevs + 1)%nat) by word. done. }
            iSplit. { rewrite fold_left_app. simpl in *. iPureIntro. replace is_sorted with (SessionPrelude.isSorted (hsOrd := hsOrd_Operation n)) by reflexivity. rewrite -> redefine_coq_sortedInsert with (len := n). eapply SessionPrelude.sortedInsert_isSorted; eauto. }
            pose proof (SessionPrelude.sortedInsert_spec (hsOrd := hsOrd_Operation n) _ _ H_wf H2_wf H_is_sorted) as (prefix & suffix & H1 & H2 & H3 & H4 & YES).
            iSplit. { rewrite fold_left_app. simpl in *. iPureIntro. done. }
            iSplit. { rewrite fold_left_app. simpl in *. iPureIntro. rewrite -> H2. rewrite length_app. simpl. apply f_equal with (f := length) in H1. rewrite length_app in H1. rewrite length_app. simpl. rewrite H1 in H_length. word. }
            { iPureIntro. congruence. }
        - iNamed "H_s2". iNamed "H_s4".
          iAssert ⌜l2_nexts = []⌝%I as "%l2_nexts_nil".
          { rewrite l2_eq in H_l2_length. rewrite length_app in H_l2_length.
            assert (uint.Z (W64 (length l2_prevs)) = uint.Z s2 .(Slice.sz)) as YES1 by word.
            assert (length l2_nexts = 0%nat) as YES2 by word.
            iPureIntro. destruct l2_nexts as [ | ? ?]; [done | simpl in *; word].
          }
          subst l2_nexts. rewrite app_nil_r in l2_eq. subst l2.
          iApply "HΦ". iModIntro. iExists s4. iExists l3_ops. iExists l2_prevs. iExists []. iFrame. rewrite app_nil_r. done.
      }
      { iExists s4. iExists l1_ops. iExists []. iExists l2. simpl in *. iPoseProof (pers_big_sepL2_is_operation with "[$H_l1_ops]") as "#H_l1_ops_pers". iFrame. iSplitL "H_s2".
        - iApply own_slice_to_small; done.
        - iSplit. { done. } iSplit. { done. } iSplit. { iApply Forall_Operation_wf. done. } iSplit. { done. } { iPureIntro. congruence. }
      }
      clear s4 s3. iIntros "(%s4 & %l3_ops & %l2_prevs & %l2_nexts & H_s2 & H_s4 & H_l2_ops_nexts & H_l3_ops & %H_l2_obs & H_i & H_l & H_intermediate & %H2_is_sorted & %H2_wf & %H3_length & %H_continue)".
      specialize (H_continue eq_refl). subst l2_nexts. rewrite app_nil_r in H_l2_obs. subst l2_prevs.
      iNamed "H_s2". iNamed "H_s4". wp_pures. wp_apply wp_ref_to; eauto. iIntros "%prev H_prev". wp_pures. wp_apply wp_ref_to; auto. iIntros "%curr H_curr". wp_pures.
      replace SessionPrelude.sortedInsert with coq_sortedInsert in H2_wf by reflexivity. remember (fold_left coq_sortedInsert l2 l1) as l3 eqn: H_l3 in *.
      set (loop_step := λ (acc: nat * list Operation.t) (element : Operation.t),
        let (index, acc) := acc in
          match (l3 !! (index + 1)%nat) with
          | Some v => if (coq_equalOperations element v) then ((index + 1)%nat, acc) else ((index + 1)%nat, acc ++ [element])
          | None => ((index + 1)%nat, acc ++ [element])
          end
      ).
      set (loop_init := (0%nat, @nil Operation.t)).
      iRename "H_s4" into "H_s3". rename s4 into s3.
      iPoseProof (big_sepL2_length with "[$H_l3_ops]") as "%YES1".
      wp_apply (wp_forBreak_cond
        ( λ continue, ∃ index : nat, ∃ acc : list Operation.t, ∃ peek_l : Operation.t, ∃ l3_ops : list (Slice.t * w64),
          own_slice_small s3 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l3_ops ∗
          ([∗ list] opv;o ∈ l3_ops;acc ++ [peek_l] ++ drop (length acc + 1)%nat l3, is_operation opv o n) ∗
          i ↦[uint64T] #(W64 (length l2)) ∗
          l ↦[uint64T] #s2 .(Slice.sz) ∗
          intermediate ↦[slice.T (slice.T uint64T * (uint64T * unitT)%ht)] s3 ∗
          prev ↦[uint64T] #(length acc + 1)%nat ∗
          curr ↦[uint64T] #(index + 1)%nat ∗
          ⌜l3 !! index = Some peek_l⌝ ∗
          ⌜(index, acc) = fold_left loop_step (take index l3) loop_init⌝ ∗
          ⌜continue = false -> drop (index + 1)%nat l3 = []⌝ ∗
          ⌜is_sorted (acc ++ [peek_l])⌝ ∗
          ⌜Forall (Operation_wf n) (acc ++ [peek_l])⌝ ∗
          ⌜length l3 = length l3_ops⌝ ∗
          ⌜(length acc <= index)%nat⌝ ∗
          ⌜(index + 1 <= length l3)%nat⌝
        )%I
      with "[] [H_l3_ops H_s2 H_s3 H_intermediate H_prev H_curr H_i H_l]").
      { clear Φ l3_ops YES1. iIntros "%Φ". iModIntro. iIntros "(%index & %acc & %peek_l & %l3_ops & H_s3 & H_l3_ops & H_i & H_l & H_intermediate & H_prev & H_curr & %H) HΦ".
        destruct H as (H_peek_l' & H_loop & H_continue & H3_is_sorted & H_wf & LENGTH & H1_index & H2_index).
        wp_pures. wp_load. wp_load. wp_apply (wp_slice_len). wp_if_destruct.
        - iPoseProof (pers_big_sepL2_is_operation with "[$H_l3_ops]") as "#YES".
          iPoseProof (big_sepL2_length with "[$H_l3_ops]") as "%H_l3_ops_len".
          iPoseProof (own_slice_small_sz with "[$H_s3]") as "%H_s3_sz".
          rewrite app_assoc. rewrite <- take_drop with (l := l3_ops) (i := (length acc + 1)%nat).
          iPoseProof (big_sepL2_app_equiv with "[$H_l3_ops]") as "[H_l3_ops_prefix H_l3_ops_suffix]".
          { rewrite length_app. simpl. rewrite length_take. rewrite H_l3_ops_len. repeat rewrite length_app. simpl in *. word. }
          assert (index + 1 < uint.nat s3 .(Slice.sz))%nat as NE_NIL.
          { assert (uint.nat (W64 (index + 1)%nat) < uint.nat s3 .(Slice.sz))%nat as YES1 by word.
            assert (index < length l3)%nat as YES2 by now eapply lookup_lt_is_Some_1.
            word.
          }
          clear Heqb.
          assert (is_Some (l3 !! (index + 1)%nat)) as [peek_r H_peek_r].
          { eapply lookup_lt_is_Some_2. word. }
          induction (take (length acc + 1) l3_ops) as [ | peek_l_ops acc_ops _] eqn: H_l3_ops_prefix_obs using rev_ind.
          { pose proof (f_equal length H_l3_ops_prefix_obs) as H_contra. simpl in *.
            rewrite length_take in H_contra. rewrite H_l3_ops_len in H_contra. rewrite length_app in H_contra. simpl in *. word.
          }
          iAssert (([∗ list] y1;y2 ∈ acc_ops;acc, is_operation y1 y2 n) ∗ (is_operation peek_l_ops peek_l n))%I with "[H_l3_ops_prefix]" as "[H_peek_l_ops H_acc_ops]".
          { iApply (big_sepL2_snoc with "H_l3_ops_prefix"). }
          iPoseProof (big_sepL2_length with "[$H_peek_l_ops]") as "%H_acc_length".
          iAssert ⌜is_Some (((acc_ops ++ [peek_l_ops]) ++ drop (length acc + 1) l3_ops) !! uint.nat (W64 (index + 1)%nat))⌝%I as "[%peek_r_ops %H_peek_r_ops]".
          { iPureIntro. eapply lookup_lt_is_Some_2. rewrite <- H_l3_ops_prefix_obs. rewrite take_drop. word. }
          iAssert ⌜is_Some (((acc_ops ++ [peek_l_ops]) ++ drop (length acc + 1) l3_ops) !! uint.nat (w64_word_instance .(word.sub) (W64 (index + 1)%nat) (W64 1)))⌝%I as "[%peek_l_ops' %H_peek_l_ops']".
          { iPureIntro. eapply lookup_lt_is_Some_2. rewrite <- H_l3_ops_prefix_obs. rewrite take_drop. word. }
          wp_pures. wp_load. wp_load. wp_apply (wp_SliceGet with "[$H_s3]"); auto. iIntros "H_s3".
          wp_pures. wp_load. wp_load. wp_apply (wp_SliceGet with "[$H_s3]"); auto. iIntros "H_s3".
          rewrite <- H_l3_ops_prefix_obs in H_peek_l_ops', H_peek_r_ops. rewrite take_drop in H_peek_l_ops', H_peek_r_ops.
          replace (uint.nat (W64 (index + 1)%nat)) with (index + 1)%nat in H_peek_r_ops by word.
          replace (uint.nat (w64_word_instance .(word.sub) (W64 (index + 1)%nat) (W64 1))) with index in H_peek_l_ops' by word.
          simpl. wp_apply (wp_equalOperations with "[]").
          { assert (length acc <= index)%nat as YES1 by word. iSplitL.
            - iApply big_sepL2_is_operation_elim; cycle 1.
              + exact H_peek_l_ops'.
              + rewrite <- H_l3_ops_prefix_obs. rewrite take_drop. iExact "YES".
              + instantiate (1 := peek_l).
                rewrite <- app_assoc. rewrite -> lookup_app_r; auto.
                replace (length acc) with (length (take (length acc) l3)); cycle 1.
                { rewrite length_take. word. }
                erewrite <- lookup_app_r; cycle 1.
                { rewrite length_take. word. }
                assert (length acc < index \/ length acc = index)%nat as [H1 | H1] by word.
                * rewrite lookup_app_r; cycle 1.
                  { rewrite length_take. word. }
                  rewrite lookup_app_r; cycle 1.
                  { rewrite length_take. simpl. word. }
                  rewrite <- take_drop with (l := l3) (i := (length (take (length acc) l3) + 1)%nat) in H_peek_l'.
                  rewrite lookup_app_r in H_peek_l'; cycle 1.
                  { do 2 rewrite length_take. word. }
                  simpl in *. replace (index - length (take (length acc) l3) - 1)%nat with (index - length (take (length (take (length acc) l3) + 1) l3))%nat; eauto.
                  { rewrite length_take. word. }
                * rewrite lookup_app_r; cycle 1.
                  { rewrite length_take. word. }
                  replace (index - length (take (length acc) l3))%nat with 0%nat; eauto.
                  { rewrite length_take; word. }
            - iApply big_sepL2_is_operation_elim; cycle 1.
              + exact H_peek_r_ops.
              + rewrite <- H_l3_ops_prefix_obs. rewrite take_drop. iExact "YES".
              + instantiate (1 := peek_r).
                rewrite lookup_app_r; cycle 1.
                { rewrite length_app. simpl. word. }
                rewrite <- take_drop with (l := l3) (i := length (acc ++ [peek_l])) in H_peek_r.
                rewrite lookup_app_r in H_peek_r; cycle 1.
                { rewrite length_take. rewrite length_app. simpl. word. }
                rewrite length_app in H_peek_r. simpl in *.
                replace (index + 1 - length (acc ++ [peek_l]))%nat with (index + 1 - length (take (length acc + 1) l3))%nat; eauto.
                { rewrite length_take. rewrite length_app. simpl in *. word. }
          }
          iIntros "%r %Hr". wp_if_destruct.
          + wp_load. wp_load. wp_apply (wp_SliceGet with "[$H_s3]").
            { iPureIntro. rewrite <- H_l3_ops_prefix_obs. rewrite take_drop. replace (uint.nat (W64 (index + 1)%nat)) with (index + 1)%nat by word. exact H_peek_r_ops. }
            iIntros "H_s3". wp_load. wp_load. wp_apply (wp_SliceSet with "[$H_s3]").
            { iPureIntro. replace (uint.nat (W64 (length acc + 1)%nat)) with (length (acc_ops ++ [peek_l_ops])).
              - rewrite lookup_app_r.
                + replace (length (acc_ops ++ [peek_l_ops]) - length (acc_ops ++ [peek_l_ops]))%nat with 0%nat by word.
                  eapply lookup_lt_is_Some_2. rewrite length_drop. word.
                + word.
              - rewrite length_app. simpl. word.
            }
            iIntros "H_s3". wp_pures. wp_load. wp_store. wp_pures. wp_load. wp_store. iModIntro. iApply "HΦ".
            iExists (index + 1)%nat. iExists (acc ++ [peek_l])%list. iExists peek_r. iExists ((<[uint.nat (W64 (length acc + 1)%nat):=peek_r_ops]> ((acc_ops ++ [peek_l_ops]) ++ drop (length acc + 1) l3_ops)))%list. iFrame.
            iSplitL "".
            { iApply big_sepL2_is_operation_intro.
              - rewrite length_insert. repeat rewrite length_app. simpl in *.
                rewrite H_acc_length. do 2 rewrite length_drop. rewrite LENGTH. word.
              - clear i. iIntros "%i %l_i %ops_i [%H1 %H2]".
                assert (i = uint.nat (W64 (length acc + 1)%nat) \/ i ≠ uint.nat (W64 (length acc + 1)%nat)) as [EQ | NE] by word.
                + iApply big_sepL2_is_operation_elim; cycle -1.
                  * iExact "YES".
                  * instantiate (1 := (index + 1)%nat). subst i.
                    rewrite lookup_app_r; cycle 1.
                    { rewrite length_app. simpl in *. word. }
                    rewrite length_app. simpl in *.
                    rewrite lookup_app_r in H1; cycle 1.
                    { rewrite length_app. simpl in *. word. }
                    rewrite length_app in H1. simpl in *.
                    rewrite lookup_cons in H1. destruct (uint.nat (W64 (length acc + 1)%nat) - (length acc + 1))%nat as [ | i] eqn: H_i.
                    { simpl. rewrite <- H1. rewrite <- take_drop with (l := fold_left coq_sortedInsert l2 l1) (i := (length acc + 1)%nat) in H_peek_r. rewrite lookup_app_r in H_peek_r.
                      - rewrite length_take in H_peek_r. replace (index + 1 - (length acc + 1) `min` length (fold_left coq_sortedInsert l2 l1))%nat with (index + 1 - (length acc + 1))%nat in H_peek_r; eauto. word.
                      - rewrite length_take. word.
                    }
                    { simpl in *. word. }
                  * subst i. rewrite -> list_lookup_insert in H2.
                    { rewrite <- H2. rewrite <- take_drop with (l := l3_ops) (i := (length acc + 1)%nat) in H_peek_r_ops. rewrite lookup_app_r in H_peek_r_ops.
                      - rewrite lookup_app_r.
                        + rewrite length_app. simpl in *. rewrite length_take in H_peek_r_ops.
                          replace (index + 1 - (length acc_ops + 1))%nat with (index + 1 - (length acc + 1) `min` length l3_ops)%nat; eauto. word.
                        + rewrite length_app. simpl. word.
                      - rewrite length_take. word.
                    }
                    { rewrite length_app. rewrite length_drop. rewrite length_app. simpl. word. }
                + iApply big_sepL2_is_operation_elim; cycle -1.
                  * iExact "YES".
                  * instantiate (1 := i). assert (i < uint.nat (W64 (length acc + 1)%nat) \/ i > uint.nat (W64 (length acc + 1)%nat))%nat as [LT | GT] by word.
                    { rewrite lookup_app_l.
                      - rewrite lookup_app_l in H1; eauto. rewrite length_app; simpl; word.
                      - rewrite length_app; simpl; word.
                    }
                    { rewrite lookup_app_r; cycle 1. { rewrite length_app. simpl. word. }
                      rewrite lookup_app_r in H1; cycle 1. { rewrite length_app. simpl. word. } rewrite lookup_cons in H1.
                      destruct (i - length (acc ++ [peek_l]))%nat as [ | i'] eqn: H_i'.
                      - rewrite length_app in H_i'. simpl in *; word.
                      - rewrite length_app in H1. simpl in *. rewrite <- drop_drop in H1.
                        rewrite lookup_drop in H1. replace (S i') with (1 + i')%nat by word; eauto.
                    }
                  * rewrite list_lookup_insert_ne in H2; cycle 1. { word. } eauto.
            }
            iSplitL "H_prev".
            { replace (W64 (length (acc ++ [peek_l]) + 1)%nat) with (w64_word_instance .(word.add) (W64 (length acc + 1)%nat) (W64 1)). { done. }
              rewrite length_app. simpl in *. word.
            }
            iSplitL "H_curr".
            { replace (W64 (index + 1 + 1)%nat) with (w64_word_instance .(word.add) (W64 (index + 1)%nat) (W64 1)). { done. }
              word.
            }
            iClear "H_l3_ops_suffix". iClear "H_peek_l_ops". iClear "H_acc_ops". iSplit.
            { iPureIntro. eauto. }
            iSplit.
            { assert ((take (index + 1) (fold_left coq_sortedInsert l2 l1)) = take index (fold_left coq_sortedInsert l2 l1) ++ [peek_l]) as LOOK.
              - rewrite <- take_drop with (l := take (index + 1) (fold_left coq_sortedInsert l2 l1)) (i := index).
                rewrite take_take. replace (index `min` (index + 1))%nat with index by word. f_equal.
                rewrite skipn_firstn_comm. replace (index + 1 - index)%nat with 1%nat by word.
                rewrite <- take_drop with (l := fold_left coq_sortedInsert l2 l1) (i := index) in H_peek_l'.
                rewrite lookup_app_r in H_peek_l'; cycle 1. { rewrite length_take. word. }
                replace (index - length (take index (fold_left coq_sortedInsert l2 l1)))%nat with 0%nat in H_peek_l'; cycle 1. { rewrite length_take. word. }
                destruct (drop index (fold_left coq_sortedInsert l2 l1)) as [ | hd tl] eqn: H_OBS.
                + rewrite lookup_nil in H_peek_l'. congruence.
                + simpl in *. replace (take 0 tl) with (@nil Operation.t) by reflexivity. congruence.
              - rewrite LOOK. rewrite fold_left_app. simpl. iPureIntro.
                unfold loop_step at 1. rewrite <- H_loop. 
                rewrite H_peek_r. rewrite Heqb. reflexivity.
            }
            iSplit.
            { iPureIntro. congruence. }
            assert (Operation_wf n peek_r) as H_wf'.
            { eapply Forall_lookup_1 with (l := fold_left coq_sortedInsert l2 l1); eauto. }
            iSplit.
            { iPureIntro. replace is_sorted with (SessionPrelude.isSorted (hsOrd := hsOrd_Operation n)) in * by reflexivity.
              rewrite -> SessionPrelude.isSorted_iff_isSorted' in H3_is_sorted; auto.
              red in H3_is_sorted |- *. clear i. intros i j i_le_j x1 x2 H_x1 H_x2.
              assert (i = length (acc ++ [peek_l]) \/ i < length (acc ++ [peek_l]))%nat as i_RANGE.
              { enough (i < length ((acc ++ [peek_l]) ++ [peek_r]))%nat as YES.
                - rewrite length_app in YES. simpl in *. word.
                - eapply lookup_lt_is_Some_1. exists x1. done.
              }
              assert (j = length (acc ++ [peek_l]) \/ j < length (acc ++ [peek_l]))%nat as j_RANGE.
              { enough (j < length ((acc ++ [peek_l]) ++ [peek_r]))%nat as YES.
                - rewrite length_app in YES. simpl in *. word.
                - eapply lookup_lt_is_Some_1. exists x2. done.
              }
              destruct i_RANGE as [EQ1 | LT1], j_RANGE as [EQ2 | LT2].
              - subst i j. rewrite -> lookup_snoc in H_x1, H_x2. right. replace x2 with peek_r by congruence. replace x1 with peek_r by congruence. rewrite SessionPrelude.eqb_eq; eauto.
                eapply SessionPrelude.eqProp_reflexivity; eauto.
              - word.
              - subst j. rewrite -> lookup_snoc in H_x2. replace x2 with peek_r by congruence.
                rewrite lookup_app_l in H_x1; cycle 1. { word. }
                assert ((hsOrd_Operation n) .(SessionPrelude.ltb) x1 peek_l = true ∨ (hsEq_Operation n) .(SessionPrelude.eqb) peek_l x1 = true) as H1.
                { eapply H3_is_sorted with (i := i) (j := length acc).
                  - rewrite length_app in i_le_j. simpl in *. word.
                  - eauto.
                  - rewrite lookup_snoc. reflexivity.
                }
                assert ((hsOrd_Operation n) .(SessionPrelude.ltb) peek_l peek_r = true ∨ (hsEq_Operation n) .(SessionPrelude.eqb) peek_r peek_l = true) as H2.
                { eapply H2_is_sorted with (i := index) (j := (index + 1)%nat).
                  - word.
                  - eauto.
                  - eauto.
                }
                assert (Operation_wf n x1) as H.
                { eapply Forall_lookup_1; eauto. }
                assert (Operation_wf n peek_l) as H0.
                { eapply Forall_lookup_1; eauto. eapply lookup_snoc. }
                destruct H1 as [H1 | H1], H2 as [H2 | H2].
                + left. rewrite SessionPrelude.ltb_lt in H1; trivial. rewrite SessionPrelude.ltb_lt in H2; trivial. rewrite SessionPrelude.ltb_lt; trivial. eapply SessionPrelude.ltProp_transitivity; eauto.
                + left. rewrite SessionPrelude.ltb_lt in H1; trivial. rewrite SessionPrelude.eqb_eq in H2; trivial. rewrite SessionPrelude.ltb_lt; trivial. pose proof (SessionPrelude.ltProp_trichotomy (hsOrd := hsOrd_Operation n) x1 peek_r) as [H3 | [H3 | H3]]; trivial.
                  * contradiction (SessionPrelude.ltProp_irreflexivity (hsOrd := hsOrd_Operation n) x1 peek_l).
                    eapply SessionPrelude.eqProp_transitivity with (y := peek_r); eauto.
                  * contradiction (SessionPrelude.ltProp_irreflexivity (hsOrd := hsOrd_Operation n) peek_r peek_l).
                    eapply SessionPrelude.ltProp_transitivity with (y := x1); eauto.
                + left. rewrite SessionPrelude.ltb_lt in H2; trivial. rewrite SessionPrelude.eqb_eq in H1; trivial. rewrite SessionPrelude.ltb_lt; trivial. pose proof (SessionPrelude.ltProp_trichotomy (hsOrd := hsOrd_Operation n) x1 peek_r) as [H3 | [H3 | H3]]; trivial.
                  * contradiction (SessionPrelude.ltProp_irreflexivity (hsOrd := hsOrd_Operation n) peek_l peek_r).
                    eapply SessionPrelude.eqProp_transitivity with (y := x1); eauto.
                  * contradiction (SessionPrelude.ltProp_irreflexivity (hsOrd := hsOrd_Operation n) peek_l x1).
                    eapply SessionPrelude.ltProp_transitivity with (y := peek_r); eauto.
                + right. rewrite -> SessionPrelude.eqb_eq in H1, H2 |- *; trivial. eapply SessionPrelude.eqProp_transitivity with (y := peek_l); eauto.
              - eapply H3_is_sorted with (i := i) (j := j).
                + word.
                + rewrite lookup_app_l in H_x1; trivial.
                + rewrite lookup_app_l in H_x2; trivial.
            }
            iSplit.
            { iPureIntro. eapply Forall_app; split; trivial. econstructor; eauto. }
            iSplit.
            { iPureIntro. rewrite length_insert. rewrite length_app. rewrite length_drop. rewrite length_app. simpl. word. }
            { iPureIntro. rewrite length_app. simpl. word. }
          + wp_pures. wp_load. wp_store. iModIntro. iApply "HΦ".
            assert (Operation_wf n peek_l) as H_wf'.
            { eapply Forall_lookup_1 with (l := fold_left coq_sortedInsert l2 l1); eauto. }
            assert (Operation_wf n peek_r) as H_wf''.
            { eapply Forall_lookup_1 with (l := fold_left coq_sortedInsert l2 l1); eauto. }
            iExists (index + 1)%nat. iExists acc. iExists peek_r. iExists ((acc_ops ++ [peek_l_ops]) ++ drop (length acc + 1) l3_ops)%list. iFrame. iSplitL "".
            { replace peek_l with peek_r. { rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. done. }
              destruct peek_l as [vl dl], peek_r as [vr dr]. unfold coq_equalOperations in Heqb. simpl in *.
              destruct (uint.nat dl =? uint.nat dr) as [ | ] eqn: H_obs; [rewrite Z.eqb_eq in H_obs | rewrite Z.eqb_neq in H_obs].
              - rewrite andb_true_r in Heqb. rewrite redefine_coq_equalSlices in Heqb. change (SessionPrelude.eqb (hsEq := SessionPrelude.hsEq_vector n) vl vr = true) in Heqb.
                rewrite SessionPrelude.eqb_eq in Heqb; eauto. simpl in Heqb. replace dl with dr by word. f_equal.
                unfold Operation_wf in H_wf', H_wf''. destruct H_wf' as [_ H_wf'], H_wf'' as [_ H_wf'']; simpl in *.
                revert Heqb H_wf' H_wf''. clear. revert vr n. induction vl as [ | hd tl IH], vr as [ | hd' tl']; intros ? EXT <- LENGTH; simpl in *; try congruence. f_equal.
                + change (SessionPrelude.eqProp hd' hd). eapply SessionPrelude.eqProp_symmetry; eauto. rewrite <- SessionPrelude.eqb_eq; trivial. eapply EXT with (i := 0%nat); eauto. word.
                + eapply IH; eauto. intros. eapply EXT with (i := S i); eauto. word.
              - rewrite andb_false_r in Heqb. congruence.
            }
            iSplitL "H_curr".
            { replace (W64 (index + 1 + 1)%nat) with (w64_word_instance .(word.add) (W64 (index + 1)%nat) (W64 1)) by word. done. }
            iClear "H_l3_ops_suffix". iClear "H_peek_l_ops". iClear "H_acc_ops". iSplit.
            { iPureIntro. eauto. }
            iSplit.
            { assert ((take (index + 1) (fold_left coq_sortedInsert l2 l1)) = take index (fold_left coq_sortedInsert l2 l1) ++ [peek_l]) as LOOK.
              - rewrite <- take_drop with (l := take (index + 1) (fold_left coq_sortedInsert l2 l1)) (i := index).
                rewrite take_take. replace (index `min` (index + 1))%nat with index by word. f_equal.
                rewrite skipn_firstn_comm. replace (index + 1 - index)%nat with 1%nat by word.
                rewrite <- take_drop with (l := fold_left coq_sortedInsert l2 l1) (i := index) in H_peek_l'.
                rewrite lookup_app_r in H_peek_l'; cycle 1. { rewrite length_take. word. }
                replace (index - length (take index (fold_left coq_sortedInsert l2 l1)))%nat with 0%nat in H_peek_l'; cycle 1. { rewrite length_take. word. }
                destruct (drop index (fold_left coq_sortedInsert l2 l1)) as [ | hd tl] eqn: H_OBS.
                + rewrite lookup_nil in H_peek_l'. congruence.
                + simpl in *. replace (take 0 tl) with (@nil Operation.t) by reflexivity. congruence.
              - rewrite LOOK. rewrite fold_left_app. simpl. iPureIntro.
                unfold loop_step at 1. rewrite <- H_loop. 
                rewrite H_peek_r. rewrite Heqb. reflexivity.
            }
            iSplit. { iPureIntro. congruence. }
            iSplit.
            { iPureIntro. replace is_sorted with (SessionPrelude.isSorted (hsOrd := hsOrd_Operation n)) in * by reflexivity.
              rewrite -> SessionPrelude.isSorted_iff_isSorted' in H3_is_sorted; auto.
              red in H3_is_sorted |- *. clear i. intros i j i_le_j x1 x2 H_x1 H_x2.
              assert (i = length acc \/ i < length acc)%nat as i_RANGE.
              { enough (i < length (acc ++ [peek_r]))%nat as YES.
                - rewrite length_app in YES. simpl in *. word.
                - eapply lookup_lt_is_Some_1. exists x1. done.
              }
              assert (j = length acc \/ j < length acc)%nat as j_RANGE.
              { enough (j < length (acc ++ [peek_r]))%nat as YES.
                - rewrite length_app in YES. simpl in *. word.
                - eapply lookup_lt_is_Some_1. exists x2. done.
              }
              destruct i_RANGE as [EQ1 | LT1], j_RANGE as [EQ2 | LT2].
              - subst i j. rewrite -> lookup_snoc in H_x1, H_x2. right. replace x2 with peek_r by congruence. replace x1 with peek_r by congruence. rewrite SessionPrelude.eqb_eq; eauto.
                eapply SessionPrelude.eqProp_reflexivity; eauto.
              - word.
              - subst j. rewrite -> lookup_snoc in H_x2. replace x2 with peek_r by congruence.
                rewrite lookup_app_l in H_x1; cycle 1. { word. }
                assert ((hsOrd_Operation n) .(SessionPrelude.ltb) x1 peek_l = true ∨ (hsEq_Operation n) .(SessionPrelude.eqb) peek_l x1 = true) as H1.
                { eapply H3_is_sorted with (i := i) (j := length acc).
                  - word.
                  - rewrite lookup_app_l; eauto.
                  - rewrite lookup_snoc. reflexivity.
                }
                assert ((hsOrd_Operation n) .(SessionPrelude.ltb) peek_l peek_r = true ∨ (hsEq_Operation n) .(SessionPrelude.eqb) peek_r peek_l = true) as H2.
                { eapply H2_is_sorted with (i := index) (j := (index + 1)%nat).
                  - word.
                  - eauto.
                  - eauto.
                }
                assert (Operation_wf n x1) as H.
                { eapply Forall_lookup_1; eauto. rewrite lookup_app_l; eauto. }
                assert (Operation_wf n peek_l) as H0.
                { eapply Forall_lookup_1; eauto. eapply lookup_snoc. }
                destruct H1 as [H1 | H1], H2 as [H2 | H2].
                + left. rewrite SessionPrelude.ltb_lt in H1; trivial. rewrite SessionPrelude.ltb_lt in H2; trivial. rewrite SessionPrelude.ltb_lt; trivial. eapply SessionPrelude.ltProp_transitivity; eauto.
                + left. rewrite SessionPrelude.ltb_lt in H1; trivial. rewrite SessionPrelude.eqb_eq in H2; trivial. rewrite SessionPrelude.ltb_lt; trivial. pose proof (SessionPrelude.ltProp_trichotomy (hsOrd := hsOrd_Operation n) x1 peek_r) as [H3 | [H3 | H3]]; trivial.
                  * contradiction (SessionPrelude.ltProp_irreflexivity (hsOrd := hsOrd_Operation n) x1 peek_l).
                    eapply SessionPrelude.eqProp_transitivity with (y := peek_r); eauto.
                  * contradiction (SessionPrelude.ltProp_irreflexivity (hsOrd := hsOrd_Operation n) peek_r peek_l).
                    eapply SessionPrelude.ltProp_transitivity with (y := x1); eauto.
                + left. rewrite SessionPrelude.ltb_lt in H2; trivial. rewrite SessionPrelude.eqb_eq in H1; trivial. rewrite SessionPrelude.ltb_lt; trivial. pose proof (SessionPrelude.ltProp_trichotomy (hsOrd := hsOrd_Operation n) x1 peek_r) as [H3 | [H3 | H3]]; trivial.
                  * contradiction (SessionPrelude.ltProp_irreflexivity (hsOrd := hsOrd_Operation n) peek_l peek_r).
                    eapply SessionPrelude.eqProp_transitivity with (y := x1); eauto.
                  * contradiction (SessionPrelude.ltProp_irreflexivity (hsOrd := hsOrd_Operation n) peek_l x1).
                    eapply SessionPrelude.ltProp_transitivity with (y := peek_r); eauto.
                + right. rewrite -> SessionPrelude.eqb_eq in H1, H2 |- *; trivial. eapply SessionPrelude.eqProp_transitivity with (y := peek_l); eauto.
              - eapply H3_is_sorted with (i := i) (j := j).
                + word.
                + rewrite lookup_app_l in H_x1; trivial. rewrite lookup_app_l; eauto.
                + rewrite lookup_app_l in H_x2; trivial. rewrite lookup_app_l; eauto.
            }
            iSplit.
            { iPureIntro. eapply Forall_app; split; eauto. rewrite Forall_app in H_wf. tauto. }
            iSplit.
            { iPureIntro. rewrite length_app. rewrite length_app. rewrite length_drop. simpl. word. }
            { iPureIntro. simpl. word. }
        - iModIntro. iApply "HΦ". iExists (length l3_ops - 1)%nat. iExists acc. iExists peek_l. iExists l3_ops.
          iPoseProof (big_sepL2_length with "[$H_l3_ops]") as "%YES1".
          iPoseProof (own_slice_small_sz with "[$H_s3]") as "%YES2".
          assert (length l3_ops = index + 1)%nat as YES3 by word.
          iFrame. iSplitL "H_curr".
          { replace (W64 (length l3_ops - 1 + 1)%nat) with (W64 (index + 1)%nat) by word. done. }
          iSplit. { iPureIntro. rewrite YES3. replace (index + 1 - 1)%nat with index by word. done. }
          rewrite YES3. replace (index + 1 - 1)%nat with index by word. iSplit.
          { iPureIntro. done. }
          iSplit. { iPureIntro. intros _. rewrite <- YES3. rewrite <- LENGTH. apply nil_length_inv. rewrite length_drop. word. }
          iSplit. { done. }
          iSplit. { done. }
          iSplit. { word. }
          iSplit. { done. }
          word.
      }
      { destruct (fold_left SessionPrelude.sortedInsert l2 l1) as [ | l3_hd l3_tl] eqn: H_l3_obs.
        { simpl in *. word. }
        subst l3. rename H_l3_obs into H_l3.
        iExists 0%nat. iExists []%list. iExists l3_hd. iExists l3_ops. iFrame. iSplitL "H_s3".
        { iApply own_slice_to_small; eauto. }
        simpl in *. rewrite H_l3. simpl. replace (drop 0 l3_tl) with l3_tl by reflexivity. iFrame.
        iClear "H_s2". iSplit. { iPureIntro. done. }
        iSplit. { iPureIntro. done. }
        iSplit. { iPureIntro. done. }
        iSplit.
        { iPureIntro. red. clear i. intros. rewrite -> lookup_cons in H0, H1. destruct i as [ | i'], j as [ | j'].
          - right. replace o2 with o1 by congruence. change (SessionPrelude.eqb (hsEq := hsEq_Operation n) o1 o1 = true). rewrite SessionPrelude.eqb_eq.
            + eapply SessionPrelude.eqProp_reflexivity; try done. eapply Forall_lookup_1 with (l := fold_left SessionPrelude.sortedInsert l2 l1) (i := 0%nat); eauto.
              rewrite -> H_l3. exact H0.
            + eapply Forall_lookup_1 with (l := fold_left SessionPrelude.sortedInsert l2 l1) (i := 0%nat); eauto.
              rewrite -> H_l3. exact H0.
            + eapply Forall_lookup_1 with (l := fold_left SessionPrelude.sortedInsert l2 l1) (i := 0%nat); eauto.
              rewrite -> H_l3. exact H0.
          - rewrite lookup_nil in H1. congruence.
          - rewrite lookup_nil in H0. congruence.
          - rewrite lookup_nil in H1. congruence.
        }
        iSplit. { iPureIntro. econstructor; eauto. eapply Forall_lookup_1 with (l := fold_left SessionPrelude.sortedInsert l2 l1) (i := 0%nat); eauto. rewrite -> H_l3. reflexivity. }
        rewrite H3_length. rewrite YES1. rewrite -> redefine_coq_sortedInsert with (len := n). rewrite -> H_l3. simpl. word.
      }
      { clear l3_ops YES1. iIntros "(%index & %acc & %peek_l & %l3_ops & H_s3 & H_l3_ops & H_i & H_l & H_intermediate & H_prev & H_curr & %H)".
        wp_pures. wp_apply wp_NewSlice. iIntros "%s4 H_s4". wp_apply wp_ref_to; eauto. iIntros "%output H_output". wp_pures. wp_store. wp_load. wp_store. wp_pures.
        replace (replicate (uint.nat (W64 0)) operation_into_val .(IntoVal_def (Slice.t * w64))) with (@nil (Slice.t * w64)) by reflexivity. destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8). specialize (H3 eq_refl).
        apply f_equal with (f := length) in H3. simpl in *. rewrite length_drop in H3. assert (length l3 = index + 1)%nat as YES by word.
        wp_apply (wp_forBreak_cond
          ( λ continue, ∃ s4 : Slice.t, ∃ l4_ops : list (Slice.t * w64),
            own_slice_small s3 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l3_ops ∗
            own_slice s4 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l4_ops ∗
            intermediate ↦[slice.T (slice.T uint64T * (uint64T * unitT)%ht)] s3 ∗
            output ↦[slice.T (slice.T uint64T * (uint64T * unitT)%ht)] s4 ∗
            i ↦[uint64T] #(W64 (length l4_ops)) ∗
            l ↦[uint64T] #(W64 (length acc + 1)%nat) ∗
            prev ↦[uint64T] #(W64 (length acc + 1)%nat) ∗
            ([∗ list] opv;o ∈ l3_ops;(acc ++ [peek_l] ++ drop (length acc + 1) l3), is_operation opv o n) ∗
            ([∗ list] opv;o ∈ l4_ops;take (length l4_ops) (acc ++ [peek_l] ++ drop (length acc + 1) l3), is_operation opv o n) ∗
            ⌜(length l4_ops <= (length acc + 1))%nat⌝ ∗
            ⌜continue = false -> length l4_ops = (length acc + 1)%nat⌝ 
          )%I
        with "[] [H_s3 H_s4 H_l3_ops H_prev H_i H_l H_intermediate H_output]").
        { clear Φ s4. iIntros "%Φ". iModIntro. iIntros "(%s4 & %l4_ops & H_s3 & H_s4 & H_intermediate & H_output & H_i & H_l & H_prev & H_l3 & H_l4 & %H_bound & %H_continue) HΦ".
          iPoseProof (own_slice_small_sz with "[$H_s3]") as "%claim1".
          wp_pures. wp_load. wp_load. wp_if_destruct.
          - iAssert ⌜is_Some (l3_ops !! uint.nat (W64 (length l4_ops)))⌝%I with "[H_l3]" as "[%x %H_x]".
            { iPoseProof (big_sepL2_length with "[$H_l3]") as "%YES1". iPureIntro. eapply lookup_lt_is_Some_2. word. }
            wp_pures. wp_load. wp_load. wp_apply (wp_SliceGet with "[$H_s3]"); eauto. iIntros "H_s3". wp_load. wp_apply (wp_SliceAppend with "[$H_s4]").
            iIntros "%s5 H_s5". wp_store. wp_load. wp_store. iModIntro. iApply "HΦ".
            iPoseProof (pers_big_sepL2_is_operation with "[$H_l3]") as "#H_l3_pers".
            iPoseProof (pers_big_sepL2_is_operation with "[$H_l4]") as "#H_l4_pers".
            iExists s5. iExists (l4_ops ++ [x])%list. iFrame.
            iPoseProof (big_sepL2_length with "[$H_l3_pers]") as "%YES1".
            iPoseProof (big_sepL2_length with "[$H_l4_pers]") as "%YES2".
            iSplitL "H_i". { rewrite length_app; simpl. replace (W64 (length l4_ops + 1)%nat) with (w64_word_instance .(word.add) (W64 (length l4_ops)) (W64 1)); eauto. word. }
            iSplitL "".
            { iApply big_sepL2_is_operation_intro.
              - rewrite length_take. rewrite <- YES1. rewrite length_app. simpl.
                do 2 rewrite length_app in YES1. rewrite length_take in YES2. do 2 rewrite length_app in YES2. simpl in *.
                enough ((length l4_ops + 1) <= length l3_ops)%nat by word.
                rewrite <- H6. rewrite <- YES1 in YES2. rewrite <- H6 in YES2. word.
              - clear i. iIntros "%i %l_i %ops_i [%YES3 %YES4]". assert (i < length (l4_ops ++ [x]))%nat as H by now eapply lookup_lt_is_Some_1.
                assert (i = length l4_ops \/ i < length l4_ops)%nat as [EQ | LT] by now rewrite length_app in H; simpl in H; word.
                + subst i. iApply (big_sepL2_is_operation_elim); cycle -1.
                  * iExact "H_l3_pers".
                  * instantiate (1 := length l4_ops).
                    rewrite lookup_take in YES3; trivial.
                  * replace (length l4_ops) with (uint.nat (W64 (length l4_ops))). { rewrite lookup_snoc in YES4. congruence. }
                    rewrite length_take in YES2. rewrite <- YES1 in YES2. word.
                + iApply (big_sepL2_is_operation_elim); cycle -1.
                  * iExact "H_l4_pers".
                  * instantiate (1 := i). rewrite lookup_take in YES3; trivial. rewrite lookup_take; trivial.
                  * rewrite lookup_app_l in YES4; trivial.
            }
            iClear "H_l4". iSplit.
            { iPureIntro. rewrite length_app. simpl. word. }
            { iPureIntro. congruence. }
          - iApply "HΦ". iExists s4. iExists l4_ops. iModIntro.
            iPoseProof (big_sepL2_length with "[$H_l4]") as "%claim3".
            iPoseProof (big_sepL2_length with "[$H_l3]") as "%claim4".
            iFrame. iPureIntro. split. { word. } intros _. rewrite length_take in claim3. rewrite <- claim4 in claim3.
            do 2 rewrite length_app in claim4. simpl in *. rewrite length_drop in claim4. word.
        }
        { iExists s4. iExists []%list. iFrame. simpl. iSplit. { done. } iPureIntro. split. { word. } { congruence. } }
        { clear s4. iIntros "(%s4 & %l4_ops & H_s3 & H_s4 & H_intermediate & H_output & H_i & H_l & H_prev & H_l3_ops & H_l4_ops & %H_bound & %H_continue)".
          specialize (H_continue eq_refl). wp_pures. wp_load. iModIntro. iApply "HΦ".
          assert (l3 = take index l3 ++ [peek_l]) as claim4.
          { rewrite <- take_drop with (l := l3) (i := index) at 1. f_equal.
            destruct (drop index l3) as [ | hd tl] eqn: H_OBS.
            - apply f_equal with (f := length) in H_OBS. simpl in *. rewrite length_drop in H_OBS. word.
            - f_equal.
              + rewrite <- take_drop with (l := l3) (i := index) in H1. rewrite lookup_app_r in H1.
                * rewrite length_take in H1. replace (index - index `min` length l3)%nat with 0%nat in H1 by word. rewrite H_OBS in H1. simpl in *. congruence.
                * rewrite length_take. word.
              + apply f_equal with (f := length) in H_OBS. simpl in *. rewrite length_drop in H_OBS. eapply nil_length_inv. word.
          }
          assert (fold_left coq_sortedInsert l2 l1 !! (index + 1)%nat = None) as claim5.
          { eapply lookup_ge_None. rewrite -> redefine_coq_sortedInsert with (len := n). rewrite H3_length. subst l3. rewrite <- redefine_coq_sortedInsert with (len := n) in *. word. }
          iExists (coq_mergeOperations l1 l2). iSplitL "H_s4 H_l4_ops".
          - iPoseProof (pers_big_sepL2_is_operation with "[$H_l4_ops]") as "#H_l4_ops_pers".
            subst l3. iExists l4_ops. iFrame. iApply big_sepL2_is_operation_intro.
            + unfold coq_mergeOperations. replace (fun acc => fun element => coq_sortedInsert acc element) with coq_sortedInsert by reflexivity.
              fold loop_step. fold loop_init. rewrite claim4. rewrite fold_left_app. simpl. rewrite <- H2. simpl.
              rewrite claim5. simpl. rewrite length_app. done.
            + clear i. iIntros "%i %l_i %ops_i [%H_l_i %H_ops_i]".
              iApply big_sepL2_is_operation_elim; cycle -1.
              * iExact "H_l4_ops".
              * instantiate (1 := i).
                assert ((acc ++ [peek_l]) !! i = Some l_i) as claim6.
                { unfold coq_mergeOperations in H_l_i. replace (fun acc => fun element => coq_sortedInsert acc element) with coq_sortedInsert in H_l_i by reflexivity.
                  fold loop_step in H_l_i. fold loop_init in H_l_i. rewrite claim4 in H_l_i. rewrite fold_left_app in H_l_i. simpl in *.
                  rewrite <- H2 in H_l_i. simpl in H_l_i. rewrite claim5 in H_l_i. simpl in *. done.
                }
                rewrite lookup_take. { rewrite app_assoc. rewrite lookup_app_l; eauto. eapply lookup_lt_is_Some_1. eauto. }
                eapply lookup_lt_is_Some_1. eauto.
              * eauto.
          - iPureIntro. split; trivial. unfold coq_mergeOperations. replace (fun acc => fun element => coq_sortedInsert acc element) with coq_sortedInsert by reflexivity.
            subst l3. fold loop_step. fold loop_init. rewrite claim4. rewrite fold_left_app. simpl in *.
            rewrite <- H2. simpl. rewrite claim5. simpl in *. done.
        }
      }
  Qed.

End heap.
