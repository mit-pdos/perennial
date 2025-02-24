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
        operation_slice s2 l2 n 
    }}}
      mergeOperations s1 s2 
    {{{
        ns, RET slice_val (ns);
        ∃ nxs, operation_slice ns nxs n ∗ ⌜nxs = coq_mergeOperations l1 l2⌝
    }}}.
  Proof.
    rewrite /mergeOperations. iIntros "%Φ [(%l1_ops & H_s1 & H_l1_ops) (%l2_ops & H_s2 & H_l2_ops)] HΦ".
    wp_rec. wp_pures. wp_apply (wp_NewSlice). iIntros "%s3 H_s3". replace (uint.nat (W64 0)) with 0%nat by word. simpl.
    wp_apply (wp_SliceAppendSlice with "[H_s1 H_s3]"); auto.
    { iFrame. iApply (own_slice_to_small with "[$H_s1]"). }
    clear s3. iIntros "%s3 [H_s3 H_s1]".
    wp_apply wp_ref_to; auto. iIntros "%output H_output". wp_pures.
    wp_apply wp_ref_to; auto. iIntros "%i H_i".
    wp_pures. wp_apply wp_slice_len. simpl.
    wp_apply wp_ref_to; auto. iIntros "%l H_l". wp_pures.
    iPoseProof (big_sepL2_length with "[$H_l2_ops]") as "%H_l2_ops_len".
    iPoseProof (own_slice_sz with "[$H_s2]") as "%H_l2_len".
    wp_apply (wp_forBreak_cond
      ( λ continue, ∃ s3 : Slice.t, ∃ l3_ops : list (Slice.t * w64), ∃ l2_prevs : list Operation.t, ∃ l2_nexts : list Operation.t,
        "H_s1" ∷ own_slice_small s1 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l1_ops ∗
        "H_s2" ∷ own_slice_small s2 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l2_ops ∗
        "H_s3" ∷ own_slice s3 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l3_ops ∗
        ([∗ list] opv;o ∈ l1_ops;l1, is_operation opv o n) ∗
        ([∗ list] opv;o ∈ drop (length l2_prevs) l2_ops;l2_nexts, is_operation opv o n) ∗
        ([∗ list] opv;o ∈ l3_ops;fold_left coq_sortedInsert l2_prevs l1, is_operation opv o n) ∗
        ⌜l2 = l2_prevs ++ l2_nexts⌝ ∗
        i ↦[uint64T] #(W64 (length l2_prevs)) ∗
        l ↦[uint64T] #s2 .(Slice.sz) ∗
        output ↦[slice.T (slice.T uint64T * (uint64T * unitT)%ht)] s3 ∗
        ⌜is_sorted (fold_left coq_sortedInsert l2_prevs l1)⌝ ∗
        ⌜Forall (Operation_wf n) (fold_left SessionPrelude.sortedInsert l2_prevs l1)⌝ ∗
        ⌜continue = false -> l2_nexts = []⌝
      )%I
    with "[] [H_l1_ops H_l2_ops H_s1 H_s2 H_s3 H_output H_i H_l]").
    { clear Φ s3. iIntros (Φ). iModIntro. iIntros "(%s3 & %l3_ops & %l2_prevs & %l2_nexts & H_s1 & H_s2 & H_s3 & H_l1_ops & H_l2_ops & H_l3_ops & %H_l2 & H_i & H_l & H_output & %H_sorted & %H_WF & %H_continue)".
      clear H_continue. iNamed "H_s1". iNamed "H_s2". iNamed "H_s3". iIntros "HΦ".
      wp_rec. wp_load. wp_load. wp_if_destruct.
      - iAssert (⌜uint.nat (W64 (length l2_prevs)) < length l2_ops⌝%nat)%I as "%H_bound".
        { iPoseProof (own_slice_small_sz with "[$H_s2]") as "%H_l2_ops_len'".
          iPureIntro. word.
        }
        apply lookup_lt_is_Some_2 in H_bound. destruct H_bound as [cur H_cur].
        wp_load. wp_apply (wp_SliceGet with "[H_s2]").
        { iSplitL "H_s2".
          - iExact "H_s2".
          - iPureIntro. exact H_cur.
        }
        iIntros "H_s2". wp_load. destruct l2_nexts as [ | l2_cur l2_nexts].
        { rewrite app_nil_r in H_l2. subst l2. word. }
        pose proof (take_drop_middle l2_ops (uint.nat (W64 (length l2_prevs))) cur H_cur) as H_middle.
        iPoseProof (big_sepL2_length with "[$H_l2_ops]") as "%YES".
        iPoseProof (big_sepL2_cons_inv_r with "[$H_l2_ops]") as "(%l2_cur' & %l2_nexts' & %EQ & H_l2_cur & H_l2_nexts)".
        iAssert ⌜cur = l2_cur'⌝%I as "%YES1".
        { rewrite <- H_middle in EQ. replace (uint.nat (W64 (length l2_prevs))) with (length l2_prevs) in EQ.
          - rewrite drop_app_ge in EQ.
            + replace (length l2_prevs - length (take (length l2_prevs) l2_ops))%nat with 0%nat in EQ.
              * simpl in *. iPureIntro. congruence.
              * rewrite length_take. enough (length l2_prevs <= length l2_ops)%nat by word.
                rewrite H_l2_ops_len. rewrite H_l2. rewrite length_app. simpl. word.
            + rewrite length_take. word.
          - enough (length l2_prevs <= uint.nat s2 .(Slice.sz))%nat by word.
            rewrite <- H_l2_len. rewrite H_l2_ops_len. rewrite H_l2. rewrite length_app. word.
        }
        iAssert ⌜length l2_cur .(Operation.VersionVector) = n⌝%I as "%YES2".
        { iDestruct "H_l2_cur" as "(%H1 & %H2 & H3)". done. }
        subst l2_cur'. rename l2_nexts' into l2_ops_nexts.
        wp_apply (wp_sortedInsert with "[H_s3 H_l3_ops H_l2_cur]").
        { iSplitR "H_l2_cur".
          - iExists l3_ops. iFrame.
          - iFrame. iPureIntro. done.
        }
        iIntros "%ns (%nxs & H_ns & %H_nxs)". iDestruct "H_ns" as "(%ns_ops & H_ns & H_ns_ops)".
        wp_store. wp_load. wp_store. iModIntro. iApply "HΦ".
        iAssert ⌜Operation_wf n l2_cur⌝%I as "%YES3".
        { iPureIntro. red. split.
          - eapply SessionPrelude.Forall_True.
          - done.
        }
        iExists ns. iExists ns_ops. iExists (l2_prevs ++ [l2_cur])%list. iExists l2_nexts. iFrame.
        iSplitL "H_l2_nexts".
        { replace (drop (length (l2_prevs ++ [l2_cur])) l2_ops) with l2_ops_nexts.
          - iFrame.
          - apply @f_equal with (f := drop 1) in EQ. simpl in EQ. replace (drop 0 l2_ops_nexts) with l2_ops_nexts in EQ by reflexivity.
            rewrite <- EQ. rewrite drop_drop. f_equal. rewrite length_app. simpl. reflexivity.
        }
        iSplitL "H_ns_ops".
        { rewrite H_nxs. rewrite fold_left_app. simpl. iFrame. }
        iSplitL "".
        { iPureIntro. rewrite <- app_assoc. simpl. done. }
        iSplitL "H_i".
        { rewrite length_app. simpl. replace ((w64_word_instance .(word.add) (W64 (length l2_prevs)) (W64 1))) with (W64 (length l2_prevs + 1)%nat) by word. iFrame. }
        iSplit.
        { rewrite fold_left_app. simpl. iPureIntro. replace is_sorted with (SessionPrelude.isSorted (hsOrd := hsOrd_Operation n)) by reflexivity.
          replace coq_sortedInsert with (SessionPrelude.sortedInsert (hsOrd := hsOrd_Operation n)) by reflexivity. eapply SessionPrelude.sortedInsert_isSorted; eauto. 
        }
        iSplit.
        { iPureIntro. rewrite fold_left_app. simpl.
          pose proof (SessionPrelude.sortedInsert_spec (hsOrd := hsOrd_Operation n) (fold_left (SessionPrelude.sortedInsert (hsOrd := hsOrd_Operation n)) l2_prevs l1) l2_cur H_WF YES3 H_sorted) as (prefix & suffix & _ & _ & _ & _ & as_wanted). done.
        }
        { iPureIntro. congruence. }
      - iModIntro. iApply "HΦ".
        iAssert ⌜length l2_prevs = length l2⌝%I as "%YES1".
        { iPureIntro. rewrite H_l2_ops_len in H_l2_len. rewrite -> H_l2 in H_l2_len |- *.
          rewrite -> length_app in H_l2_len |- *. word.
        }
        iAssert ⌜l2_nexts = []⌝%I as "%YES2".
        { destruct l2_nexts as [ | l2_nexts_hd l2_nexts_tl].
          - iPureIntro. done.
          - rewrite H_l2 in YES1. rewrite length_app in YES1. simpl in *. word.
        }
        subst l2_nexts. rewrite app_nil_r in H_l2. subst l2_prevs.
        iExists s3. iExists l3_ops. iExists l2. iExists []. iFrame.
        rewrite app_nil_r. done.
    }
    { iAssert (<pers> ([∗ list] opv;o ∈ l1_ops;l1, is_operation opv o n))%I as "#H_l1_ops_pers".
      { iApply pers_big_sepL2_is_operation. done. }
      iExists s3. iExists l1_ops. iExists []. iExists l2. simpl.
      iPoseProof (big_sepL2_length with "[$H_l1_ops_pers]") as "%H_l1_len".
      iFrame. iSplit.
      { iApply (own_slice_to_small with "[$H_s2]"). }
      iSplit.
      { iExact "H_l1_ops_pers". }
      iSplit.
      { done. }
      iSplit.
      { admit. }
      iSplit.
      { iApply Forall_Operation_wf. iExact "H_l1_ops_pers". }
      { iPureIntro. congruence. }
    }
    admit. (*
    clear s3. iIntros "(%s3 & %l3_ops & %l2_prevs & %l2_nexts & H_s1 & H_s2 & H_s3 & H_l1_ops & H_l2_ops & H_l3_ops & %H_l2 & H_i & H_l & H_output & %H_l2_nexts)".
    specialize (H_l2_nexts eq_refl). subst l2_nexts. rewrite app_nil_r in H_l2. subst l2_prevs. iNamed "H_s1". iNamed "H_s2". iNamed "H_s3".
    wp_pures. wp_apply wp_ref_to; auto. iIntros "%prev H_prev".
    wp_pures. wp_apply wp_ref_to; auto. iIntros "%curr H_curr".
    wp_pures.
    remember (fold_left coq_sortedInsert l2 l1) as l3 eqn: H_l3.
    set (loop_step := λ (acc: nat * list Operation.t) (element : Operation.t),
      let (index, acc) := acc in
      if (index >? 0) then 
        match (l3 !! (uint.nat (index - 1))) with
        | Some v => if (coq_equalOperations element v) then ((index + 1)%nat, acc) else ((index + 1)%nat,  acc ++ [element])
        | None => ((index + 1)%nat, acc ++ [element])
        end
      else ((index + 1)%nat, acc ++ [element])
    ).
    set (loop_init := (0%nat, @nil Operation.t)).
    destruct l3 as [ | l3_hd l3_tl].
    - wp_apply (wp_forBreak_cond
        ( λ continue, ∃ s3 : Slice.t, ∃ l3_ops : list (Slice.t * w64), 
          "H_s1" ∷ own_slice_small s1 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l1_ops ∗
          "H_s2" ∷ own_slice s2 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l2_ops ∗
          "H_s3" ∷ own_slice s3 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l3_ops ∗
          ([∗ list] opv;o ∈ l1_ops;l1, □ is_operation opv (DfracOwn 1) o n) ∗
          ([∗ list] opv;o ∈ l2_ops;l2, □ is_operation opv (DfracOwn 1) o n) ∗
          ([∗ list] opv;o ∈ l3_ops;[], is_operation opv (DfracOwn 1) o n) ∗
          prev ↦[uint64T] #1 ∗
          curr ↦[uint64T] #1 ∗
          output ↦[slice.T (slice.T uint64T * (uint64T * unitT)%ht)] s3
        )%I
      with "[] [H_prev H_curr H_output H_s1 H_s2 H_s3 H_l1_ops H_l2_ops H_l3_ops]").
      { clear Φ s3 l3_ops. iIntros (Φ). iModIntro. iIntros "(%s3 & %l3_ops & H_s1 & H_s2 & H_s3 & H_l1_ops & H_l2_ops & H_l3_ops & H_prev & H_curr & H_output) H_ret".
        wp_pures. wp_load. wp_load. wp_apply wp_slice_len. wp_if_destruct.
        - wp_pures. iExFalso.
          iPoseProof (own_slice_sz with "[$H_s3]") as "%H_l3_ops_len".
          iPoseProof (big_sepL2_length with "[$H_l3_ops]") as "%H_l3_len".
          simpl in *. word.
        - iModIntro. iApply "H_ret". iExists s3. iExists l3_ops. iFrame.
      }
      { iExists s3. iExists l3_ops. iFrame. }
      { clear s3 l3_ops.
        iIntros "(%s3 & %l3_ops & H_s1 & H_s2 & H_s3 & H_l1_ops & H_l2_ops & H_l3_ops & H_output & H_prev & H_curr)".
        wp_pures. wp_load. wp_load. wp_apply (wp_SliceTake).
        { admit. (* uint.Z (W64 1) ≤ uint.Z s3 .(Slice.cap) *) }
        iApply "H_ret". iExists (coq_mergeOperations l1 l2). iSplitL.
        - iExists []. unfold coq_mergeOperations. replace (fold_left (λ (acc : list Operation.t) (element : Operation.t), coq_sortedInsert acc element) l2 l1) with (@nil Operation.t). simpl.
          iAssert ⌜l3_ops = []⌝%I as "%H_l3_ops_nil".
          { iApply (big_sepL2_nil_inv_r with "[$H_l3_ops]"). }
          subst l3_ops. iSplitR "H_l3_ops".
          + admit. (* own_slice (slice_take s3 (W64 1)) (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) [] *)
          + iApply (big_sepL2_nil). iExact "H_l3_ops".
        - done.
      }
    - wp_apply (wp_forBreak_cond
        ( λ continue, ∃ s3 : Slice.t, ∃ l3_ops : list (Slice.t * w64), ∃ l3_sec1 : list Operation.t, ∃ l3_sec2 : list Operation.t, ∃ l3_sec3 : list Operation.t,
          "H_s1" ∷ own_slice_small s1 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l1_ops ∗
          "H_s2" ∷ own_slice s2 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l2_ops ∗
          "H_s3" ∷ own_slice s3 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l3_ops ∗
          ([∗ list] opv;o ∈ l1_ops;l1, □ is_operation opv (DfracOwn 1) o n) ∗
          ([∗ list] opv;o ∈ l2_ops;l2, □ is_operation opv (DfracOwn 1) o n) ∗
          ([∗ list] opv;o ∈ l3_ops;snd (fold_left loop_step (l3_sec1 ++ l3_sec2) loop_init) ++ l3_sec2 ++ l3_sec3, is_operation opv (DfracOwn 1) o n) ∗
          ⌜l3_hd :: l3_tl = l3_sec1 ++ l3_sec2 ++ l3_sec3⌝%list ∗
          prev ↦[uint64T] #(length l3_sec1) ∗
          curr ↦[uint64T] #(length (l3_sec1 ++ l3_sec2)) ∗
          output ↦[slice.T (slice.T uint64T * (uint64T * unitT)%ht)] s3 ∗
          ⌜continue = false -> l3_sec3 = []⌝ ∗
          ⌜length l3_sec1 = length (snd (fold_left loop_step (l3_sec1 ++ l3_sec2) loop_init))⌝ ∗
          ⌜length (l3_sec1 ++ l3_sec2) = fst (fold_left loop_step (l3_sec1 ++ l3_sec2) loop_init)⌝ ∗
          ⌜length (l3_sec1 ++ l3_sec2 ++ l3_sec3) = uint.nat s3 .(Slice.sz)⌝ ∗
          ⌜length (l3_sec1) > 0⌝%nat ∗
          ⌜length (l3_sec1 ++ l3_sec2) > 0⌝%nat
        )%I
      with "[] [H_l1_ops H_l2_ops H_l3_ops H_s1 H_s2 H_s3 H_output H_prev H_curr]").
      { clear Φ s3 l3_ops. iIntros (Φ). iModIntro.
        iIntros "(%s3 & %l3_ops & %l3_sec1 & %l3_sec2 & %l3_sec3 & H_s1 & H_s2 & H_s3 & H_l1_ops & H_l2_ops & H_l3_ops & %H_l3_secs & H_prev & H_curr & H_output & %H_continue & %H_prev_val & %H_curr_val & %H_l3_len & %H_prev_val_pos & %H_curr_val_pos) H_ret".
        wp_rec. wp_load. wp_load. wp_apply wp_slice_len. wp_if_destruct.
        - iAssert (⌜is_Some (l3_ops !! uint.nat (W64 (length (l3_sec1 ++ l3_sec2))))⌝%I) as "%SOME".
          { iPoseProof (big_sepL2_length with "[$H_l3_ops]") as "%H_l3_ops_len". 
            rewrite length_app in H_l3_ops_len. rewrite <- H_prev_val in H_l3_ops_len. rewrite length_app in H_l3_ops_len.
            iPureIntro. eapply lookup_lt_is_Some_2. do 2 rewrite length_app in H_l3_len. rewrite length_app. rewrite length_app in Heqb. word.
          }
          destruct SOME as [peek H_peek].
          wp_pures. wp_load. wp_load. wp_apply (wp_SliceGet with "[H_s3]").
          { iSplitL "H_s3".
            - iApply (own_slice_to_small with "[$H_s3]").
            - iPureIntro. exact H_peek.
          }
          iAssert (⌜is_Some (l3_ops !! uint.nat (W64 (length (l3_sec1 ++ l3_sec2) - 1)))⌝%I) as "%SOME".
          { iPoseProof (big_sepL2_length with "[$H_l3_ops]") as "%H_l3_ops_len". 
            rewrite length_app in H_l3_ops_len. rewrite <- H_prev_val in H_l3_ops_len. rewrite length_app in H_l3_ops_len.
            iPureIntro. eapply lookup_lt_is_Some_2. do 2 rewrite length_app in H_l3_len. rewrite length_app. rewrite length_app in Heqb. word.
          }
          destruct SOME as [peek' H_peek'].
          iIntros "H_s3". wp_load. wp_load. wp_apply (wp_SliceGet with "[H_s3]").
          { iSplitL "H_s3".
            - iExact "H_s3".
            - iPureIntro. replace (uint.nat (W64 (length (l3_sec1 ++ l3_sec2) - 1))) with (uint.nat (w64_word_instance .(word.sub) (W64 (length (l3_sec1 ++ l3_sec2))) (W64 1))) in H_peek' by word. exact H_peek'.
          }
          iIntros "H_s3". simpl. admit.
        - iModIntro. iApply "H_ret". iExists s3. iExists l3_ops. iExists l3_sec1. iExists l3_sec2. iExists l3_sec3.
          iAssert ⌜l3_sec3 = []⌝%I as "%H_l3_sec3_nil".
          { iPureIntro. enough (length l3_sec3 = 0)%nat by by destruct l3_sec3.
            rewrite length_app in Heqb. rewrite length_app in H_curr_val_pos. do 2 rewrite length_app in H_l3_len. word.
          }
          iFrame. done.
      }
      { iExists s3. iExists l3_ops. iExists [l3_hd]%list. iExists []%list. iExists l3_tl. simpl.
        iPoseProof (own_slice_sz with "[$H_s3]") as "%claim1".
        iPoseProof (big_sepL2_length with "[$H_l3_ops]") as "%claim2".
        rewrite claim1 in claim2. simpl in *. symmetry in claim2. iFrame.
        iSplit. { iPureIntro. done. }
        iSplit. { iPureIntro. congruence. }
        iSplit. { iPureIntro. done. }
        iSplit. { iPureIntro. done. }
        iSplit. { iPureIntro. done. }
        word.
      }
      { clear s3 l3_ops.
        iIntros "(%s3 & %l3_ops & %l3_sec1 & %l3_sec2 & %l3_sec3 & H_s1 & H_s2 & H_s3 & H_l1_ops & H_l2_ops & H_l3_ops & %H_l3_secs & H_prev & H_curr & H_output & %H_continue & %H_prev_val & %H_curr_val & %H_l3_len & %H_prev_val_pos & %H_curr_val_pos)".
        iNamed "H_s1". iNamed "H_s2". iNamed "H_s3".
        wp_pures. wp_load. wp_load. 
        iAssert ⌜uint.Z (W64 (length l3_sec1)) ≤ uint.Z s3 .(Slice.cap)⌝%I as "%H_s3_cap".
        { iPoseProof (own_slice_small_wf with "[H_s3]") as "%H_claim1".
          { iApply (own_slice_to_small with "[$H_s3]"). }
          do 2 rewrite length_app in H_l3_len. simpl in *. word.
        }
        iAssert ⌜uint.Z (W64 (length l3_sec1)) ≤ length l3_ops⌝%I as "%claim1".
        { iPoseProof (big_sepL2_length with "[$H_l3_ops]") as "%H_l3_ops_len".
          do 2 rewrite length_app in H_l3_ops_len. rewrite <- H_prev_val in H_l3_ops_len. word.
        }
        wp_apply (wp_SliceTake_full with "[$H_s3]"); auto. iIntros "H_s3".
        iApply "H_ret". iExists (coq_mergeOperations l1 l2). iSplitL.
        - iExists (take (length l3_sec1) l3_ops). do 2 rewrite length_app in H_l3_len.
          replace (uint.nat (W64 (length l3_sec1))) with (length l3_sec1) by word.
          unfold coq_mergeOperations. replace (fold_left (λ (acc : list Operation.t) (element : Operation.t), coq_sortedInsert acc element) l2 l1) with (l3_hd :: l3_tl)%list.
          specialize (H_continue eq_refl). subst l3_sec3. rewrite app_nil_r in H_l3_secs, H_l3_len |- *.
          fold loop_step. fold loop_init. rewrite H_l3. iFrame. clear Φ.
          simpl in *. rewrite Nat.add_0_r in H_l3_len. admit.
        - done.
      } *)
  Admitted.

End heap.
