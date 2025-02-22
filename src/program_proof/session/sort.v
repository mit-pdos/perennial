From Perennial.program_proof.session Require Export session_prelude.
From Perennial.program_proof.session Require Export coq_session.
From Perennial.program_proof.session Require Export versionVector.

Section heap.
  Context `{hG: !heapGS Σ}.

  Definition is_sorted (l: list Operation.t) :=
    ∀ (i j: nat), (i < j)%nat ->
                  ∀ (o1 o2: Operation.t), l !! i = Some o1 ->
                                          l !! j = Some o2 ->
                                          coq_lexicographicCompare
                                            (o2.(Operation.VersionVector)) (o1.(Operation.VersionVector)) = true \/
                                                                                                              coq_equalSlices (o2.(Operation.VersionVector)) (o1.(Operation.VersionVector)) = true.
  
  Lemma implies_Sorted :
    forall (l: list Operation.t) (element: Operation.t) (i: u64),
    is_sorted l ->
    uint.nat i <= length l ->
    (∀ (i': nat), i' < uint.nat i ->
                  ∀ (x: Operation.t), l !! i' = Some x ->
                                      coq_lexicographicCompare
                                        (element.(Operation.VersionVector)) (x.(Operation.VersionVector)) = true) -> 
    (∀ (j': nat),
       uint.nat i ≤ j' →
       ∀ (y: Operation.t), l !! j' = Some y →
                           coq_lexicographicCompare (y.(Operation.VersionVector))
                             (element.(Operation.VersionVector)) = true
                                                                   \/
                                                                     coq_equalSlices
                                                                       (y.(Operation.VersionVector))
                                                                       (element.(Operation.VersionVector)) = true)
    -> is_sorted ((take (uint.nat i) l) ++ (cons element (drop (uint.nat i) l))).
  Proof.
    unfold is_sorted. intros.
    destruct (decide (j < uint.nat i)).
    - assert (i0 < (uint.nat i - 1)) by word.
      rewrite lookup_app_l in H4.
      + rewrite lookup_app_l in H5.
        * rewrite lookup_take in H4; try word.
          rewrite lookup_take in H5; try word.
          eapply H in H3; try eassumption.
        * rewrite length_take_le; try word.
      + rewrite length_take_le; try word.
    - assert (j >= (uint.nat i - 1)) by word. clear n.
      destruct (decide (j = (uint.nat i)%nat)).
      + clear H6. subst.
        rewrite lookup_app_l in H4.
        * rewrite lookup_app_r in H5.
          -- rewrite length_take_le in H5; try word.
             assert ((uint.nat i - (uint.nat i))%nat = 0%nat) by word.
             rewrite H6 in H5. rewrite <- head_lookup in H5. simpl in H5.
             injection H5 as ?. rewrite lookup_take in H4; try word. 
             assert (i0 < uint.nat i) by word. rewrite <- H5.
             left. eapply H1; try eassumption.
          -- rewrite length_take_le; try word.
        * rewrite length_take_le; try word.
      + destruct (decide (i0%nat = (uint.nat i))).
        * assert (j > uint.nat i) by word. rewrite lookup_app_r in H4.
          -- rewrite lookup_app_r in H5.
             ++ rewrite e in H4. rewrite length_take_le in H4; try word.
                assert ((uint.nat i - uint.nat i)%nat = 0%nat) by word.
                rewrite H8 in H4. rewrite <- head_lookup in H4. simpl in H4.
                injection H4 as ?. rewrite <- H4.
                rewrite lookup_cons_ne_0 in H5; try rewrite length_take_le; try word.
                rewrite lookup_drop in H5. eapply H2.
                ** assert (uint.nat i <= (uint.nat i + Init.Nat.pred (j - length (take (uint.nat i) l)))%nat)
                     by word. apply H9. 
                ** auto. 
             ++ rewrite length_take_le; try word.
          -- rewrite length_take_le; try word.
        * destruct (decide (i0%nat > (uint.nat i))).
          -- clear n0. clear n.
             rewrite lookup_app_r in H4; try rewrite length_take_le; try word.
             rewrite lookup_app_r in H5; try rewrite length_take_le; try word.
             rewrite lookup_cons_ne_0 in H4; try rewrite length_take_le; try word.
             rewrite lookup_cons_ne_0 in H5; try rewrite length_take_le; try word.
             rewrite lookup_drop in H4. rewrite lookup_drop in H5.
             rewrite length_take_le in H4; try word.
             rewrite length_take_le in H5; try word.
             eapply H.
             ++ assert (Init.Nat.pred (i0 - uint.nat i) <Init.Nat.pred (j - uint.nat i)) by word.
                assert (uint.nat i + Init.Nat.pred (i0 - uint.nat i) <
                          uint.nat i + Init.Nat.pred (j - uint.nat i))%nat by word.
                apply H8.
             ++ auto.
             ++ auto.
          -- assert (i0 < uint.nat i) by word.
             destruct (decide (j = (uint.nat i - 1)%nat)).
             ++ rewrite lookup_app_l in H4; try rewrite length_take_le; try word.
                rewrite lookup_app_l in H5; try rewrite length_take_le; try word.
                rewrite lookup_take in H4; try word.
                rewrite lookup_take in H5; try word.
                eapply H in H3; try eassumption.
             ++ assert (j > uint.nat i) by word.
                rewrite lookup_app_l in H4; try rewrite length_take_le; try word.
                rewrite lookup_app_r in H5; try rewrite length_take_le; try word.
                rewrite lookup_cons_ne_0 in H5; try rewrite length_take_le;
                  try word.
                rewrite lookup_take in H4; try word.
                rewrite lookup_drop in H5. eapply H.
                ** assert (i0 < (uint.nat i + Init.Nat.pred (j - length (take (uint.nat i) l)))%nat)%nat by word.
                   apply H9.
                ** auto.
                ** auto.
  Qed.

  Lemma op_versionVector_len (s: Slice.t) (l: list Operation.t) 
    (opv: Slice.t*u64) (n: nat) :
    (operation_slice s l n ⊢@{_} ⌜∀ i e, l !! i = Some e -> length e.(Operation.VersionVector) = n⌝)%I.
  Proof.
    iIntros "H".
    unfold operation_slice. unfold operation_slice'.
    iDestruct "H" as "[%ops H]".
    iDestruct "H" as "(H & H1)".
    iDestruct (big_sepL2_length with "H1") as "%H".
    iApply big_sepL2_sep in "H1".
    iDestruct "H1" as "(H1 & H2)".
    iApply big_sepL2_sep in "H2".
    iDestruct "H2" as "(H2 & _)".
    iApply big_sepL2_pure_1 in "H2".
    iDestruct "H2" as "%H1".
    iPureIntro.
    intros.
    assert (i < length l)%nat. {
      eapply lookup_lt_Some.
      eassumption.
    }
    assert (i < length ops)%nat by word.
    apply list_lookup_lt in H3 as [x H3].
    symmetry. eapply H1.
    - eassumption.
    - auto.
  Qed.
  
  Lemma wp_BinarySearch (s: Slice.t) (l: list Operation.t)
    (opv: Slice.t*u64) (needle: Operation.t) (n: nat) :
    {{{
          operation_slice s l n ∗
          is_operation opv needle n ∗
          ⌜is_sorted l⌝
    }}}
      binarySearch s (operation_val opv)
      {{{ (i: u64) , RET #i ;
          operation_slice s l n ∗
          is_operation opv needle n ∗
          ⌜is_sorted l⌝ ∗
          ⌜ ∀ (i': nat), i' < uint.nat i ->
                         ∀ (x: Operation.t), l !! i' = Some x -> 
                                             coq_lexicographicCompare (needle.(Operation.VersionVector)) (x.(Operation.VersionVector)) = true⌝ ∗ ⌜∀ (j': nat),
            uint.nat i ≤ j' →
            ∀ (y: Operation.t), l !! j' = Some y -> 
                                coq_lexicographicCompare (y.(Operation.VersionVector)) (needle.(Operation.VersionVector)) = true \/ coq_equalSlices (y.(Operation.VersionVector)) (needle.(Operation.VersionVector)) = true⌝ ∗
                                ⌜uint.nat i <= length l⌝
      }}}.
  Proof.
    iIntros (Φ) "(H & H1 & %H2) H4". unfold binarySearch.
    wp_pures.
    wp_apply wp_ref_to; auto.
    iIntros (i_l) "i". wp_pures.
    wp_apply wp_slice_len.
    wp_apply wp_ref_to; auto.
    iIntros (j_l) "j". wp_pures.
    iDestruct (op_versionVector_len with "H") as "%len"; auto.
    iNamed "H".
    iDestruct "H" as "(H & H2)".
    iDestruct "H" as "(H & H3)".
    iDestruct (big_sepL2_length with "H2") as "%len1".
    iDestruct (slice.own_slice_small_sz with "H") as %Hsz.
    unfold is_operation.
    iApply big_sepL2_sep in "H2".
    wp_apply (wp_forBreak_cond
                (λ continue, ∃ (i j: w64),
                    operation_slice s l n ∗
                    is_operation opv needle n ∗
                    i_l ↦[uint64T] #i ∗
                    j_l ↦[uint64T] #j ∗
                    ⌜uint.Z i ≤ uint.Z j ≤ Z.of_nat (length l)⌝ ∗
                    ⌜∀ (i': nat),
                   i' < uint.nat i →
                   ∀ (x: Operation.t), l !! i' = Some x -> coq_lexicographicCompare (needle.(Operation.VersionVector)) (x.(Operation.VersionVector)) = true⌝ ∗
                                       ⌜∀ (j': nat),
                   uint.nat j ≤ j' →
                   ∀ (y: Operation.t), l !! j' = Some y ->
                                       coq_lexicographicCompare (y.(Operation.VersionVector)) (needle.(Operation.VersionVector)) = true \/ coq_equalSlices (y.(Operation.VersionVector)) (needle.(Operation.VersionVector)) = true⌝ ∗
                                       ⌜continue = false → i = j⌝ ∗
                                       ⌜uint.nat i <= length l⌝ 
                )%I
               with "[] [H H1 H2 H3 i j]").
    - iIntros (?). iModIntro. iIntros "H1 H2".
      wp_pures. iNamed "H1".
      iDestruct "H1" as "(H & H1 & H3 & H4 & %H5 & %H6 & %H7)".
      wp_load. wp_load.
      wp_if_destruct.
      + wp_pures.
        wp_load. wp_load. wp_load. wp_pures.
        set (mid := word.add i (word.divu (word.sub j i) (W64 2)) : w64).
        assert (uint.Z mid = (uint.Z i + uint.Z j) / 2) as Hmid_ok.
        { subst mid.
          word. }
        list_elem l (uint.nat mid) as x_mid.
        iNamed "H".
        iDestruct "H" as "(H & H5)".
        iDestruct "H" as "(H & H6)".
        iDestruct (big_sepL2_length with "H5") as "%H8".
        assert (length (list.untype ops0) = length ops0). {
          apply list_untype_length. }
        assert (uint.nat mid < length (list.untype ops0))%nat by word.
        assert (uint.nat mid < length ops0)%nat by word.
        apply list_lookup_lt in H0.
        apply list_lookup_lt in H1.
        destruct H0.
        destruct H1.
        wp_apply (slice.wp_SliceGet with "[H]").
        * unfold own_slice_small. simpl. iSplitL.
          { iFrame. }
          { iPureIntro. apply H0. }
        * iIntros "(H & %H3)". wp_pures.
          wp_bind (lexicographicCompare _ _).
          wp_pures. unfold operation_val.
          iDestruct (big_sepL2_insert_acc _ _ _ _ _ _ H1 Hx_mid_lookup with "H5")
            as "[H7 H8]".
          destruct x_mid as [a b].
          apply untype_lookup_Some in H0.
          destruct H0. destruct H0.
          assert (x0 = x1). {
            rewrite H0 in H1. inversion H1. auto. }
          rewrite H4.
          iDestruct "H7" as "(#H7 & %H10 & #H10)".
          iDestruct "H1" as "(#H1 & %H11 & #H12)".
          wp_apply (wp_lexicographicCompare with "[H12]").
          { unfold is_operation.
            iSplitL "H12".
            - simpl. iApply "H12".
            - iSplitL.
              + rewrite H9. iApply "H10".
              + rewrite <- H11. word.
          }
          iIntros (r) "(%H13 & H5 & H14 & H15)".
          wp_if_destruct.
          { wp_store. iModIntro. iApply "H2".
            iExists (W64 (uint.Z mid + 1)). 
            iExists (j).
            iFrame.
            remember ({| Operation.VersionVector := a; Operation.Data := b |}) as t0.
            iAssert (⌜t0 = {| Operation.VersionVector := a; Operation.Data := b |}⌝)%I as "H".
            { iPureIntro. auto. }
            iSpecialize ("H8" with "[H14 H10 H]"). {
              iAssert (□ is_operation x0 t0 n)%I with "[H14 H10]" as "H2". {
                rewrite /is_operation. iSplitL.
                - iApply "H7".
                - iSplitL.
                  + word.
                  + iApply "H10". }
              iApply "H2". }
            iSplitL.
            - rewrite Heqt0. simpl in *. assert (<[uint.nat mid:=x1]> ops0 = ops0). {
                apply list_insert_id. auto.
              }
              assert (<[uint.nat mid:={| Operation.VersionVector := a; Operation.Data := b |}]> l = l).
              { apply list_insert_id. rewrite <- Heqt0. auto. }
              rewrite H14. subst. rewrite H12. iFrame.
            - iSplitL.
              + iSplitL. { iApply "H1". }
                word.
              + intros. unfold is_sorted in H2.
                assert (coq_lexicographicCompare needle.(Operation.VersionVector) t0.(Operation.VersionVector) = true).
                {
                  symmetry. auto.
                }
                iPureIntro.
                * split; try word.
                  -- intros. split.
                     ++ intros. destruct (decide ((i' < uint.nat mid)%nat)).
                        { unfold is_sorted in H2.
                          apply (H2 i' (uint.nat mid) l0 x2 t0) in H15 as H16; try eassumption.
                          destruct H16.
                          { eapply aux0_lexicographicCompare; try eassumption. }
                          { rewrite H10 in H11.
                            symmetry.
                            apply aux0_equalSlices in H16; auto.
                            - rewrite <- H16. auto.
                            - rewrite <- H10. symmetry. eapply len. apply H15.
                          }
                        }
                        { assert (i' <= uint.nat mid)%nat by word.
                          assert (i' = uint.nat mid) by word. subst.
                          rewrite Hx_mid_lookup in H15. inversion H15. subst. auto.
                        }
                     ++ split; try word.
                        intros. eapply H7; try eassumption.
          }
          {
            wp_store.
            iModIntro.
            iApply "H2".
            iExists i.
            iExists mid.
            iFrame.
            remember ({| Operation.VersionVector := a; Operation.Data := b |}) as t0.
            iAssert (⌜t0 = {| Operation.VersionVector := a; Operation.Data := b |}⌝)%I as "H".
            { iPureIntro. auto. }
            iSpecialize ("H8" with "[H14 H10 H]"). {
              iAssert (□ is_operation x0 t0 n)%I with "[H14 H10]" as "H2". {
                rewrite /is_operation. iSplitL.
                - iApply "H7".
                - iSplitL.
                  + word.
                  + iApply "H10". }
              iApply "H2". }
            iSplitL.
            - rewrite Heqt0. simpl in *. assert (<[uint.nat mid:=x1]> ops0 = ops0). {
                apply list_insert_id. auto.
              }
              assert (<[uint.nat mid:={| Operation.VersionVector := a; Operation.Data := b |}]> l = l).
              { apply list_insert_id. rewrite <- Heqt0. auto. }
              rewrite H14. subst. rewrite H12. iFrame.
            - iDestruct "H1" as "%H14".
              iDestruct "H" as "%H15".
              iDestruct "H7" as "%H16".              
              iPureIntro.
              split_and!; try word.
              { auto. }
              intros. unfold is_sorted in *. 
              assert (coq_lexicographicCompare needle.(Operation.VersionVector) t0.(Operation.VersionVector) = false).
              {
                symmetry. auto.
              }
              destruct (decide (uint.nat mid = j')).
              + rewrite e in Hx_mid_lookup. rewrite H17 in Hx_mid_lookup. injection Hx_mid_lookup as
                ?. subst. destruct (decide (coq_equalSlices {| Operation.VersionVector := a; Operation.Data := b |}.(Operation.VersionVector) needle.(Operation.VersionVector) = true)).
                * right. auto.
                * left. apply aux1_lexicographicCompare; auto. apply aux1_equalSlices; auto.
                  apply not_true_is_false in n. auto.
              + assert (uint.nat mid < j')%nat by word.
                eapply (H2 (uint.nat mid) j' H19 t0 y) in H17 as H20.
                * destruct H20.
                  { left. destruct (decide (t0.(Operation.VersionVector) = needle.(Operation.VersionVector))).
                    - rewrite <- e. auto.
                    - eapply aux1_lexicographicCompare in H18; try eassumption.
                      + eapply aux0_lexicographicCompare; eassumption.
                      + word.
                  }
                  { destruct (decide (t0.(Operation.VersionVector) = needle.(Operation.VersionVector))).
                    - right. apply aux0_equalSlices in H20.
                      + rewrite H20. rewrite e. apply aux3_equalSlices.
                      + rewrite <- H10. eapply len. eassumption.
                    - left. apply aux0_equalSlices in H20.
                      + rewrite <- H20 in H18. apply aux1_lexicographicCompare in H18.
                        * auto.
                        * rewrite <- H11. eapply len; eassumption.
                        * rewrite H20. auto.
                      + rewrite <- H10. eapply len; eassumption.
                  }
                * auto.
          } 
      + iModIntro.
        iApply "H2".
        iFrame.
        iPureIntro.
        split_and!; try word; auto.
        * destruct H7. auto.
        * intros. word.
    - iFrame.
      iDestruct "H2" as "[H2 H3]".
      iApply big_sepL2_sep_2 in "H2".
      iApply "H2" in "H3".
      iFrame.
      iPureIntro.
      split; try word.
      + rewrite list_untype_length in Hsz. word.
      + split; try word.
        split; try word.
        intros. apply lookup_lt_Some in H0.
        assert (length ops = length (list.untype ops)). {
          symmetry. apply list_untype_length. } word.
    - iIntros "Hpost".
      wp_pures. iNamed "Hpost". iDestruct "Hpost" as "(H2 & H3 & H5 & H6 & %H7 & %H8 & %H9 & %H10)".
      wp_load. wp_pures. iModIntro. 
      iApply "H4". iFrame. iPureIntro. split; auto.
      split; auto. split.
      + intros. destruct H10. destruct H1; auto.
        eapply H9; eassumption.
      + destruct H10. auto.
  Qed.

  (*
  Lemma wp_sortedInsert (s: Slice.t) (l: list Operation.t)
    (opv: Slice.t*u64) (v: Operation.t) (n: nat) :
    {{{
          operation_slice s l n ∗
          is_operation opv v n ∗
          ⌜is_sorted l⌝ 
    }}}
      sortedInsert s (operation_val opv)
      {{{ (ns: Slice.t), RET slice_val (ns);
          ∃ nxs, operation_slice ns nxs n %I ∗
                 ⌜nxs = coq_sortedInsert l v⌝
      }}}.
  Proof.
    iIntros (Φ) "(H & H1 & %H2) H4". unfold sortedInsert. wp_pures.
    wp_apply (wp_BinarySearch with "[$H $H1]"); auto.
    iIntros (i) "(H & H1 & %H4 & %H5 & %H6 & %H7)". wp_pures.
    iDestruct (op_versionVector_len with "H") as "%v_len"; auto.
    unfold is_operation.
    unfold operation_slice.
    unfold operation_slice'.
    iNamed "H".
    iDestruct "H" as "[H H2]".
    iDestruct (big_sepL2_length with "H2") as %len.
    iDestruct (own_slice_sz with "H") as %Hsz.
    assert (length l = uint.nat s.(Slice.sz)) by word.
    unfold slice.len. wp_pures.
    remember i.
    wp_if_destruct.
    - unfold operation_val. wp_pures. 
      wp_apply (wp_SliceAppend with "[$]"); auto.
      iIntros (s') "H".
      iApply "H4".
      iExists (l ++ [v]).
      iDestruct "H1" as "(%H1 & %H3 & H3)".
      iSplitL.
      + iExists (ops ++ [opv]).
        iFrame.
        unfold is_operation.
        auto.
      + apply (implies_Sorted l v (length l)) in H2; try word.
        * iPureIntro.
          unfold insert.
          replace (uint.nat (W64 (length l))) with (length l)%nat in H2 by word.
          rewrite <- H in H5.  rewrite <- H in H6.
          clear H7.
          clear len.
          clear Hsz.
          clear H.
          induction l; try auto.
          assert (coq_lexicographicCompare v.(Operation.VersionVector) a.(Operation.VersionVector) = true
                                                                                \/ coq_equalSlices v.(Operation.VersionVector) a.(Operation.VersionVector) = true). { 
            assert (0 < S (length l))%nat by word.
            eapply H2 in H.
            eapply H.
            - auto.
            - simpl. simpl. rewrite lookup_app_r.
              + rewrite length_take_le; try word. 
              replace (length l - length l)%nat with 0%nat by word.
              simpl. auto.
              + rewrite length_take_le; try word.
          }
          assert (length v.(Operation.VersionVector) = length a.(Operation.VersionVector)). {
            rewrite <- H3. symmetry. eapply v_len.
            + assert ((a :: l) !! 0%nat = Some a) by auto. eassumption.
          }
          destruct H.
          { apply aux1_lexicographicCompare in H.
            - assert (l ++ [v] = coq_sortedInsert l v). {
                apply IHl.
                - unfold is_sorted.
                  intros. unfold is_sorted in H2. eapply H2.
                  + assert ((S i < S j)%nat) by word. eassumption.
                  + auto.
                  + auto.
                - unfold is_sorted. intros.
                  unfold is_sorted in H4.
                  assert ((S i < S j)%nat) by word.
                  eapply H4.
                  + apply H10.
                  + auto.
                  + auto.
                - intros. eapply H5.
                  + assert (S i' < S (length l)) by word.
                    assert (length (a :: l) = S (length l)). {
                      rewrite length_cons. auto. }
                    rewrite H10. eassumption.
                  + auto.
                - intros. eapply H6.
                  + assert (S (length l) ≤ S j') by word.
                    assert (length (a :: l) = S (length l)). {
                      rewrite length_cons. auto. }
                    rewrite H10. eassumption.
                  + simpl. auto.
                - intros. eapply v_len. assert ((a :: l) !! S i = Some e). { simpl. auto. }
                  eassumption. 
              }
              rewrite <- app_comm_cons. unfold coq_sortedInsert. rewrite H.
              simpl. fold coq_sortedInsert. rewrite H7. auto.
            - auto.
            - destruct (decide (v.(Operation.VersionVector) = a.(Operation.VersionVector))).
              + subst. apply aux4_lexicographicCompare in H. eapply aux1_equalSlices; eassumption.
              + auto.
          }
          { - apply aux2_equalSlices in H; try auto.
              eapply aux5_lexicographicCompare in H. assert (l ++ [v] = coq_sortedInsert l v). {
                apply IHl.
                - unfold is_sorted.
                  intros. unfold is_sorted in H2. eapply H2.
                  + assert ((S i < S j)%nat) by word. eassumption.
                  + auto.
                  + auto.
                - unfold is_sorted. intros.
                  unfold is_sorted in H4.
                  assert ((S i < S j)%nat) by word.
                  eapply H4.
                  + apply H10.
                  + auto.
                  + auto.
                - intros. eapply H5.
                  + assert (S i' < S (length l)) by word.
                    assert (length (a :: l) = S (length l)). {
                      rewrite length_cons. auto. }
                    rewrite H10. eassumption.
                  + auto.
                - intros. eapply H6.
                  + assert (S (length l) ≤ S j') by word.
                    assert (length (a :: l) = S (length l)). {
                      rewrite length_cons. auto. }
                    rewrite H10. eassumption.
                  + simpl. auto.
                - intros. eapply v_len. assert ((a :: l) !! S i = Some e). { simpl. auto. }
                  eassumption. 
              }
              rewrite <- app_comm_cons. unfold coq_sortedInsert.
              simpl. fold coq_sortedInsert. rewrite H7. rewrite H. auto.
          }
        * intros. eapply H5.
          { assert (i' < length l) by word. rewrite <- H.
            eassumption. }
          { auto. }
        * intros. eapply H6.
          { assert (length l <= j') by word. rewrite <- H.
            eassumption. }
          { auto. }
    - wp_bind (SliceAppendSlice _ _ _).
      wp_apply wp_SliceSkip; try word.
      unfold own_slice.
      unfold slice.own_slice.
      iDestruct (own_slice_wf with "H") as %Hcap.
      iDestruct "H1" as "(%H1 & %H3 & H3)".
      iDestruct "H" as "[H H5]".
      iDestruct (slice_small_split with "H") as "H".
      + assert (uint.Z i <= length ops) by word.
        eassumption.
      + iDestruct "H" as "[H H6]".
        wp_apply slice.wp_SliceSingleton; auto.
        iIntros (s0) "H7".
        wp_apply (wp_SliceAppendSlice with "[H7 H6]"); try auto.
        * unfold own_slice. iSplitL "H7".
          -- assert (list.untype [opv] = cons (operation_val opv) []). {
               auto.
             }
             rewrite <- H0. iFrame.
          -- subst. iFrame.
        * iIntros (s') "[H7 H8]". wp_pures. wp_bind (SliceAppendSlice _ _ _).
          wp_apply wp_SliceTake; try word.
          unfold own_slice. unfold slice.own_slice.
          iDestruct "H7" as "[H7 H9]".
          wp_apply (wp_SliceAppendSlice with "[H8 H5 H7 H]"); try auto.
          -- iAssert (own_slice_small (slice_skip s (slice.T uint64T * (uint64T * unitT)%ht) w)
                        (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) (drop (uint.nat w) ops)
                      ∗ own_slice_cap s (struct.t Operation))%I with "[H8 H5]" as "H1". { subst. iFrame. }
             iSplitL "H H1".
             ++ unfold own_slice. unfold slice.own_slice.
                iSplitR "H1".
                ** unfold own_slice_small. simpl. subst.
                   iFrame.
                ** iApply own_slice_cap_take; try word. iDestruct "H1" as "[H H1]". iFrame.
             ++ iFrame.
          -- iIntros (s'0) "H". wp_pures. iModIntro. iApply "H4".
             iExists (take (uint.nat i) l ++ [#v] ++ drop (uint.nat i) l).
             iSplitL.
             ++ iExists (take (uint.nat i) ops ++ [opv] ++ drop (uint.nat i) ops).
                unfold own_slice. unfold slice.own_slice. iDestruct "H" as "(H & H4)".
                subst. iFrame.
                unfold is_operation. simpl. admit.
             ++ iPureIntro.
                apply (implies_Sorted l v (uint.nat i)) in H2;
                  try word.
                ** clear len.
                   clear Hsz.
                   clear H4.
                   clear Heqb.
                   clear Hcap.
                   clear H.
                   subst.
                   generalize dependent i. induction l.
                   { simpl. intros. rewrite take_nil. rewrite drop_nil. auto. }
                   { intros. unfold insert.
                     destruct (decide (uint.nat i = 0%nat)). 
                     -- rewrite e. rewrite e in H2. simpl.
                        assert (coq_lexicographicCompare a.(Operation.VersionVector) v.(Operation.VersionVector) = true
                               ∨ coq_equalSlices a.(Operation.VersionVector) v.(Operation.VersionVector) = true).
                        { unfold is_sorted in H2.
                          assert (0 < 1)%nat by word. eapply H2.
                          - apply H.
                          - auto.
                          - auto.
                        }
                        destruct H.
                        ++ rewrite H. auto.
                        ++ apply aux5_lexicographicCompare in H as H0. apply aux0_equalSlices in H.
                           ** rewrite H0.
                              assert (take (uint.nat 0) l ++ [#v] ++ drop (uint.nat 0) l = (a :: l)%list). {
                                replace (uint.nat 0) with 0%nat by word.
                                simpl. rewrite drop_0.
                                f_equal. 
                                destruct v.
                                destruct a.
                                simpl in H.
                                subst. admit.
                              }
                              simpl in H3. rewrite take_0 in H3.
                              admit.
                           ** admit.
                     -- assert (H: (exists n, S n = uint.nat i)%nat). {
                          exists (Nat.pred (uint.nat i)). word. }
                        destruct H. 
                        rewrite <- H. simpl.
                        assert (coq_lexicographicCompare v.(Operation.VersionVector) a.(Operation.VersionVector) = true \/ coq_equalSlices v.(Operation.VersionVector) a.(Operation.VersionVector) = true). {
                          unfold is_sorted in H2.
                          eapply H2.
                          - assert (0 < (uint.nat i))%nat by word.
                            apply H0.
                          - replace (uint.nat (W64 (uint.nat i))) with (uint.nat i) by word. rewrite <- H. simpl. auto.
                          - replace (uint.nat (W64 (uint.nat i))) with (uint.nat i) by word. rewrite <- H. simpl. apply list_lookup_middle. rewrite length_take_le;
                              try word. rewrite length_cons in H7. word.
                        }
                        assert (coq_lexicographicCompare a.(Operation.VersionVector) v.(Operation.VersionVector) = false). { admit. }
                        (* 
                            
                        ++ rewrite H3.
                           assert (take (uint.nat x) l ++ [#v] ++ drop (uint.nat x) l = coq_sortedInsert l v). {
                             eapply IHl.
                             - rewrite length_cons in H3. word.
                             - replace (uint.nat (W64 (uint.nat (W64 x)))) with x%nat by word. replace (uint.nat (W64 (S x))) with (S x)%nat in H2 by word. simpl in H2. unfold is_sorted. intros.
                               eapply H2.
                               + assert (S i0 < S j)%nat by word. apply H10.
                               + replace (uint.nat (W64 (uint.nat i))) with
                                   (uint.nat i) by word.
                                 rewrite <- H. auto.
                               + replace (uint.nat (W64 (uint.nat i))) with
                                   (uint.nat i) by word.
                                 rewrite <- H. auto.
                             - rewrite length_cons in H7. word.
                             - intros. eapply H6.
                               + assert (uint.nat i <= S j') by word. apply H9.
                               + auto.
                             - intros. eapply H5.
                               + assert (S i' < uint.nat i) by word. apply H9.
                               + auto.
                           }
                           rewrite <- H4. replace (uint.nat (W64 x)) with x by word.
                           auto.
                   }
                ** intros. eapply H5.
                   { assert (i' < uint.nat w) by word. apply H8. }
                   { auto. }
                ** intros. eapply H6.
                   { assert (uint.nat w <= j') by word. apply H8. }
                   { auto. } *)
  Admitted.
  *)

End heap.
