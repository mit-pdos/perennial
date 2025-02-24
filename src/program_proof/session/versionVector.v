From Perennial.program_proof.session Require Import coq_session.

Section heap.
  Context `{hG: !heapGS Σ}.
               
  Lemma wp_compareVersionVector (x: Slice.t) (xs: list w64) (y: Slice.t)
    (ys: list w64) (d: dfrac) :
    {{{
          own_slice_small x uint64T d xs ∗
          own_slice_small y uint64T d ys ∗
          ⌜length xs = length ys⌝ 
    }}}
      compareVersionVector x y 
      {{{
            r , RET #r;
            ⌜r = coq_compareVersionVector xs ys⌝ ∗
            own_slice_small x uint64T d xs ∗
            own_slice_small y uint64T d ys ∗            
            ⌜length xs = length ys⌝ 
      }}}.
  Proof.
    iIntros (Φ) "(H1 & H2) H3".
    rewrite /compareVersionVector.
    iDestruct (own_slice_small_sz with "H1") as %Hsz.
    wp_pures.
    wp_apply wp_ref_to; auto.
    iIntros (output) "H4". wp_pures.
    wp_apply wp_ref_to; auto.
    iIntros (index) "H5". wp_pures.
    wp_apply wp_slice_len.
    wp_apply wp_ref_to; auto.
    iIntros (l) "H6". wp_pures.
    wp_apply (wp_forBreak_cond
                (λ continue,
                   ∃ (b: bool) (i: w64),
                     "Hx" ∷ own_slice_small x uint64T d xs ∗
                     "Hy" ∷ own_slice_small y uint64T d ys ∗
                     output ↦[boolT] #b ∗
                     index ↦[uint64T] #i ∗
                     l ↦[uint64T] #(length xs) ∗
                     ⌜length xs = length ys⌝ ∗
                     ⌜length xs < 2^64⌝ ∗
                     ⌜∀ (x y: w64),
                   uint.nat i <= length xs ->
                   xs !! (uint.nat i) = Some x ->
                   ys !! (uint.nat i) = Some y ->
                   (uint.Z x) >=? (uint.Z y) = true ->
                   b = true⌝ ∗                   
                   ⌜∀ (i': nat),
                     ∀ (x y: w64),
                   i' < uint.nat i <= length xs ->
                   xs !! i' = Some x ->
                   ys !! i' = Some y ->
                   (uint.Z x) <? (uint.Z y) = true
                   -> b = false⌝ ∗  
                   ⌜uint.Z i <= (uint.Z (length xs))⌝ ∗ 
                   ⌜continue = true -> 
                   b = true⌝ ∗
                   ⌜continue = false ->
                   (exists x y, xs !! (uint.nat i) = Some x /\
                                ys !! (uint.nat i) = Some y /\
                                (uint.Z x) <? (uint.Z y) = true /\ b = false)
                   \/ ((uint.nat i) = (length xs) /\ b = true)⌝ 
                )%I
               with "[] [H1 H4 H2 H5 H6]").
    - iIntros (?).
      iModIntro. iIntros "H1 H2".
      iNamed "H1".
      iDestruct "H1" as "(H3 & H4 & H5 & %H6 & %H7 & %H8 & %H9 & %H10 & %H11 & %H12)".
      wp_pures. wp_load. wp_load. wp_if_destruct.
      + wp_pures. wp_load.
        assert ((uint.nat i < length xs)%nat) by word.
        apply list_lookup_lt in H. destruct H.
        wp_apply (wp_SliceGet with "[$Hx]").
        * iPureIntro. apply H.
        * iIntros "Hx". wp_pures.
          wp_load. assert ((uint.nat i < length ys)%nat) by word.
          eapply list_lookup_lt in H0. destruct H0.
          wp_apply (wp_SliceGet with "[$Hy]").
          { iPureIntro. eassumption. }
          iIntros "Hy". wp_pures. case_bool_decide.
          { wp_pures. wp_store. iModIntro. iApply "H2". iExists false.
            iExists i. iFrame. iPureIntro.
            repeat split; try eauto.
            - intros. rewrite H in H3. rewrite H0 in H4. inversion H3. inversion H4. word.
            - intros. left. exists x0. exists x1.
              split; auto. split; auto.
              apply Z.ltb_lt in H1. 
              auto.
          }
          { wp_pures. wp_load. wp_pures.
            wp_store. iModIntro. 
            iApply "H2". iExists b.
            iExists (w64_word_instance.(word.add) i (W64 1)). iFrame.
            iPureIntro. repeat split; auto.
            - intros. assert (i' <= uint.Z (i)). { rewrite word.unsigned_add in H2. word. }
              destruct (decide (uint.nat i = i')).
              + subst. rewrite H0 in H4. rewrite H in H3. inversion H4. inversion H3. word.
              + assert (i' < uint.nat i) by word. eapply H9; try eassumption.
                word.
            - word.
            - intros. inversion H2.
          } 
      + iModIntro. iApply "H2". iExists b. iExists i. iFrame. iPureIntro.
        repeat split; auto. intros. apply Znot_lt_ge in Heqb0. right.
        destruct H11; auto. split; auto. word.
    - iExists true. iExists (W64 0).
      rewrite Hsz.
      assert (#(W64 (uint.nat x.(Slice.sz))) = #x.(Slice.sz)). {
        f_equal. rewrite w64_to_nat_id. auto. }
      rewrite H.
      iDestruct "H2" as "[H2 H3]".
      iFrame. iPureIntro.
      split. { word. }
      split. { auto. }
      split. { word. }
      split. { word. }
      split. { word. }
      word.
    - iIntros "H".
      iNamed "H". iDestruct "H" as "(H1 & H2 & H8 & %H5 & %H6 &
      %H7 & %H8 & %H9 & %H10 & %H11)".   
      wp_pures. wp_load. iModIntro. iApply "H3". iFrame. iPureIntro.
      clear Hsz.
      assert (uint.nat i <= length xs) by word.
      clear H9.
      generalize dependent ys. generalize dependent i. 
      induction xs.
      + intros.
        simpl in H5.
        symmetry in H5.
        apply nil_length_inv in H5.
        simpl. cbn in *. destruct H11 as [H11 | H12]; auto.
        * destruct H11 as (? & ? & ? & ?). inversion H0.
        * destruct H12. split; auto. rewrite H5. auto.
      + induction ys.
        * intros. inversion H5.
        * intros. simpl. destruct (decide (uint.Z a <? uint.Z a0 = true)).
          { assert (uint.nat a <? uint.nat a0 = true) by word.
            rewrite H0. split; auto.
            rewrite length_cons in H.
            destruct H11; auto.
            - destruct H1 as (? & ? & ? & ? & ? & ?). auto.
            - destruct H1. eapply (H8 0%nat a a0); try eassumption.
              + rewrite H1.
                replace (uint.nat (W64 (length (a :: xs)))) with (length (a :: xs)) by word.
                repeat rewrite length_cons. word.
              + auto.
              + auto.
          }
          { intros. split; auto. assert (uint.nat a <? uint.nat a0 = false) by word.
            rewrite H0.
            assert (uint.nat (uint.nat i - 1%nat)%nat = ((uint.nat i) - 1)%nat) by word.
            eapply IHxs.
            - rewrite length_cons in H6. word.
            - rewrite length_cons in H. 
              assert ((uint.nat i - 1)%nat <= length xs) by word.
              rewrite <- H1 in H2.
              eassumption.
            - auto.
            - intros. rewrite H1 in H3.
              rewrite H1 in H4.
              rewrite H1 in H2.
              destruct (decide (uint.nat i = 0%nat)).
              + eapply H7.
                * auto.
                * rewrite e. auto.
                * rewrite e. auto.
                * word.
              + eapply H7.
                * auto.
                * rewrite lookup_cons_Some. right.
                  assert (1 <= uint.nat i)%nat by word. split; auto. eassumption.
                * rewrite lookup_cons_Some. right.
                  assert (1 <= uint.nat i)%nat by word. split; auto. eassumption.
                * word.
            - intros.
              destruct (decide (i' = 0%nat)).
              + eapply (H8 (i' + 1)%nat).
                * word.
                * subst. simpl. eassumption.
                * subst. simpl. eassumption.
                * word.
              + eapply (H8 (i' + 1)%nat).
                * word.
                * rewrite lookup_cons_Some. right. assert (1 <= i' + 1)%nat by word.
                  assert ((i' + 1 - 1)%nat = i') by word.
                  rewrite H13. split; eassumption.
                * rewrite lookup_cons_Some. right. assert (1 <= i' + 1)%nat by word.
                  assert ((i' + 1 - 1)%nat = i') by word.
                  rewrite H13. split; eassumption.
                * word.
            - intros. destruct H11 as [? | ?]; auto.
              + destruct (decide (uint.nat i = 0%nat)).
                * destruct H3 as (? & ? & ? & ? & ? & ?).
                  subst. rewrite e in H3. rewrite e in H4.
                  simpl in *. inversion H3. inversion H4.
                  subst. word.
                * destruct H3 as (? & ? & ? & ? & ? & ?).
                  rewrite H1.
                  assert (uint.nat i > 0) by word.
                  left.
                  exists x0. exists x1.
                  rewrite lookup_cons_Some in H3.
                  destruct H3 as [? | [? ?]]; try word.
                  rewrite lookup_cons_Some in H4.
                  destruct H4 as [? | [? ?]]; try word.                  
                  split. { eassumption. }
                  split. { eassumption. }
                  split. { word. }
                  auto.
              + destruct H3. rewrite length_cons in H3.
                right.
                split. { rewrite H1. word. }
                eassumption.
          }
  Qed.

  Lemma wp_lexicographicCompare (x: Slice.t) (xs: list u64) (y: Slice.t) (ys: list u64) (d: dfrac) :
    {{{
          own_slice_small x uint64T d xs ∗
          own_slice_small y uint64T d ys ∗
          ⌜length xs = length ys⌝ 
    }}}
      lexicographicCompare x y 
      {{{
            r , RET #r;
            ⌜r = coq_lexicographicCompare xs ys⌝ ∗ 
            own_slice_small x uint64T d xs ∗
            own_slice_small y uint64T d ys ∗
            ⌜length xs = length ys⌝ 
      }}}.
  Proof.
    iIntros (Φ) "(H1 & H2 & %H3) H5".
    rewrite /lexicographicCompare.
    iDestruct (own_slice_small_sz with "H1") as %Hsz.
    wp_pures.
    wp_apply wp_ref_to; auto.
    iIntros (output) "H6".
    wp_pures.
    wp_apply wp_ref_to; auto.
    iIntros (index) "H7". wp_pures.
    wp_apply wp_slice_len.
    wp_apply wp_ref_to; auto.
    iIntros (l) "H8". wp_pures.
    wp_apply (wp_forBreak_cond
                (λ continue, ∃ (b: bool) (i: w64),
                    "Hx" ∷ own_slice_small x uint64T d xs ∗
                    "Hy" ∷ own_slice_small y uint64T d ys ∗
                    output ↦[boolT] #b ∗
                    index ↦[uint64T] #i ∗
                    l ↦[uint64T] #(length xs) ∗
                    ⌜length xs = length ys⌝ ∗                 
                    ⌜∀ (i': nat) (x y: w64),
                   i' < uint.nat i <= length xs ->
                   xs !! i' = Some x ->
                   ys !! i' = Some y ->
                   (uint.Z x) =? (uint.Z y) = true⌝ ∗
                   ⌜uint.nat i <= (length xs)⌝ ∗
                   ⌜continue = true -> b = false⌝ ∗
                   ⌜continue = false ->
                   (uint.nat i = length xs /\ b = false) \/
                     (exists (x y : w64),
                         xs !! uint.nat i = Some x /\
                         ys !! uint.nat i = Some y /\
                         (uint.Z x =? uint.Z y) = false /\
                         b = (uint.Z x >? uint.Z y))⌝ 
                )%I
               with "[] [H1 H2 H6 H7 H8]").
    - iIntros (?). iModIntro. iIntros "H1 H2".
      iNamed "H1". iDestruct "H1" as "(H1 & H3 & H4 & H5 & %H6 & %H7 & %H8 & %H9)".
      wp_load. wp_load.
      wp_if_destruct.
      + wp_pures. wp_load.
        assert (uint.nat i < length xs)%nat by word.
        apply list_lookup_lt in H as [x0 H].
        assert (uint.nat i < length ys)%nat by word.
        apply list_lookup_lt in H0 as [y0 H0].
        wp_apply (wp_SliceGet with "[Hx]"). { iFrame. auto. }
        iIntros "H". wp_load.
        wp_apply (wp_SliceGet with "[Hy]"). { iFrame. auto. }
        iIntros "H9". wp_if_destruct.
        * wp_load. wp_pures. wp_store. iModIntro. iApply "H2".
          iExists b. iExists (w64_word_instance.(word.add) i (W64 1)).
          iFrame. iSplit.
          { iPureIntro. intros. destruct (decide (i' = uint.nat i)).
            - subst. rewrite H in H2. rewrite H0 in H4.
              inversion H2. inversion H4.
              word.
            - replace (uint.nat (w64_word_instance.(word.add) i (W64 1)))
                with (S (uint.nat i)) in H1 by word.
              assert (i' < uint.nat i <= length xs) by word.
              eapply H6; eassumption.
          }
          iSplitL. { word. }
          iSplitL. { auto. }
          iPureIntro. intros. inversion H1.
        * wp_load. wp_apply (wp_SliceGet with "[H9]"). { iFrame. auto. }
          iIntros "H9". wp_load.
          wp_apply (wp_SliceGet with "[H]"). { iFrame. auto. }
          iIntros "H". wp_pures. wp_store. iModIntro. iApply "H2".
          iExists (bool_decide (uint.Z y0 < uint.Z x0)).
          iExists i. iFrame. iPureIntro.
          split. { auto. }
          split. { word. }
          split. { word. }
          intros. right. exists x0. exists y0.
          split. { auto. }
          split. { auto. }
          split. { word. }
          destruct (decide ((uint.Z x0 > uint.Z y0))).
          { assert (uint.Z x0 >? uint.Z y0 = true) by word.
            rewrite H2. apply bool_decide_eq_true. word.
          }
          { assert (uint.Z x0 >? uint.Z y0 = false) by word.
            rewrite H2. 
            apply bool_decide_eq_false. word.
          } 
      + iModIntro. iApply "H2". iExists b. iExists i. iFrame. iPureIntro.
        split. { auto. }
        split. { word. }
        split. { word. }
        intros. left.
        split. { word. }
        auto.
    - iExists false. iExists (W64 0).
      rewrite Hsz.
      replace ((W64 (uint.nat x.(Slice.sz)))) with (x.(Slice.sz)) by word. iFrame.
      iPureIntro.
      repeat split; word.
    - iIntros "Hpost".
      wp_pures. iNamed "Hpost".
      iDestruct "Hpost" as "(H1 & H2 & H3 & %H5 & %H6 & %H7 & %H8 & %H9)".
      wp_load. iModIntro. iApply "H5". iFrame. iSplitL.
      + destruct H9 as [[H9 H10] | ?]; auto.
        * iPureIntro. rewrite /coq_lexicographicCompare.
          clear Hsz. clear H5.
          generalize dependent ys. generalize dependent i. induction xs.
          { auto. }
          { induction ys.
            - auto.
            - intros. clear IHys.
              assert (0%nat < uint.nat i <= length (a :: xs)). {
                rewrite H9. repeat rewrite length_cons. word. }
              assert ((uint.Z a =? uint.Z a0) = true). {
                eapply H6; try eassumption.
                - auto.
                - auto.
              }
              rewrite H0. 
              assert (uint.nat (uint.nat i - 1%nat)%nat = ((uint.nat i) - 1)%nat) by word.
              eapply IHxs.
              + rewrite length_cons in H7.
                assert ((uint.nat i - 1)%nat <= length xs) by word.
                rewrite <- H1 in H2. eassumption.
              + rewrite H1. rewrite length_cons in H9. word.
              + auto.
              + intros.
                eapply H6.
                * assert ((i' + 1)%nat < uint.nat i <= length (a :: xs)) by word.
                  apply H11.
                * simpl. rewrite lookup_cons_Some. right.
                  assert ((i' + 1 - 1)%nat = i') by word.
                  rewrite H11.
                  split; auto. word.
                * simpl. rewrite lookup_cons_Some. right.
                  assert ((i' + 1 - 1)%nat = i') by word.
                  rewrite H11.
                  split; auto. word.
          } 
        * iPureIntro. rewrite /coq_lexicographicCompare.
          clear Hsz. clear H5.
          generalize dependent ys. generalize dependent i. induction xs.
          { intros. destruct H as (? & ? & ? & ?). inversion H. }
          { induction ys.
            - intros. destruct H as (? & ? & ? & ? & ?). inversion H0.
            - clear IHys. intros.
              destruct (decide (uint.nat i = 0%nat)).
              + destruct H as (? & ? & ? & ? & ? & ?).
                rewrite e in H. rewrite e in H0. cbn in *.
                inversion H. inversion H0. subst.
                rewrite H1. auto.
              + assert (0%nat < uint.nat i) by word.
                assert (0%nat < uint.nat i <= length (a :: xs)) by word.
                assert ((uint.Z a =? uint.Z a0) = true). {
                eapply H6; try eassumption.
                - auto.
                - auto.
                }
                rewrite H2.
                assert (uint.nat (uint.nat i - 1%nat)%nat = ((uint.nat i) - 1)%nat) by word.
                eapply IHxs.
                * rewrite length_cons in H7.
                  assert (uint.nat (uint.nat i - 1%nat)%nat <= length xs) by word.
                  eassumption.
                * auto.
                * intros.
                  eapply H6.
                  { assert ((i' + 1)%nat < uint.nat i <= length (a :: xs)) by word.
                    apply H11. }
                  { simpl. rewrite lookup_cons_Some. right.
                  assert ((i' + 1 - 1)%nat = i') by word.
                  rewrite H11.
                  split; auto. word. }
                  { simpl. rewrite lookup_cons_Some. right.
                  assert ((i' + 1 - 1)%nat = i') by word.
                  rewrite H11.
                  split; auto. word. }
                * destruct H as (? & ? & ? & ? & ? & ?). exists x0. exists x1.
                  split.
                  { rewrite H4. rewrite lookup_cons_Some in H.
                    destruct H as [? | [? ?]]; try word. auto. }
                  split.
                  { rewrite H4. rewrite lookup_cons_Some in H5.
                    destruct H5 as [? | [? ?]]; try word. auto. }
                  split. { word. }
                  auto.
          }
      + auto.
  Qed.

  Lemma wp_maxTwoInts (x: w64) (y: w64) :
    {{{
          True
    }}}
      maxTwoInts #x #y 
      {{{
            r , RET #r;
            ⌜r = coq_maxTwoInts x y⌝
      }}}.
  Proof.
    iIntros (Φ) "H H1".
    rewrite /maxTwoInts. wp_pures.
    wp_if_destruct.
    - iModIntro. iApply "H1". iPureIntro.
      unfold coq_maxTwoInts. apply Z.gtb_lt in Heqb.
      rewrite Heqb. auto.
    - iModIntro. iApply "H1". iPureIntro.
      rewrite /coq_maxTwoInts.
      assert (uint.Z y >= uint.Z x) by word.
      assert (uint.Z x >? uint.Z y = false) by word.
      rewrite H0.
      auto.
  Qed.

  Lemma wp_maxTS (x: Slice.t) (xs: list w64) (y: Slice.t) (ys: list w64) (d: dfrac) :
    {{{
          own_slice_small x uint64T d xs ∗
            own_slice_small y uint64T d ys ∗
            ⌜length xs = length ys⌝
    }}}
      maxTS x y 
      {{{
            (s': Slice.t), RET slice_val s'; 
            own_slice s' uint64T (DfracOwn 1) (coq_maxTS xs ys) ∗ 
            own_slice_small x uint64T d xs ∗
            own_slice_small y uint64T d ys 
      }}}.
  Proof.
    iIntros (Φ) "(H & H1 & %H3) H2".
    rewrite /maxTS.
    iDestruct (own_slice_small_sz with "H") as %Hsz_x.
    iDestruct (own_slice_small_sz with "H1") as %Hsz_y.
    wp_pures. wp_apply wp_ref_to; auto.
    iIntros (index) "index". wp_pures.
    wp_pures. wp_apply wp_slice_len.
    wp_apply wp_ref_to; auto.
    iIntros (len) "len". wp_pures.
    wp_bind (NewSlice uint64T (slice.len x)).
    wp_apply wp_slice_len.
    wp_apply wp_new_slice; auto.
    iIntros (s') "s'". 
    wp_apply wp_ref_to; auto.
    iIntros (slice) "slice". wp_pures.
    wp_apply (wp_forBreak_cond
                (λ continue, ∃ (i: w64) (l: list w64),
                    own_slice_small x uint64T d xs ∗
                    own_slice_small y uint64T d ys ∗
                    own_slice s' uint64T (DfracOwn 1) l ∗ 
                    index ↦[uint64T] #i ∗
                    len ↦[uint64T] #(length xs) ∗
                    slice ↦[slice.T uint64T] s' ∗ 
                    ⌜continue = false -> uint.nat i = (length xs)⌝ ∗
                    ⌜length l = length xs⌝ ∗
                    ⌜forall (i': nat),
                   i' < uint.nat i <= length xs ->
                   forall (x y: w64), xs !! i' = Some x ->
                                      ys !! i' = Some y ->
                                      l !! i' = Some (coq_maxTwoInts x y)⌝ ∗
                                      ⌜uint.nat i <= length xs⌝ 
                )%I
               with "[] [H H1 index len s' slice]").
    - iIntros (?). iModIntro. iIntros "H1 H2".
      iNamed "H1". iDestruct "H1"
        as "(Hx & Hy & H4 & H5 & H6 & H7 & %H8 & %H9 & %H10 & %H11)".
      wp_pures. wp_load. wp_load. wp_if_destruct.
      + wp_pures. wp_load.
        wp_bind (maxTwoInts _ _)%E.
        iDestruct "H4" as "[Hs Hsc]".
        assert (uint.nat i < length xs)%nat by word.
        rewrite H3 in H. eapply list_lookup_lt in H.
        destruct H as [x0 H].
        assert (uint.nat i < length xs)%nat by word.
        eapply list_lookup_lt in H0.
        destruct H0 as [y0 H0].
        wp_apply (wp_SliceGet with "[$Hy]"). { auto. }
        iIntros "Hy". wp_load. wp_apply (wp_SliceGet with "[$Hx]"). { auto. }
        iIntros "Hx".
        wp_apply (wp_maxTwoInts). iIntros (r) "%H12".
        wp_load. wp_load.
        wp_apply (wp_SliceSet with "[$Hs]").
        { iPureIntro. eapply lookup_lt_is_Some_2. word. }
        iIntros "H11". wp_pures. wp_load. wp_store. iModIntro.
        iApply "H2". iExists (w64_word_instance.(word.add) i (W64 1)).
        iExists (<[uint.nat i:=r]> l)%E. iFrame.
        iSplit. { auto. }
        iSplit. { iPureIntro. rewrite <- H9. apply length_insert. }
        iSplit. { iPureIntro. intros. destruct (decide (i' = uint.nat i)).
                  - rewrite list_lookup_insert_Some.
                    left.
                    split. { auto. }
                    split. { subst. rewrite H4 in H. rewrite H2 in H0. inversion H. inversion H0.
                             auto. }
                    word.
                  - rewrite Z.lt_le_pred in H1.
                    assert ((Z.pred (uint.nat (w64_word_instance.(word.add) i (W64 1)))) = uint.nat i) by word.
                    rewrite H5 in H1.
                    destruct H1. assert(uint.nat i ≠ i') by word.
                    apply (list_lookup_insert_ne l (uint.nat i) (i') r) in H7.
                    rewrite H7. eapply H10; try eassumption.
                    word.
        }
        word.
      + iModIntro. iApply "H2". iExists i. iExists l. iFrame. iPureIntro. split; auto. word.
    - assert (zero_val uint64T = #(W64 0)). { unfold zero_val. simpl. auto. }
      rewrite H. iExists (W64 0).
      iExists (replicate (uint.nat x.(Slice.sz)) (W64 0))%V.
      iFrame.
      iSplitL "s'". { rewrite /own_slice. rewrite untype_replicate. iFrame. }
      iSplitL "len". { rewrite Hsz_x.
                       assert (#(W64 (uint.nat x.(Slice.sz))) = #x.(Slice.sz)). {
                         f_equal. rewrite w64_to_nat_id. auto. }
                       rewrite H0. iFrame. }
      iPureIntro.
      split. { intros. inversion H0. }
      split. { rewrite length_replicate. auto. }
      split. { intros. word. }
      word.
    - iIntros "H". wp_pures. iNamed "H". iDestruct "H" as "(H1 & H3 & H4 & H5 & H6 & H7 & %H8 & %H9 & %H10 & %H11)".
      wp_load. iModIntro. iApply "H2". iFrame.
      assert (coq_maxTS xs ys = l). {
        clear Hsz_x.
        clear Hsz_y.        
        generalize dependent ys. generalize dependent l. generalize dependent i.
        induction xs.
        + intros. inversion H9. apply nil_length_inv in H0. rewrite H0. auto.
        + induction ys.
          * intros. inversion H3.
          * clear IHys. intros.
            assert (uint.nat (uint.nat i - 1%nat)%nat = ((uint.nat i) - 1)%nat) by word.
            destruct (decide (uint.Z a >? uint.Z a0 = true)).
            { inversion H3.
              assert (0%nat < uint.nat i <= length (a :: xs)). {
                destruct H8; auto. rewrite H3. repeat rewrite length_cons. word. }
              rewrite /coq_maxTS. rewrite /coq_maxTwoInts.
              rewrite e.
              eapply H10 in H0.
              - rewrite <- head_lookup in H0. rewrite head_Some in H0. destruct H0 as [l' H0].
                rewrite H0. f_equal.
                + assert (a = coq_maxTwoInts a a0). { rewrite /coq_maxTwoInts. rewrite e. auto. }
                  eassumption.
                + eapply IHxs.
                  * intros. destruct H8; auto.
                    rewrite length_cons in H3. assert (uint.nat (uint.nat i - 1)%nat = length xs) by word.
                    eassumption.
                  * rewrite H. rewrite length_cons in H11. word.
                  * rewrite length_cons in H9.
                    assert (length l = (1 + length l')%nat). { rewrite H0. simpl. auto. }
                    rewrite H9 in H2. word.
                  * auto.
                  * intros. assert (l !! (S i')%nat = l' !! i'). {
                       rewrite H0. rewrite lookup_cons.
                       auto. }
                    rewrite <- H6.
                    eapply H10.
                    { rewrite length_cons. word. }
                    { rewrite lookup_cons_Some. right. split.
                      - word.
                      - simpl. replace (i' - 0)%nat with i' by word. eassumption.
                    }
                    { rewrite lookup_cons_Some. right. split.
                      - word.
                      - simpl. replace (i' - 0)%nat with i' by word. eassumption.
                    }
              - auto.
              - auto.
            } 
            assert (uint.Z a >? uint.Z a0 = false) by word.
            rewrite /coq_maxTS. assert (a0 = coq_maxTwoInts a a0). { rewrite /coq_maxTwoInts. rewrite H0. auto. }
            rewrite <- H1.
            assert (0%nat < uint.nat i <= length (a :: xs)). {
              destruct H8; auto. rewrite H3. repeat rewrite length_cons. word. }
            eapply H10 in H2.
            { rewrite <- head_lookup in H2. rewrite head_Some in H2. destruct H2 as [l' H2].
              rewrite H2. f_equal.
              - eassumption.
              - eapply IHxs.
                + intros.
                  inversion H3.
                  destruct H8; auto.
                  rewrite length_cons in H3.
                  assert (uint.nat (uint.nat i - 1)%nat = length xs) by word.
                  eassumption.
                + rewrite H. rewrite length_cons in H11. word.
                + rewrite length_cons in H9.
                  assert (length l = (1 + length l')%nat). {  rewrite H2. simpl. auto. }
                  rewrite H9 in H4. word.
                + auto.
                + intros.
                  assert (l !! (S i')%nat = l' !! i').
                  { rewrite H2. rewrite lookup_cons.
                    auto. }
                  rewrite <- H7.
                  eapply H10.
                  * rewrite length_cons. word. 
                  * rewrite lookup_cons_Some. right. split.
                    { word. }
                    { simpl. replace (i' - 0)%nat with i' by word. eassumption. }
                  * rewrite lookup_cons_Some. right. split.
                      { word. }
                      { simpl. replace (i' - 0)%nat with i' by word. eassumption. }
            }
        - auto.
        - auto.
      }
      rewrite H. iFrame.
  Qed.

  Lemma wp_equalSlices (x: Slice.t) (xs: list w64) (y: Slice.t) (ys: list w64)  (d: dfrac):
      {{{
            own_slice_small x uint64T d xs ∗
            own_slice_small y uint64T d ys ∗
            ⌜length xs = length ys⌝ 
      }}}
        equalSlices x y 
        {{{
              r , RET #r;
              ⌜r = coq_equalSlices xs ys⌝ ∗ 
              own_slice_small x uint64T d xs ∗
              own_slice_small y uint64T d ys ∗
              ⌜length xs = length ys⌝
        }}}.
    Proof.
      iIntros (Φ) "(H1 & H2) H3".
      unfold equalSlices.
      wp_pures.
      wp_apply wp_ref_to; auto.
      iIntros (output) "H4". wp_pures.
      wp_apply wp_ref_to; auto.
      iIntros (index) "H5". wp_pures.
      wp_apply wp_slice_len.
      wp_apply wp_ref_to; auto.
      iIntros (l) "H6". wp_pures.
      wp_apply (wp_forBreak_cond
                  (λ continue,
                     ∃ (b: bool) (i: w64),
                       "Hx" ∷ own_slice_small x uint64T d xs ∗
                       "Hy" ∷ own_slice_small y uint64T d ys ∗
                       output ↦[boolT] #b ∗
                       index ↦[uint64T] #i ∗
                       l ↦[uint64T] #(length xs) ∗
                       ⌜length xs = length ys⌝ ∗
                       ⌜length xs < 2^64⌝ ∗
                       ⌜∀ (x y: w64),
                     uint.nat i <= length xs ->
                     xs !! (uint.nat i) = Some x ->
                     ys !! (uint.nat i) = Some y ->
                     (uint.Z x) =? (uint.Z y) = true ->
                     b = true⌝ ∗                   
                     ⌜∀ (i': nat),
                     ∀ (x y: w64),
                     i' < uint.nat i <= length xs ->
                     xs !! i' = Some x ->
                     ys !! i' = Some y ->
                     (uint.Z x) =? (uint.Z y) = false
                     -> b = false⌝ ∗  
                     ⌜uint.Z i <= (uint.Z (length xs))⌝ ∗ 
                     ⌜continue = true -> 
                     b = true⌝ ∗
                     ⌜continue = false ->
                     (exists x y, xs !! (uint.nat i) = Some x /\
                                  ys !! (uint.nat i) = Some y /\
                                  ((uint.Z x) =? (uint.Z y)) = false /\ b = false)
                     \/ ((uint.Z i) = uint.Z (W64 (length xs)) /\ b = true)⌝ 
                  )%I
                 with "[] [H1 H4 H2 H5 H6]").
      - iIntros (?).
        iModIntro. iIntros "H1 H2".
        iNamed "H1".
        iDestruct "H1" as "(H3 & H4 & H5 & %H6 & %H7)".
        destruct H7 as (H7 & H8 & H9 & H10 & H11 & H12).
        wp_pures. wp_load. wp_load. wp_if_destruct.
        + wp_pures. wp_load.
          assert ((uint.nat i < length xs)%nat) by word.
          apply list_lookup_lt in H. destruct H.
          wp_apply (wp_SliceGet with "[$Hx]").
          * iPureIntro. apply H.
          * iIntros "Hx". wp_pures.
            wp_load. assert ((uint.nat i < length ys)%nat) by word.
            eapply list_lookup_lt in H0. destruct H0.
            wp_apply (wp_SliceGet with "[$Hy]").
            { iPureIntro. apply H0. }
            iIntros "Hy". wp_pures. case_bool_decide.
            { wp_pures. wp_load. wp_store. iModIntro. iApply "H2". iExists b.
              iExists (w64_word_instance.(word.add) i (W64 1)).
              iFrame. iPureIntro. split; try word.
              split; try word. split.
              - intros. eapply H11; auto.
              - split.
                + intros. destruct (decide (i' = uint.nat i)).
                  * inversion H1. rewrite e in H3. rewrite e in H4.
                    rewrite H in H3. rewrite H0 in H4. injection H3 as ?.
                    injection H4 as ?. word.
                  * assert (i' < uint.Z (w64_word_instance.(word.add) i (W64 1))) by lia.
                    assert (i' <= uint.nat i). { apply Zlt_succ_le.
                                                 replace (Z.succ (uint.nat i))
                                                   with (uint.Z (w64_word_instance.(word.add) i (W64 1))) by word.
                                                 auto. }
                    assert (i' < uint.nat i <= length xs) by word.
                    eapply H9; try eassumption.
                + split; try word. split; auto. intros. inversion H2.
            }
            { wp_pures. wp_store. iModIntro. iApply "H2". iExists false. iExists i.
              iFrame. iPureIntro. split; auto. split; auto. split.
              - intros. rewrite H in H3. rewrite H0 in H4. injection H3 as ?.
                injection H4 as ?. unfold not in H1.
                assert (x2 = y0) by word. rewrite H13 in H3. rewrite <- H4 in H3.
                rewrite H3 in H1. assert (#x1 = #x1) by word. apply H1 in H14.
                inversion H14.
              - split; auto. split; auto. split; auto. left.
                exists x0. exists x1. split; auto. split; auto.
                split; auto. destruct (decide (x0 = x1)).
                + rewrite e in H1. assert (#x1 = #x1) by auto. unfold not in H1. apply H1 in H3. inversion H3.
                + word.
            }
        + iModIntro. iApply "H2". iExists b. iExists i. iFrame. iPureIntro.
          split; auto. split; auto. split; auto. split; auto. split; auto.
          split; auto. right.
          * split; try word. auto.
      - iDestruct (own_slice_small_sz with "H1") as %Hsz.
        iDestruct "H2" as "[H7 %H8]". 
        iExists true. iExists (W64 0).
        rewrite Hsz.
        assert (#(W64 (uint.nat x.(Slice.sz))) = #x.(Slice.sz)). {
          f_equal. rewrite w64_to_nat_id. auto. }
        rewrite H.
        iFrame. iPureIntro. split; try intros; try word.
        split; try intros; try word.
        split; try word. split; try word.
      - iIntros "H".
        iNamed "H". iDestruct "H" as "(H1 & H2 & H8 & %H5 & %H6)".
        destruct H6 as (H6 & H7 & H8 & H9 & H10 & H11).
        wp_pures. wp_load. iModIntro. iApply "H3". iFrame. iPureIntro. split; auto.
        + unfold coq_equalSlices. assert (uint.nat i <= length xs) by word. clear H9. 
          generalize dependent ys. generalize dependent i.
          induction xs.
          * intros. destruct H11.
            { auto. }
            { destruct H0. destruct H0. destruct H0. inversion H0. }
            { destruct H0. auto. }
          * intros. simpl. induction ys.
            { inversion H5. }
            { destruct (decide ((uint.Z a =? uint.Z a0) = true)).
              - rewrite e. simpl.
                destruct (decide (uint.nat i = 0%nat)).
                + eapply IHxs.
                  * rewrite length_cons in H6. word.
                  * assert (uint.nat 0 <= length xs) by word.
                    apply H0.
                  * auto.
                  * intros. eapply H7.
                    { rewrite length_cons. rewrite e0. word. }
                    { rewrite e0. simpl. auto. }
                    { rewrite e0. simpl. auto. }
                    { auto. }
                  * word.
                  * intros; auto. destruct H11; auto.
                    { destruct H1. destruct H1. rewrite e0 in H1.
                      destruct H1. destruct H2. simpl in H1.
                      simpl in H2. destruct H3.
                      injection H1 as ?. injection H2 as ?. word.
                    }
                    { right. destruct H1. rewrite length_cons in H1.
                      assert (uint.nat i = uint.nat (W64 (S (length xs)))) by word.
                      rewrite e0 in H3.
                      rewrite length_cons in H6.
                      replace (uint.nat (W64 (S (length xs)))) with
                        (S (length xs))%nat in H3 by word.
                      word.
                    }
                + eapply IHxs.
                  * rewrite length_cons in H6. word.
                  * rewrite length_cons in H.
                    assert (uint.nat (uint.nat i - 1) <= length xs) by word.
                    apply H0.
                  * auto.
                  * intros. eapply H7.
                    { rewrite length_cons. word. }
                    { rewrite lookup_cons.
                      assert ((S (uint.nat (W64 (uint.nat i - 1))) = uint.nat i)%nat) by word.
                      rewrite <- H4. apply H1. }
                    { rewrite lookup_cons.
                      assert ((S (uint.nat (W64 (uint.nat i - 1))) = uint.nat i)%nat) by word.
                      rewrite <- H4. apply H2. }
                    { auto. }
                  * intros. eapply H8.
                    { assert ((S i')%nat < uint.nat i ≤ length (a :: xs))
                        by word. apply H4.
                    }
                    { rewrite lookup_cons. simpl. eassumption. }
                    { rewrite lookup_cons. simpl. eassumption. }
                    { auto. }
                  * intros. destruct H11; auto.
                    { left. destruct H1.  destruct H1. destruct H1.
                      destruct H2. exists x0. exists x1.
                      split.
                      - replace (uint.nat (W64 (uint.nat i - 1))) with (Init.Nat.pred (uint.nat i)) by word.
                        rewrite lookup_cons_ne_0 in H1; try word.
                        auto.
                      - split.
                        + replace (uint.nat (W64 (uint.nat i - 1))) with (Init.Nat.pred (uint.nat i)) by word.
                          rewrite lookup_cons_ne_0 in H2; try word.
                          auto.
                        + auto.
                    }
                    { right. rewrite length_cons in H1. destruct H1.
                      split; try word. auto.
                    }
              - assert ((uint.Z a =? uint.Z a0) = false) by word.
                rewrite H0. simpl. destruct H11; auto.
                + destruct H1.  destruct H1. destruct H1. destruct H2.  destruct H3. auto.
                + destruct H1.
                  eapply H8.
                  * rewrite length_cons in H1.
                    rewrite length_cons in H6.
                    assert (uint.nat i = S (length xs)) by word.
                    assert (0%nat < uint.nat i <= length (a :: xs)). { rewrite length_cons. word. } apply H4.
                  * simpl. auto.
                  * simpl. auto.
                  * auto.
            } 
    Qed.

    Lemma wp_oneOffVersionVector (x: Slice.t) (xs: list u64) (y: Slice.t) (ys: list u64) :
    {{{
          own_slice_small x uint64T (DfracOwn 1) xs ∗
          own_slice_small y uint64T (DfracOwn 1) ys ∗
          ⌜length xs = length ys⌝
    }}}
      oneOffVersionVector x y
      {{{ (b: bool) , RET #b ;
          ⌜b = coq_oneOffVersionVector xs ys⌝ ∗
          own_slice_small x uint64T (DfracOwn 1) xs ∗
          own_slice_small y uint64T (DfracOwn 1) ys ∗
          ⌜length xs = length ys⌝ 
      }}}.
  Proof.
    iIntros (Φ) "(Hx & Hy & %H) H2".
    iDestruct (own_slice_small_sz with "Hx") as %Hsz.
    assert (length xs < 2^64) by word.
    rewrite /oneOffVersionVector.
    wp_apply wp_ref_to; auto.
    iIntros (output) "H3".
    wp_apply wp_ref_to; auto.
    iIntros (canApply) "H4".
    wp_apply wp_ref_to; auto.
    iIntros (index) "H5".
    wp_pures.
    wp_apply (wp_slice_len).
    wp_apply wp_ref_to; auto.
    iIntros (l) "H6".
    wp_pures.
    set (loop_step := λ (acc: bool * bool) (element : w64 * w64),
           let (e1, e2) := element in
                 let (output, canApply) := acc in
                 if (canApply && (uint.Z (w64_word_instance.(word.add) e1 (W64 1)) =? uint.Z e2)) then
                   (output && true, false)
                 else
                   if uint.Z e1 >=? uint.Z e2 then
                     (output && true, canApply)
                   else 
                     (false, canApply)).
    set (loop_init := (true, true)).
    wp_apply (wp_forBreak_cond
                ( λ continue, ∃ (b1 b2 : bool) , ∃ (xs_prev xs_next ys_prev ys_next : list u64),
                    own_slice_small x uint64T (DfracOwn 1) xs ∗
                    own_slice_small y uint64T (DfracOwn 1) ys ∗
                    output ↦[boolT] #b1 ∗
                    canApply ↦[boolT] #b2 ∗
                    index ↦[uint64T] #(length xs_prev) ∗
                    l ↦[uint64T] #(length xs) ∗
                    ⌜xs = xs_prev ++ xs_next⌝ ∗
                    ⌜ys = ys_prev ++ ys_next⌝ ∗
                    ⌜length xs_prev = length ys_prev⌝ ∗
                    ⌜continue = false -> xs_next = [] /\ ys_next = []⌝ ∗ 
                    ⌜b1 = fst (fold_left loop_step (zip xs_prev ys_prev) loop_init)⌝ ∗
                    ⌜b2 = snd (fold_left loop_step (zip xs_prev ys_prev) loop_init)⌝ 
                )%I
               with "[] [Hx Hy H3 H4 H5 H6]").
    - iIntros (Φ'). iModIntro. iIntros "(%b1 & %b2 & %xs_prev & %xs_next & %ys_prev & %ys_next & Hxs & Hys & H2
& H3 & H4 & H5 & %H6 & %H7 & %H8 & %H9 & %H10 & %H11) H_ret".
      wp_load. wp_load. wp_if_destruct.
      + wp_load. wp_bind (if: #b2 then _ else _)%E.
        wp_if_destruct.
        * assert (length xs_prev <= length xs). {
            rewrite H6. rewrite length_app. word. }
          assert (uint.nat (length xs_prev) < length xs)%nat by word.
          assert (uint.nat (length xs_prev) < length ys)%nat by word.
          apply list_lookup_lt in H2 as [x0 H2].
          apply list_lookup_lt in H3 as [y0 H3].
          wp_load. wp_apply (wp_SliceGet with "[Hxs]"); iFrame; auto.
          iIntros "Hxs". wp_load. wp_apply (wp_SliceGet with "[Hys]"); iFrame; auto.
          iIntros "Hys". wp_pures.
          wp_if_destruct.
          { wp_store. wp_load. wp_store. iModIntro. iApply "H_ret".
            - iExists (fold_left loop_step (zip xs_prev ys_prev)
                             loop_init).1.
              iExists false. 
              iExists (xs_prev ++ [x0]).
              iExists (drop 1 xs_next).
              iExists (ys_prev ++ [(w64_word_instance.(word.add) x0 (W64 1))]).
              iExists (drop 1 ys_next).
              iFrame.
              iSplitL. { rewrite length_app. simpl.
                         assert (w64_word_instance.(word.add) (W64 (length xs_prev)) (W64 1)
                                 = (W64 (length xs_prev + 1)%nat)) by word.
                         rewrite H4. auto. }
              iPureIntro.
              assert (xs_next !! 0%nat = Some x0). { 
                rewrite lookup_app_r in H2.
                - assert ((uint.nat (W64 (length xs_prev)) - length xs_prev)%nat = 0%nat)
                    by word.
                  rewrite H4 in H2. auto. 
                - word.
              }
              assert (head xs_next = Some x0). { rewrite lookup_app_r in H2.
                                                 - rewrite head_lookup. auto.
                                                 - word. }
              split. { apply head_Some in H5 as [l' H5]. rewrite H5. simpl. rewrite drop_0.
                       rewrite cons_middle. rewrite app_assoc. auto. }
              assert (ys_next !! 0%nat = Some (w64_word_instance.(word.add) x0 (W64 1))). { 
                rewrite lookup_app_r in H3.
                - assert ((uint.nat (W64 (length xs_prev)) - length ys_prev)%nat = 0%nat)
                    by word.
                  rewrite H6 in H3. auto. 
                - word.
              }
              assert (head ys_next = Some (w64_word_instance.(word.add) x0 (W64 1))).
              { rewrite lookup_app_r in H3.
                - rewrite head_lookup. auto.
                - word. }
              split. { apply head_Some in H7 as [l' H7]. rewrite H7. simpl. rewrite drop_0.
                       rewrite cons_middle. rewrite app_assoc. auto. }
              split. { repeat rewrite length_app. simpl. auto. }
              assert ((zip (xs_prev ++ [x0]) (ys_prev ++ [w64_word_instance.(word.add) x0 (W64 1)])) = zip xs_prev ys_prev ++ zip [x0] [w64_word_instance.(word.add) x0 (W64 1)]). {
                rewrite zip_with_app; auto. }
              rewrite H10.
              split. { intros. inversion H12. }
              split. { 
                rewrite fold_left_app.
                destruct (fold_left loop_step (zip xs_prev ys_prev) loop_init) as [ind ?].
                unfold loop_step.
                simpl. 
                assert (uint.Z (w64_word_instance.(word.add) x0 (W64 1)) =? uint.Z (w64_word_instance.(word.add) x0 (W64 1))
                        = true) by word.
                rewrite H12. simpl in H11. rewrite <- H11. simpl.
                rewrite andb_true_r. auto. }
              rewrite fold_left_app.
              destruct (fold_left loop_step (zip xs_prev ys_prev) loop_init) as [ind ?].
              unfold loop_step.
              simpl.
              assert (uint.Z (w64_word_instance.(word.add) x0 (W64 1)) =? uint.Z (w64_word_instance.(word.add) x0 (W64 1))
                        = true) by word.
              rewrite H12. simpl in H11. rewrite <- H11.
              auto.
          }
          { wp_load. wp_apply (wp_SliceGet with "[Hxs]"); iFrame; auto.
            iIntros "Hxs". wp_load.
            wp_apply (wp_SliceGet with "[Hys]"); iFrame; auto.
            iIntros "Hys". wp_pures. wp_if_destruct.
            - wp_store. wp_load.
              wp_store. iModIntro. iApply "H_ret".
              iExists false. iExists true. 
              iExists (xs_prev ++ [x0]). iExists (drop 1 xs_next).
              iExists (ys_prev ++ [y0]). iExists (drop 1 ys_next).
              iFrame.
              iSplitL. { rewrite length_app. simpl.
                         assert (w64_word_instance.(word.add) (W64 (length xs_prev)) (W64 1)
                                 = (W64 (length xs_prev + 1)%nat)) by word.
                         rewrite H4. auto. }
              iPureIntro.
              rewrite H6 in H2.
              assert (xs_next !! 0%nat = Some x0). { 
                rewrite lookup_app_r in H2.
                - assert ((uint.nat (W64 (length xs_prev)) - length xs_prev)%nat = 0%nat)
                    by word.
                  rewrite H4 in H2. auto. 
                - word.
              }
              assert (head xs_next = Some x0). { rewrite lookup_app_r in H2.
                                                 - rewrite head_lookup. auto.
                                                 - word. }
              split. { rewrite H6.
                       apply head_Some in H5 as [l' H5]. rewrite H5. simpl. rewrite drop_0.
                       rewrite cons_middle. rewrite app_assoc. auto. }
              rewrite H7 in H3.
              assert (ys_next !! 0%nat = Some (y0)). { 
                rewrite lookup_app_r in H3.
                - assert ((uint.nat (W64 (length xs_prev)) - length ys_prev)%nat = 0%nat)
                    by word. rewrite H12 in H3. auto.
                - word.
              }
              assert (head ys_next = Some (y0)).
              { rewrite lookup_app_r in H3.
                - rewrite head_lookup. auto.
                - word. }
              split. { rewrite H7.
                       apply head_Some in H13 as [l' H13]. rewrite H13. simpl. rewrite drop_0.
                       rewrite cons_middle. rewrite app_assoc. auto. }
              split. { repeat rewrite length_app. simpl. auto. }
              split. { intros. inversion H14. }
              assert ((zip (xs_prev ++ [x0]) (ys_prev ++ [y0])) =
                      zip xs_prev ys_prev ++ zip [x0] [y0]). {
                rewrite zip_with_app; auto. }
              rewrite H14.
              split. {
                rewrite fold_left_app.
                destruct (fold_left loop_step (zip xs_prev ys_prev) loop_init) as [ind ?].
                unfold loop_step.
                simpl.
                apply w64_val_neq in Heqb1 as [? ?].
                apply Z.eqb_neq in H15.
                rewrite H15.
                simpl in H11. rewrite <- H11. simpl. assert (uint.Z x0 >=? uint.Z y0 = false)
                                                       by word.
                rewrite H17. auto.
              }
              rewrite fold_left_app.
              destruct (fold_left loop_step (zip xs_prev ys_prev) loop_init) as [ind ?].
              unfold loop_step.
              simpl.
              apply w64_val_neq in Heqb1 as [? ?].
              apply Z.eqb_neq in H15.
              rewrite H15.
              simpl in H11. rewrite <- H11. simpl. assert (uint.Z x0 >=? uint.Z y0 = false)
                                                     by word.
              rewrite H17. auto.
            - wp_load. wp_store. iModIntro.
              iApply "H_ret".
              iExists b1. iExists true. 
              iExists (xs_prev ++ [x0]). iExists (drop 1 xs_next).
              iExists (ys_prev ++ [y0]). iExists (drop 1 ys_next).
              iFrame.
              iSplitL. { rewrite length_app. simpl.
                         assert (w64_word_instance.(word.add) (W64 (length xs_prev)) (W64 1)
                                 = (W64 (length xs_prev + 1)%nat)) by word.
                         rewrite H4. auto. }
              iPureIntro.
              rewrite H6 in H2.
              assert (xs_next !! 0%nat = Some x0). { 
                rewrite lookup_app_r in H2.
                - assert ((uint.nat (W64 (length xs_prev)) - length xs_prev)%nat = 0%nat)
                    by word.
                  rewrite H4 in H2. auto. 
                - word.
              }
              assert (head xs_next = Some x0). { rewrite lookup_app_r in H2.
                                                 - rewrite head_lookup. auto.
                                                 - word. }
              split. { rewrite H6.
                       apply head_Some in H5 as [l' H5]. rewrite H5. simpl. rewrite drop_0.
                       rewrite cons_middle. rewrite app_assoc. auto. }
              rewrite H7 in H3.
              assert (ys_next !! 0%nat = Some (y0)). { 
                rewrite lookup_app_r in H3.
                - assert ((uint.nat (W64 (length xs_prev)) - length ys_prev)%nat = 0%nat)
                    by word. rewrite H12 in H3. auto.
                - word.
              }
              assert (head ys_next = Some (y0)).
              { rewrite lookup_app_r in H3.
                - rewrite head_lookup. auto.
                - word. }
              split. { rewrite H7.
                       apply head_Some in H13 as [l' H13]. rewrite H13. simpl. rewrite drop_0.
                       rewrite cons_middle. rewrite app_assoc. auto. }
              split. { repeat rewrite length_app. simpl. auto. }
              split. { intros. inversion H14. }
              assert ((zip (xs_prev ++ [x0]) (ys_prev ++ [y0])) =
                      zip xs_prev ys_prev ++ zip [x0] [y0]). {
                rewrite zip_with_app; auto. }
              rewrite H14.
              split. {
                rewrite fold_left_app.
                destruct (fold_left loop_step (zip xs_prev ys_prev) loop_init) as [ind ?].
                unfold loop_step.
                simpl. 
                apply w64_val_neq in Heqb1 as [? ?].
                apply Z.eqb_neq in H15.
                rewrite H15. 
                simpl in H11. rewrite <- H11. simpl. assert (uint.Z x0 >=? uint.Z y0 = true)
                                                       by word.
                rewrite H17. simpl. rewrite H10. simpl. rewrite andb_true_r. auto.
              }
              rewrite fold_left_app.
              destruct (fold_left loop_step (zip xs_prev ys_prev) loop_init) as [ind ?].
              unfold loop_step.
              simpl. apply w64_val_neq in Heqb1 as [? ?].
              apply Z.eqb_neq in H15.
              rewrite H15. 
              simpl in H11. rewrite <- H11. simpl. assert (uint.Z x0 >=? uint.Z y0 = true)
                                                     by word. 
              rewrite H17. auto.
          }
        * assert (length xs_prev <= length xs). {
            rewrite H6. rewrite length_app. word. }
          assert (uint.nat (length xs_prev) < length xs)%nat by word.
          assert (uint.nat (length xs_prev) < length ys)%nat by word.
          apply list_lookup_lt in H2 as [x0 H2].
          apply list_lookup_lt in H3 as [y0 H3].
          wp_pures. wp_load.  wp_apply (wp_SliceGet with "[Hxs]"); iFrame; auto.
          iIntros "Hxs". wp_load.
          wp_apply (wp_SliceGet with "[Hys]"); iFrame; auto.
          iIntros "Hys". wp_pures.
          wp_if_destruct.
          { wp_store. wp_load. wp_store. iModIntro.
            iApply "H_ret".
            iExists false. iExists false. 
              iExists (xs_prev ++ [x0]). iExists (drop 1 xs_next).
              iExists (ys_prev ++ [y0]). iExists (drop 1 ys_next).
              iFrame.
              iSplitL. { rewrite length_app. simpl.
                         assert (w64_word_instance.(word.add) (W64 (length xs_prev)) (W64 1)
                                 = (W64 (length xs_prev + 1)%nat)) by word.
                         rewrite H4. auto. }
              iPureIntro.
              rewrite H6 in H2.
              assert (xs_next !! 0%nat = Some x0). { 
                rewrite lookup_app_r in H2.
                - assert ((uint.nat (W64 (length xs_prev)) - length xs_prev)%nat = 0%nat)
                    by word.
                  rewrite H4 in H2. auto. 
                - word.
              }
              assert (head xs_next = Some x0). { rewrite lookup_app_r in H2.
                                                 - rewrite head_lookup. auto.
                                                 - word. }
              split. { rewrite H6.
                       apply head_Some in H5 as [l' H5]. rewrite H5. simpl. rewrite drop_0.
                       rewrite cons_middle. rewrite app_assoc. auto. }
              rewrite H7 in H3.
              assert (ys_next !! 0%nat = Some (y0)). { 
                rewrite lookup_app_r in H3.
                - assert ((uint.nat (W64 (length xs_prev)) - length ys_prev)%nat = 0%nat)
                    by word. rewrite H12 in H3. auto.
                - word.
              }
              assert (head ys_next = Some (y0)).
              { rewrite lookup_app_r in H3.
                - rewrite head_lookup. auto.
                - word. }
              split. { rewrite H7.
                       apply head_Some in H13 as [l' H13]. rewrite H13. simpl. rewrite drop_0.
                       rewrite cons_middle. rewrite app_assoc. auto. }
              split. { repeat rewrite length_app. simpl. auto. }
              split. { intros. inversion H14. }
              assert ((zip (xs_prev ++ [x0]) (ys_prev ++ [y0])) =
                      zip xs_prev ys_prev ++ zip [x0] [y0]). {
                rewrite zip_with_app; auto. }
              rewrite H14.
              split. {
                rewrite fold_left_app.
                destruct (fold_left loop_step (zip xs_prev ys_prev) loop_init) as [ind ?].
                unfold loop_step.
                simpl in H11. simpl. rewrite <- H11. simpl.
                assert (uint.Z x0 >=? uint.Z y0 = false) by word.
                rewrite H15. auto.
              }
              rewrite fold_left_app.
              destruct (fold_left loop_step (zip xs_prev ys_prev) loop_init) as [ind ?].
              unfold loop_step. simpl.
              simpl in H11. rewrite <- H11. simpl. assert (uint.Z x0 >=? uint.Z y0 = false)
                                                     by word.
              rewrite H15. auto.
          }
          { wp_load. wp_store. iModIntro.
            iApply "H_ret".
            iExists b1. iExists false. 
            iExists (xs_prev ++ [x0]). iExists (drop 1 xs_next).
            iExists (ys_prev ++ [y0]). iExists (drop 1 ys_next).
            iFrame.
            iSplitL. { rewrite length_app. simpl.
                         assert (w64_word_instance.(word.add) (W64 (length xs_prev)) (W64 1)
                                 = (W64 (length xs_prev + 1)%nat)) by word.
                         rewrite H4. auto. }
            iPureIntro.
            rewrite H6 in H2.
              assert (xs_next !! 0%nat = Some x0). { 
                rewrite lookup_app_r in H2.
                - assert ((uint.nat (W64 (length xs_prev)) - length xs_prev)%nat = 0%nat)
                    by word.
                  rewrite H4 in H2. auto. 
                - word.
              }
              assert (head xs_next = Some x0). { rewrite lookup_app_r in H2.
                                                 - rewrite head_lookup. auto.
                                                 - word. }
              split. { rewrite H6.
                       apply head_Some in H5 as [l' H5]. rewrite H5. simpl. rewrite drop_0.
                       rewrite cons_middle. rewrite app_assoc. auto. }
              rewrite H7 in H3.
              assert (ys_next !! 0%nat = Some (y0)). { 
                rewrite lookup_app_r in H3.
                - assert ((uint.nat (W64 (length xs_prev)) - length ys_prev)%nat = 0%nat)
                    by word. rewrite H12 in H3. auto.
                - word.
              }
              assert (head ys_next = Some (y0)).
              { rewrite lookup_app_r in H3.
                - rewrite head_lookup. auto.
                - word. }
              split. { rewrite H7.
                       apply head_Some in H13 as [l' H13]. rewrite H13. simpl. rewrite drop_0.
                       rewrite cons_middle. rewrite app_assoc. auto. }
            split. { repeat rewrite length_app. simpl. auto. }
            split. { intros. inversion H14. }
            assert ((zip (xs_prev ++ [x0]) (ys_prev ++ [y0])) =
                    zip xs_prev ys_prev ++ zip [x0] [y0]). {
              rewrite zip_with_app; auto. }
            rewrite H14.
            split. {
              rewrite fold_left_app.
              destruct (fold_left loop_step (zip xs_prev ys_prev) loop_init) as [ind ?].
              unfold loop_step.
              simpl in H11. simpl. rewrite <- H11. simpl.
              assert (uint.Z x0 >=? uint.Z y0 = true) by word.
              rewrite H15. rewrite H10. simpl. rewrite andb_true_r. auto.
            }
            rewrite fold_left_app.
            destruct (fold_left loop_step (zip xs_prev ys_prev) loop_init) as [ind ?].
            unfold loop_step. simpl.
            simpl in H11. rewrite <- H11. simpl. assert (uint.Z x0 >=? uint.Z y0 = true)
                                                   by word.
            rewrite H15. auto.
          }
      + iModIntro. iApply "H_ret". iExists b1. iExists b2. iExists xs. iExists [].
        iExists ys. iExists []. iFrame.
        assert (length xs_prev >= length xs) by word.
        assert (length xs = length xs_prev + length xs_next)%nat. { rewrite H6.
                                                                    rewrite app_length. auto. }
        assert (length xs_prev = length xs) by word.
        assert (length xs_next = 0%nat) by word.
        apply length_zero_iff_nil in H4.
        rewrite H4 in H6. 
        assert (xs = xs_prev). {
          rewrite app_nil_r in H6. auto. }
        assert (length ys_prev >= length ys) by word.
        assert (length ys = length ys_prev + length ys_next)%nat. { rewrite H7.
                                                                    rewrite app_length. auto. }
        assert (length ys_prev = length ys) by word.
        assert (length ys_next = 0%nat) by word.
        apply length_zero_iff_nil in H15.
        rewrite H15 in H7.
        assert (ys = ys_prev). {
          rewrite app_nil_r in H7. auto. }
        iSplitL. { rewrite H5. auto. }
        iPureIntro.
        split. { rewrite app_nil_r. auto. }
        split. { rewrite app_nil_r. auto. }
        split. { auto. }
        split. { auto. }
        split. { rewrite H5. rewrite H16. auto. }
        rewrite H5. rewrite H16. auto.
    - iExists true. iExists true. 
      iExists []. iExists xs. iExists []. iExists ys.
      iFrame. rewrite Hsz.
      iSplitL; auto. assert (x.(Slice.sz) = (W64 (uint.nat x.(Slice.sz)))) by word.
      rewrite <- H1. iFrame.
    - iIntros "(%b1 & %b2 & %xs_prev & %xs_next & %ys_prev & %ys_next & Hxs & Hys & H3 & H4 & H5 & H6 & %H7 & %H8 & %H9 & %H10 & %H11 & %H12)".
      wp_load. wp_if_destruct.
      + wp_load. wp_pures. iModIntro. iApply "H2".
        iFrame. iSplitL; auto.
        iPureIntro.
        destruct H10; auto.
        rewrite H1 in H7. rewrite H2 in H8. rewrite app_nil_r in H7. rewrite app_nil_r in H8. 
        rewrite H7. rewrite H8.
        unfold coq_oneOffVersionVector.
        fold loop_step.
        replace (true, true) with loop_init by auto.
        destruct (fold_left loop_step (zip xs_prev ys_prev) loop_init) as [ind ?].
        simpl in *. rewrite <- H11. rewrite andb_true_l. rewrite H12. auto.
      + wp_pures. iModIntro. iApply "H2".
        iFrame. iSplitL; auto.
        iPureIntro.
        destruct H10; auto.
        rewrite H1 in H7. rewrite H2 in H8. rewrite app_nil_r in H7. rewrite app_nil_r in H8. 
        rewrite H7. rewrite H8.
        unfold coq_oneOffVersionVector.
        fold loop_step.
        replace (true, true) with loop_init by auto.
        destruct (fold_left loop_step (zip xs_prev ys_prev) loop_init) as [ind ?].
        simpl in *. rewrite <- H11. rewrite andb_false_l. auto.
  Qed. 
    
End heap.

