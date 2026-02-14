From New.generatedproof Require Import slices.
From New.proof Require Import proof_prelude.
From New.proof.slices_proof Require Import slices_init.
From New.proof.slices_proof.pdqSort Require Import sort_basics.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : slices.Assumptions}.

Context `[!ZeroVal E] `[!TypedPointsto E] `[!IntoValTyped E Et].
Context (R: E → E → Prop) `{!StrictWeakOrder R} `{!RelDecision R}.
Collection W := sem + package_sem + IntoValTyped0.

#[local] Infix "≺" := R (at level 70).
#[local] Notation "x ≽ y" := (¬ R x y) (at level 70, only parsing).

Definition is_heap_seg (xs: list E) (a b: nat) (l r: nat) :=
  forall i (xi xls xrs: E), (l <= i < r)%nat -> xs !! (a + i)%nat = Some xi ->
    ((l <= 2 * i + 1 < r  ->  xs !! (a + 2 * i + 1)%nat = Some xls -> xi ≽ xls) ∧
    (l <= 2 * i + 2 < r  ->  xs !! (a + 2 * i + 2)%nat = Some xrs -> xi ≽ xrs)).


Lemma heap_seg_shrink:
  forall xs a b l r,
  is_heap_seg xs a b l (r + 1)%nat ->
  is_heap_seg xs a b l r.
Proof.
  unfold is_heap_seg. intros.
  destruct (H i xi xls xrs); eauto; try lia.
  split; intros.
  - apply H2; eauto. lia.
  - apply H3; eauto. lia.
Qed.


Lemma heap_top_greatest:
  forall xs xtop xi a b i lim,
  is_heap_seg xs a b 0 (lim + 1) ->
  xs !! a%nat = Some xtop ->
  xs !! (a + i)%nat = Some xi ->
  (0 <= i <= lim)%nat ->
  (length xs >= a + lim)%nat ->
  xtop ≽ xi.
Proof using StrictWeakOrder0.
  intros. generalize dependent i.
  generalize dependent xi. induction lim.
  - intros. assert(i = 0%nat) by lia. inv H4.
    rewrite Nat.add_0_r in H1.
    rewrite H0 in H1. inv H1.
    apply notR_refl; auto.
  - intros. destruct (Nat.eq_dec i (S lim)).
    + subst i. set (par := (lim / 2)%nat).
      assert((2%nat * par)%nat + 1%nat = (S lim) ∨ (2%nat * par)%nat + 2%nat = (S lim)).
      { unfold par.
        pose proof (Nat.div_mod lim 2).
        destruct (lim `mod` 2)%nat eqn: Heq1.
        - lia.
        - destruct n eqn: Heq2.
          + lia.
          + pose proof (Nat.mod_upper_bound lim 2). lia.
      }
      assert((par <= lim)%nat); try lia.
      assert(∃ xpar, xs !! (a + par)%nat = Some xpar). { apply list_lookup_lt. lia. }
      destruct H6 as [xpar Hpar]. apply (notR_trans R xi xpar xtop).
      * eapply IHlim; eauto; try lia.
        apply heap_seg_shrink.
        replace (lim + 1 + 1)%nat with (S lim + 1)%nat by lia.
        auto.
      * destruct (H par xpar xi xi); eauto; try lia.
        destruct H4.
        -- apply H6; try lia. replace (a + 2 * par + 1)%nat with (a + (S lim))%nat by lia. auto.
        -- apply H7; try lia. replace (a + 2 * par + 2)%nat with (a + (S lim))%nat by lia. auto.

    + assert ((i <= lim)%nat); try lia.
      eapply IHlim; eauto; try lia.
      apply heap_seg_shrink.
      replace (lim + 1 + 1)%nat with (S lim + 1)%nat by lia.
      auto.
Qed.



Lemma wp_siftDownCmpFunc (data: slice.t) (lo hi a b: w64) (cmp_code: func.t)
                       (xs: list E):
  {{{ is_pkg_init slices ∗
      "Hxs" ∷ data ↦* xs ∗
      "#Hcmp" ∷ cmp_implements R cmp_code ∗
      "%H_bounds" ∷ ⌜ 0 ≤ sint.Z a ∧ sint.Z a <= sint.Z a + sint.Z lo ∧
                      sint.Z a + sint.Z lo < sint.Z a + sint.Z hi ∧
                      sint.Z a + sint.Z hi <= sint.Z b ∧
                      sint.Z b <= length xs ∧
                      length xs <= 2 ^ 62⌝ ∗
      "%HSegSorted" ∷ ⌜ ∀ i j (xi xj: E), (i < j)%nat ∧ sint.nat a + sint.nat hi <= j ∧
                  (sint.nat a <= j < sint.nat b)%nat ∧
                  (sint.nat a <= i < sint.nat b)%nat ->
                  xs !! i = Some xi ->
                  xs !! j = Some xj -> xj ≽ xi ⌝ ∗
      "%Heap" ∷ ⌜ is_heap_seg xs (sint.nat a) (sint.nat b) (sint.nat lo + 1)%nat (sint.nat hi) ⌝
  }}}
    #(functions slices.siftDownCmpFunc [Et]) #data #lo #hi #a #cmp_code
  {{{ (xs': list E), RET #();
      "Hxs" ∷ data ↦* xs' ∗
      "%HPermPost" ∷ ⌜ Permutation xs xs' ⌝ ∗
      "%HSegSortedPost" ∷ ⌜ ∀ i j (xi xj: E), (i < j)%nat ∧ sint.nat a + sint.nat hi <= j ∧
                  (sint.nat a <= j < sint.nat b)%nat ∧
                  (sint.nat a <= i < sint.nat b)%nat ->
                  xs' !! i = Some xi ->
                  xs' !! j = Some xj -> xj ≽ xi  ⌝ ∗
      "%Heap" ∷ ⌜ is_heap_seg xs' (sint.nat a) (sint.nat b) (sint.nat lo)%nat (sint.nat hi) ⌝ ∗
      "%Houtside" ∷ ⌜ outside_same xs xs' (sint.nat a) (sint.nat b) ⌝
  }}}.
Proof using StrictWeakOrder0 + RelDecision0 + W.
  wp_start as "H". iNamed "H". unfold is_heap_seg in *. wp_auto.

  iAssert( ∃ (root_val: w64) xs',
    "hi" ∷ hi_ptr ↦ hi ∗
    "cmp" ∷ cmp_ptr ↦ cmp_code ∗
    "first" ∷ first_ptr ↦ a ∗
    "data" ∷ data_ptr ↦ data ∗

    "root" ∷ root_ptr ↦ root_val ∗
    "Hxs1" ∷ data ↦* xs' ∗
    "%HPerm1" ∷ ⌜ Permutation xs xs' ⌝ ∗
    "%Hbound1" ∷ ⌜ sint.Z lo <= sint.Z root_val < sint.Z hi ⌝ ∗
    "%HSegSorted1" ∷ ⌜ ∀ i j (xi xj: E), (i < j)%nat ∧ sint.nat a + sint.nat hi <= j ∧
                  (sint.nat a <= j < sint.nat b)%nat ∧
                  (sint.nat a <= i < sint.nat b)%nat ->
                  xs' !! i = Some xi ->
                  xs' !! j = Some xj -> xj ≽ xi ⌝ ∗
    "%Heap" ∷ ⌜ forall i (xi xls xrs: E), (sint.nat lo <= i < sint.nat hi)%nat -> i ≠ (sint.nat root_val) -> xs' !! (sint.nat a + i)%nat = Some xi ->
                ((sint.nat lo <= 2 * i + 1 < sint.nat hi  ->  xs' !! (sint.nat a + 2 * i + 1)%nat = Some xls -> xi ≽ xls) ∧
                (sint.nat lo <= 2 * i + 2 < sint.nat hi  ->  xs' !! (sint.nat a + 2 * i + 2)%nat = Some xrs -> xi ≽ xrs)) ⌝ ∗
     "%HeapParent " ∷ ⌜ forall par_i (x_parent xls xrs: E), (sint.nat lo <= (sint.nat root_val) < sint.nat hi)%nat ->  (sint.nat lo <= par_i < sint.nat hi)%nat ->
              (2 * par_i + 1)%nat = (sint.nat root_val) ∨ (2 * par_i + 2)%nat = (sint.nat root_val) -> xs' !! (sint.nat a + par_i)%nat = Some x_parent ->
              ((sint.nat lo <= 2 * (sint.nat root_val) + 1 < sint.nat hi  ->  xs' !! (sint.nat a + 2 * (sint.nat root_val) + 1)%nat = Some xls -> x_parent ≽ xls) ∧
              (sint.nat lo <= 2 * (sint.nat root_val) + 2 < sint.nat hi  ->  xs' !! (sint.nat a + 2 * (sint.nat root_val) + 2)%nat = Some xrs -> x_parent ≽ xrs)) ⌝ ∗
      "%Houtside" ∷ ⌜ outside_same xs xs' (sint.nat a) (sint.nat b) ⌝

  )%I with "[Hxs hi data root first cmp ]" as "HI".
  { iFrame. iPureIntro. split; auto. split; try lia. split; auto.
    split; intros.
    - destruct (Heap i xi xls xrs); eauto; try lia. split; intros.
      + apply H2; eauto. lia.
      + apply H3; eauto. lia.
    - split; try split; auto; try lia.
    }
  wp_for "HI".
  iDestruct (own_slice_len with "Hxs1") as "%Hlen".
  assert(length xs = length xs'). { apply Permutation_length. auto. }
  clear Heap. wp_if_destruct.
  - (* child >= hi, exit the loop *)
    wp_for_post. iApply "HΦ". iFrame. iSplit; try iSplit; auto.
    { (* re-establishing the heap *)
      iPureIntro. split; auto. intros. destruct (Nat.eq_dec i (sint.nat root_val)) as [Heq | Hneq].
      - split_and!; intros; word.
      - destruct (Heap0 i xi xls xrs); eauto.  }
  - replace (sint.Z (word.add (word.mul (W64 2) root_val) (W64 1))) with (2 * (sint.Z root_val) + 1) in n by word.
    assert(sint.Z (word.add a root_val) = sint.Z a + sint.Z root_val) by word.
    assert(∃ x : E, xs' !! ((sint.nat a) + 2 * (sint.nat root_val) + 1)%nat  = Some x).
    { apply list_lookup_lt. lia. } destruct H1 as [xls Hls].
    assert(Hindex_ls: sint.nat (word.add a (word.add (word.mul (W64 2) root_val) (W64 1))) = ((sint.nat a) + 2 * (sint.nat root_val) + 1)%nat) by word.

    assert(∃ x : E, xs' !! (sint.nat a + sint.nat root_val)%nat = Some x). { apply list_lookup_lt. lia. }
    assert(Hindex_rt: sint.nat (word.add a root_val) = (sint.nat a + sint.nat root_val)%nat ) by word.
    destruct H1 as [xrt Hrt].
    wp_if_destruct.
    + (* right-chld within bound, check data[right-child] *)
      replace (sint.Z (word.add (word.add (word.mul (W64 2) root_val) (W64 1)) (W64 1))) with (2 * (sint.Z root_val) + 2) in l; try word.
      rewrite -> decide_True; last lia. (* Read left-child *)
      wp_apply (wp_load_slice_index with "[$Hxs1]") as "Hxs1";
      try rewrite Hindex_ls; try rewrite Hindex_ls; eauto; first lia.

      assert(∃ x : E, xs' !! ((sint.nat a) + 2 * (sint.nat root_val) + 2)%nat  = Some x).
      { apply list_lookup_lt. lia. } destruct H1 as [xrs Hrs].
      assert(Hindex_rs1: sint.nat (word.add (word.add a (word.add (word.mul (W64 2) root_val) (W64 1))) (W64 1)) = ((sint.nat a) + 2 * (sint.nat root_val) + 2)%nat) by word.
      assert(Hindex_rs2: sint.nat (word.add a (word.add (word.add (word.mul (W64 2) root_val) (W64 1)) (W64 1))) = ((sint.nat a) + 2 * (sint.nat root_val) + 2)%nat).
      { word. }

      rewrite -> decide_True; last lia. (* Read right-child *)
      wp_apply (wp_load_slice_index with "[$Hxs1]") as "Hxs1"; try rewrite Hindex_rs1; eauto; try lia.

      wp_apply "Hcmp". iIntros (r) "%Hcmp_r". wp_auto. wp_if_destruct.

      * (*.right-child greater *)
        rewrite -> decide_True; last lia. (* read the root *)
        wp_apply (wp_load_slice_index with "[$Hxs1]") as "Hxs1"; try rewrite Hindex_rt; eauto; first lia.

        rewrite -> decide_True; last lia. (* read the right child *)
        wp_apply (wp_load_slice_index with "[$Hxs1]") as "Hxs1"; try rewrite Hindex_rs2; eauto; first lia.

        wp_apply "Hcmp". iIntros (r2) "%Hcmp_r2". wp_auto. wp_if_destruct.
        -- (* root is not greatest, swap and continue *)
           rewrite -> decide_True; last lia. (* read the right child *)
           wp_apply (wp_load_slice_index with "[$Hxs1]") as "Hxs1"; try rewrite Hindex_rs2; eauto; first lia.
           rewrite -> decide_True; last lia. (* read the root *)
           wp_apply (wp_load_slice_index with "[$Hxs1]") as "Hxs1"; try rewrite Hindex_rt; eauto; first lia.
           rewrite -> decide_True; last lia. wp_auto. (* write to the root *)
           wp_apply (wp_store_slice_index with"[$Hxs1]") as "Hxs1"; try (iPureIntro; lia).
           rewrite -> decide_True; last lia. wp_auto. (* write to the right child *)
           wp_apply (wp_store_slice_index with"[$Hxs1]") as "Hxs1".
           { assert(length (<[sint.nat (word.add a root_val):=xrs]> xs') = length xs') by apply length_insert. iPureIntro. lia. }

           wp_for_post. iFrame. iSplit; iPureIntro.
           { eapply perm_trans. { eapply HPerm1. } { eapply swap_perm; try rewrite Hindex_rs2; try rewrite Hindex_rt; eauto. } }
           { split; first (clear HeapParent Heap0 HSegSorted Houtside; word).
             rewrite Hindex_rt. rewrite Hindex_rs2. split; intros.
            {
              (* re-establish seg *)
              rewrite list_lookup_insert_ne in H3; try lia.
             rewrite list_lookup_insert_ne in H3; try lia.
             destruct (Nat.eq_dec i (sint.nat a + 2 * sint.nat root_val + 2)%nat) as [Heq | Hneq].
             - rewrite <- Heq in H2. rewrite list_lookup_insert_eq in H2.
               { inv H2. eapply (HSegSorted1 (sint.nat a + sint.nat root_val)%nat j); eauto. lia. }
               { rewrite length_insert. lia. }
             - rewrite list_lookup_insert_ne in H2; try lia.
               destruct (Nat.eq_dec i (sint.nat a + sint.nat root_val)%nat) as [Heq1 | Hneq1].
               + rewrite <- Heq1 in H2. rewrite list_lookup_insert_eq in H2.
               { inv H2. eapply (HSegSorted1 (sint.nat a + 2 * sint.nat root_val + 2)%nat); eauto. lia. }
               { lia. }
               + rewrite list_lookup_insert_ne in H2; auto. eapply HSegSorted1; eauto.
            }
            { (* re-establish heap *)
              apply Hcmp_r in l0. apply R_antisym in l0; auto.
              apply Hcmp_r2 in l1. apply R_antisym in l1; auto.
              clear HSegSorted HSegSorted1 Hindex_rt Hindex_ls Hindex_rs1 Hindex_rs2 H0 Hcmp_r Hcmp_r2.
              assert(Hlen': length (<[(sint.nat a + sint.nat root_val)%nat:=xrs]> xs') = length xs') by apply length_insert.
              split. {
                intros.
                replace (sint.nat ((word.add) ((word.add) ((word.mul) (W64 2) root_val) (W64 1)) (W64 1))) with (2 * sint.nat root_val + 2)%nat in H1 by abstract(word).
                intros. destruct (Nat.eq_dec i (sint.nat root_val)) as [Heq | Hneq].
                - rewrite list_lookup_insert_ne in H2; try lia. rewrite Heq in H2.
                  rewrite list_lookup_insert_eq in H2; try lia. inv H2. split; intros.
                  + rewrite list_lookup_insert_ne in H3; try lia.
                    rewrite list_lookup_insert_ne in H3; try lia.
                    rewrite H3 in Hls. inv Hls. auto.
                  + rewrite list_lookup_insert_eq in H3; try lia.
                    inv H3. auto.
                - split; intros.
                  + rewrite list_lookup_insert_ne in H4; try lia.
                    destruct (Nat.eq_dec (2 * i + 1)%nat (sint.nat root_val)) as [Heq1 | Hneq1].
                    * rewrite <- Heq1 in H4. rewrite Nat.add_assoc in H4.
                      rewrite list_lookup_insert_eq in H4; try lia.
                      injection H4. intros. subst xls0.
                      rewrite list_lookup_insert_ne in H2; try lia.
                      rewrite list_lookup_insert_ne in H2; try lia.
                      destruct (HeapParent i xi xls xrs); eauto; try lia.
                      apply H6; eauto. lia.
                    * rewrite list_lookup_insert_ne in H4; try lia.
                      rewrite list_lookup_insert_ne in H2; try lia.
                      rewrite list_lookup_insert_ne in H2; try lia.
                      destruct (Heap0 i xi xls0 xrs); auto.
                  + rewrite list_lookup_insert_ne in H2; auto; try lia.
                    rewrite list_lookup_insert_ne in H2; auto; try lia.
                    rewrite list_lookup_insert_ne in H4; auto; try lia.
                    destruct (Nat.eq_dec (2 * i + 2)%nat (sint.nat root_val)) as [Heq1 | Hneq1].
                    * rewrite <- Heq1 in H4. rewrite Nat.add_assoc in H4.
                      rewrite list_lookup_insert_eq in H4; try lia. inv H4.
                      destruct (HeapParent i xi xls xrs0); eauto; try lia.
                      apply H5; eauto. lia.
                    * rewrite list_lookup_insert_ne in H4; try lia.
                      destruct (Heap0 i xi xls0 xrs0); auto.
              }
              {
                split; try eapply outside_same_trans; eauto; try eapply outside_same_swap; try lia.
                replace (sint.nat ((word.add) ((word.add) ((word.mul) (W64 2) root_val) (W64 1)) (W64 1))) with (2 * sint.nat root_val + 2)%nat by abstract(word).
                intros. assert(par_i = sint.nat root_val) by lia. subst par_i.
                rewrite list_lookup_insert_ne in H3; try lia.
                rewrite list_lookup_insert_eq in H3; try lia.
                inv H3. split; intros.
                - rewrite list_lookup_insert_ne in H4; try lia.
                  rewrite list_lookup_insert_ne in H4; try lia.
                  destruct (Heap0 (2 * sint.nat root_val + 2)%nat x_parent xls0 xls0); eauto; try lia.
                  rewrite Nat.add_assoc. auto.
                - rewrite list_lookup_insert_ne in H4; try lia.
                  rewrite list_lookup_insert_ne in H4; try lia.
                  destruct (Heap0 (2 * sint.nat root_val + 2)%nat x_parent xrs0 xrs0); eauto; try lia.
                  rewrite Nat.add_assoc. auto.
              }
            }

           }
        -- (* root is greatest, exit the loop *)
           wp_for_post. iApply "HΦ". iFrame. auto. iPureIntro.
           split; auto. split; auto.
           split; try eapply outside_same_trans; eauto; try eapply outside_same_refl.
           intros. destruct (Nat.eq_dec i (sint.nat root_val)) as [Heq | Hneq].
           {
            subst i. rewrite Hrt in H2. inv H2.
            apply Hcmp_r in l0. apply comparison_negate in Hcmp_r2.
            apply Hcmp_r2 in n0. apply R_antisym in l0; auto.
            split; intros.
            - rewrite H3 in Hls. inv Hls.
              eapply notR_trans; eauto.
            - rewrite H3 in Hrs. inv Hrs. auto.
            }
            {
              destruct (Heap0 i xi xls0 xrs0); eauto.
            }

      * (* left-child greater *)
        rewrite -> decide_True; last lia.  (* read the root *)
        wp_apply (wp_load_slice_index with "[$Hxs1]") as "Hxs1"; try rewrite Hindex_rt; auto; first lia.

        rewrite -> decide_True; last lia. (* read the right child *)
        wp_apply (wp_load_slice_index with "[$Hxs1]") as "Hxs1"; try rewrite Hindex_ls; auto; first lia.

        wp_apply "Hcmp". iIntros (r2) "%Hcmp_r2". wp_auto. wp_if_destruct.
        -- (* root is not greatest, swap and continue *)
           rewrite -> decide_True; last lia. (* read the left-child *)
           wp_apply (wp_load_slice_index with "[$Hxs1]") as "Hxs1"; try rewrite Hindex_ls; eauto; first lia.
           rewrite -> decide_True; last lia. (* read the root *)
           wp_apply (wp_load_slice_index with "[$Hxs1]") as "Hxs1"; try rewrite Hindex_rt; eauto; first lia.

           rewrite -> decide_True; last lia. wp_auto. (* write to the root *)
           wp_apply (wp_store_slice_index with"[$Hxs1]") as "Hxs1"; try (iPureIntro; lia).

           rewrite -> decide_True; last lia. wp_auto. (* write to the left-child *)
           wp_apply (wp_store_slice_index with"[$Hxs1]") as "Hxs1".
           { assert(length (<[sint.nat (word.add a root_val):=xls]> xs') = length xs') by apply length_insert.
            iPureIntro; lia. }

           wp_for_post. iFrame. iPureIntro; split; try split.
           { eapply perm_trans. { eapply HPerm1. } { eapply swap_perm; try rewrite Hindex_ls; try rewrite Hindex_rt; eauto. } }
           { clear HSegSorted HSegSorted1 Heap0 HeapParent. abstract(word). }
           {  split.
            { (* restore seg *)
              rewrite Hindex_rt. rewrite Hindex_ls. intros.
              rewrite list_lookup_insert_ne in H3; try lia.
              rewrite list_lookup_insert_ne in H3; try lia.
              destruct (Nat.eq_dec i (sint.nat a + 2 * sint.nat root_val + 1)%nat) as [Heq | Hneq].
              - rewrite <- Heq in H2. rewrite list_lookup_insert_eq in H2.
                { inv H2. eapply (HSegSorted1 (sint.nat a + sint.nat root_val)%nat j); eauto. lia. }
                { rewrite length_insert. lia. }
              - rewrite list_lookup_insert_ne in H2; try lia.
                destruct (Nat.eq_dec i (sint.nat a + sint.nat root_val)%nat) as [Heq1 | Hneq1].
                + rewrite <- Heq1 in H2. rewrite list_lookup_insert_eq in H2.
                { inv H2. eapply (HSegSorted1 (sint.nat a + 2 * sint.nat root_val + 1)%nat); eauto. lia. }
                { lia. }
                + rewrite list_lookup_insert_ne in H2; auto. eapply HSegSorted1; eauto. }
              {
                (* re-establish heap *)
                apply comparison_negate in Hcmp_r. apply Hcmp_r in n0.
                apply Hcmp_r2 in l0. apply R_antisym in l0; auto.
                rewrite Hindex_rt. rewrite Hindex_ls.
                clear HSegSorted HSegSorted1 Hindex_rt Hindex_ls Hindex_rs1 Hindex_rs2 H0 Hcmp_r Hcmp_r2.
                assert(Hlen': length (<[(sint.nat a + sint.nat root_val)%nat:=xls]> xs') = length xs') by apply length_insert.
                split. {
                  intros.
                  replace (sint.nat (((word.add) ((word.mul) (W64 2) root_val) (W64 1)) )) with (2 * sint.nat root_val + 1)%nat in H1 by abstract(word).
                  intros. destruct (Nat.eq_dec i (sint.nat root_val)) as [Heq | Hneq].
                  - rewrite list_lookup_insert_ne in H2; try lia. rewrite Heq in H2.
                    rewrite list_lookup_insert_eq in H2; try lia. inv H2. split; intros.
                    + rewrite list_lookup_insert_eq in H3; try lia.
                      inv H3. auto.
                    + rewrite list_lookup_insert_ne in H3; try lia.
                      rewrite list_lookup_insert_ne in H3; try lia.
                      rewrite Hrs in H3. inv H3. auto.
                  - split; intros.
                    + rewrite list_lookup_insert_ne in H2; try lia.
                      rewrite list_lookup_insert_ne in H4; try lia.
                      rewrite list_lookup_insert_ne in H2; try lia.
                      destruct (Nat.eq_dec (2 * i + 1)%nat (sint.nat root_val)) as [Heq1 | Hneq1].
                      * rewrite <- Heq1 in H4. rewrite Nat.add_assoc in H4.
                        rewrite list_lookup_insert_eq in H4; try lia. inv H4.
                        destruct (HeapParent i xi xls0 xrs); eauto; try lia.
                        apply H4; eauto. lia.
                      * rewrite list_lookup_insert_ne in H4; try lia.
                        destruct (Heap0 i xi xls0 xrs); auto.
                    + rewrite list_lookup_insert_ne in H2; auto; try lia.
                      rewrite list_lookup_insert_ne in H2; auto; try lia.
                      rewrite list_lookup_insert_ne in H4; auto; try lia.
                      destruct (Nat.eq_dec (2 * i + 2)%nat (sint.nat root_val)) as [Heq1 | Hneq1].
                      * rewrite <- Heq1 in H4. rewrite Nat.add_assoc in H4.
                        rewrite list_lookup_insert_eq in H4; try lia.
                        rewrite <- Heq1 in Hrt. rewrite Nat.add_assoc in Hrt.
                        injection H4. intros. subst xrs0.
                        destruct (HeapParent i xi xls xrs); eauto; try lia.
                        apply H5; eauto. lia.
                      * rewrite list_lookup_insert_ne in H4; try lia.
                        destruct (Heap0 i xi xls0 xrs0); auto.
              }
              {
                split; try eapply outside_same_trans; eauto; try eapply outside_same_swap; try lia.
                replace (sint.nat (((word.add) ((word.mul) (W64 2) root_val) (W64 1)))) with (2 * sint.nat root_val + 1)%nat by abstract(word).
                intros. assert(par_i = sint.nat root_val) by lia. subst par_i.
                rewrite list_lookup_insert_ne in H3; try lia.
                rewrite list_lookup_insert_eq in H3; try lia.
                inv H3. split; intros.
                - rewrite list_lookup_insert_ne in H4; try lia.
                  rewrite list_lookup_insert_ne in H4; try lia.
                  destruct (Heap0 (2 * sint.nat root_val + 1)%nat x_parent xls0 xls0); eauto; try lia.
                  rewrite Nat.add_assoc. auto.
                - rewrite list_lookup_insert_ne in H4; try lia.
                  rewrite list_lookup_insert_ne in H4; try lia.
                  destruct (Heap0 (2 * sint.nat root_val + 1)%nat x_parent xrs0 xrs0); eauto; try lia.
                  rewrite Nat.add_assoc. auto.
              }
            }
           }
          -- (* root is greatest, exit the loop *)
             wp_for_post. iApply "HΦ". iFrame. iSplit; auto.
             iSplit; auto. iPureIntro.
             split; try eapply outside_same_trans; eauto; try eapply outside_same_refl.
             intros.

           destruct (Nat.eq_dec i (sint.nat root_val)) as [Heq | Hneq].
           {
            subst i. rewrite Hrt in H2. inv H2.
            apply comparison_negate in Hcmp_r, Hcmp_r2.
            apply Hcmp_r in n0. apply Hcmp_r2 in n1.
            split; intros.
            - rewrite H3 in Hls. inv Hls. eauto.
            - rewrite H3 in Hrs. inv Hrs.
              eapply notR_trans; eauto.
          }
          {
            destruct (Heap0 i xi xls0 xrs0); eauto.
          }
    + (* right-child out of bound; only consider left-child *)
      rewrite -> decide_True; last lia. (* read the root val *)
      wp_apply (wp_load_slice_index with "[$Hxs1]") as "Hxs1"; try rewrite Hindex_rt; eauto; first lia.
      rewrite -> decide_True; last lia. (* read the left-child *)
      wp_apply (wp_load_slice_index with "[$Hxs1]") as "Hxs1"; try rewrite Hindex_ls; eauto; first lia.

      wp_apply "Hcmp". iIntros (r) "%Hcmp_r". wp_auto. wp_if_destruct.
      * (* root is not greatest, swap and continue *)
        rewrite -> decide_True; last lia. (* read the left-child *)
        wp_apply (wp_load_slice_index with "[$Hxs1]") as "Hxs1"; try rewrite Hindex_ls; eauto; first lia.
        rewrite -> decide_True; last lia. (* read the root val *)
        wp_apply (wp_load_slice_index with "[$Hxs1]") as "Hxs1"; try rewrite Hindex_rt; eauto; first lia.
        rewrite -> decide_True; last lia. wp_auto. (* write to the root *)
        wp_apply (wp_store_slice_index with"[$Hxs1]") as "Hxs1"; try (iPureIntro; lia).
        rewrite -> decide_True; last lia. wp_auto. (* write to the left-child *)
        wp_apply (wp_store_slice_index with"[$Hxs1]") as "Hxs1".
        { assert(length (<[sint.nat (word.add a root_val):=xls]> xs') = length xs') by apply length_insert.
          iPureIntro. lia. }

        wp_for_post. iFrame. iSplit; iPureIntro; try split.
        { eapply perm_trans. { eapply HPerm1. } { eapply swap_perm; try rewrite Hindex_ls; try rewrite Hindex_rt; eauto. } }
        { clear HSegSorted HSegSorted1 Heap0 HeapParent. abstract(word). }
        {
          split.
          {  (* restore seg *)
              rewrite Hindex_rt. rewrite Hindex_ls. intros.
             rewrite list_lookup_insert_ne in H3; try lia.
             rewrite list_lookup_insert_ne in H3; try lia.
             destruct (Nat.eq_dec i (sint.nat a + 2 * sint.nat root_val + 1)%nat) as [Heq | Hneq].
             - rewrite <- Heq in H2. rewrite list_lookup_insert_eq in H2.
               { inv H2. eapply (HSegSorted1 (sint.nat a + sint.nat root_val)%nat j); eauto. lia. }
               { rewrite length_insert. lia. }
             - rewrite list_lookup_insert_ne in H2; try lia.
               destruct (Nat.eq_dec i (sint.nat a + sint.nat root_val)%nat) as [Heq1 | Hneq1].
               + rewrite <- Heq1 in H2. rewrite list_lookup_insert_eq in H2.
               { inv H2. eapply (HSegSorted1 (sint.nat a + 2 * sint.nat root_val + 1)%nat); eauto. lia. }
               { lia. }
               + rewrite list_lookup_insert_ne in H2; auto. eapply HSegSorted1; eauto. }
          {
            (* re-store heap *)
            apply Hcmp_r in l. apply R_antisym in l; auto.
            rewrite Hindex_rt. rewrite Hindex_ls.
            clear HSegSorted HSegSorted1 Hindex_rt Hindex_ls H0 Hcmp_r.
            assert(Hlen': length (<[(sint.nat a + sint.nat root_val)%nat:=xls]> xs') = length xs') by apply length_insert.
            split. {
              intros.
              replace (sint.nat (((word.add) ((word.mul) (W64 2) root_val) (W64 1)) )) with (2 * sint.nat root_val + 1)%nat in H1 by abstract(word).
              intros. destruct (Nat.eq_dec i (sint.nat root_val)) as [Heq | Hneq].
              - rewrite list_lookup_insert_ne in H2; try lia. rewrite Heq in H2.
                rewrite list_lookup_insert_eq in H2; try lia. inv H2. split; intros.
                + rewrite list_lookup_insert_eq in H3; try lia.
                  inv H3. auto.
                + abstract(word).
              - split; intros.
                + rewrite list_lookup_insert_ne in H2; try lia.
                  rewrite list_lookup_insert_ne in H4; try lia.
                  rewrite list_lookup_insert_ne in H2; try lia.
                  destruct (Nat.eq_dec (2 * i + 1)%nat (sint.nat root_val)) as [Heq1 | Hneq1].
                  * rewrite <- Heq1 in H4. rewrite Nat.add_assoc in H4.
                    rewrite list_lookup_insert_eq in H4; try lia. inv H4.
                    destruct (HeapParent i xi xls0 xrs); eauto; try lia.
                    apply H4; eauto. lia.
                  * rewrite list_lookup_insert_ne in H4; try lia.
                    destruct (Heap0 i xi xls0 xrs); auto.
                + rewrite list_lookup_insert_ne in H2; auto; try lia.
                  rewrite list_lookup_insert_ne in H2; auto; try lia.
                  rewrite list_lookup_insert_ne in H4; auto; try lia.
                  destruct (Nat.eq_dec (2 * i + 2)%nat (sint.nat root_val)) as [Heq1 | Hneq1].
                  * rewrite <- Heq1 in H4. rewrite Nat.add_assoc in H4.
                    rewrite list_lookup_insert_eq in H4; try lia.
                    rewrite <- Heq1 in Hrt. rewrite Nat.add_assoc in Hrt.
                    injection H4. intros. subst xls.
                    destruct (HeapParent i xi xrs xrs); eauto; try lia.
                    apply H5; eauto. lia.
                  * rewrite list_lookup_insert_ne in H4; try lia.
                    destruct (Heap0 i xi xls0 xrs); auto.
          }
          {
            split; try eapply outside_same_trans; eauto; try eapply outside_same_swap; try lia.
            replace (sint.nat (((word.add) ((word.mul) (W64 2) root_val) (W64 1)))) with (2 * sint.nat root_val + 1)%nat by abstract(word).
            intros. assert(par_i = sint.nat root_val) by lia. subst par_i.
            rewrite list_lookup_insert_ne in H3; try lia.
            rewrite list_lookup_insert_eq in H3; try lia.
            inv H3. split; intros.
            - rewrite list_lookup_insert_ne in H4; try lia.
              rewrite list_lookup_insert_ne in H4; try lia.
              destruct (Heap0 (2 * sint.nat root_val + 1)%nat x_parent xls0 xls0); eauto; try lia.
              rewrite Nat.add_assoc. auto.
            - rewrite list_lookup_insert_ne in H4; try lia.
              rewrite list_lookup_insert_ne in H4; try lia.
              destruct (Heap0 (2 * sint.nat root_val + 1)%nat x_parent xrs xrs); eauto; try lia.
              rewrite Nat.add_assoc. auto.
          }
          }
        }

      * (* root is greatest, exit the loop *)
        wp_for_post. iApply "HΦ". iFrame. auto.
        iSplit; auto. iSplit; auto. iPureIntro.
        split; try eapply outside_same_trans; eauto; try eapply outside_same_refl.
        intros.
        destruct (Nat.eq_dec i (sint.nat root_val)) as [Heq | Hneq].
        {
          subst i. rewrite Hrt in H2. inv H2.
          apply comparison_negate in Hcmp_r.
          apply Hcmp_r in n1. split; intros.
          - rewrite H3 in Hls. inv Hls. eauto.
          - abstract(word).
        }
        {
          destruct (Heap0 i xi xls0 xls0); eauto.
        }
Qed.

Lemma wp_siftDownCmpFunc_Trivial (data: slice.t) (a b: w64) (cmp_code: func.t)
                       (xs: list E):
  {{{ is_pkg_init slices ∗
      "Hxs" ∷ data ↦* xs ∗
      "#Hcmp" ∷ cmp_implements R cmp_code ∗
      "%H_bounds" ∷ ⌜ 0 ≤ sint.Z a ∧
                      sint.Z b <= length xs ∧
                      length xs <= 2 ^ 62⌝
  }}}
    #(functions slices.siftDownCmpFunc [Et]) #data #(W64 0) #(W64 0) #a #cmp_code
  {{{ RET #();
      "Hxs" ∷ data ↦* xs
  }}}.
Proof using RelDecision0 + StrictWeakOrder0 + W.
  wp_start as "H". iNamed "H". unfold is_heap_seg in *. wp_auto.
  iAssert(
    "hi" ∷ hi_ptr ↦ (W64 0) ∗
    "cmp" ∷ cmp_ptr ↦ cmp_code ∗
    "first" ∷ first_ptr ↦ a ∗
    "data" ∷ data_ptr ↦ data ∗

    "root" ∷ root_ptr ↦ (W64 0) ∗
    "Hxs1" ∷ data ↦* xs
  )%I with "[Hxs hi data root first cmp ]" as "HI".
  { iFrame. }
  wp_for "HI".
  iDestruct (own_slice_len with "Hxs1") as "%Hlen".
  wp_for_post. iApply "HΦ". iFrame.
Qed.

Lemma wp_heapSortCmpFunc (data: slice.t) (a b: w64) (cmp_code: func.t)
                       (xs: list E):
  {{{ is_pkg_init slices ∗
      "Hxs" ∷ data ↦* xs ∗
      "#Hcmp" ∷ cmp_implements R cmp_code ∗
      "%Hab_bound" ∷ ⌜ 0 ≤ sint.Z a < sint.Z b ∧ sint.Z b <= length xs

                      ∧  length xs <= 2 ^ 62     ⌝
  }}}
    #(functions slices.heapSortCmpFunc [Et]) #data #a #b #cmp_code
  {{{ (xs': list E), RET #();
      data ↦* xs' ∗
      "%Hperm" ∷ ⌜ Permutation xs xs' ⌝ ∗
      "%Hsorted" ∷ ⌜ is_sorted_seg R xs' (sint.nat a) (sint.nat b) ⌝ ∗
      "%Houtside" ∷ ⌜ outside_same xs xs' (sint.nat a) (sint.nat b) ⌝
  }}}.
Proof using RelDecision0 + StrictWeakOrder0 + W.
  wp_start as "H". iNamed "H". wp_auto.
  assert(Hdiv: sint.Z (word.divs (word.sub (word.sub b a) (W64 1)) (W64 2)) = ((sint.Z b - sint.Z a - 1) / 2) ).
  { replace (word.sub (word.sub b a) (W64 1)) with (W64 (sint.Z b - sint.Z a - 1)) by word.
    rewrite Automation.word.word_signed_divs_nowrap_pos; word. }
  (* Loop Invariant for the outer loop *)
  iAssert( ∃ (i_val: w64) xs',
    "Hxs1" ∷ data ↦* xs' ∗
    "lo" ∷ lo_ptr ↦ W64 0 ∗
    "hi" ∷ hi_ptr ↦ (word.sub b a) ∗

    "i" ∷ i_ptr ↦ i_val ∗
    "%irange" ∷ ⌜ sint.Z (W64 (-1)) ≤ sint.Z i_val ≤ sint.Z b - sint.Z a - 1 ⌝ ∗
    "%HPerm1" ∷ ⌜ Permutation xs xs' ⌝ ∗
    "%Heap1" ∷ ⌜ is_heap_seg xs' (sint.nat a) (sint.nat b) (sint.nat (word.add i_val (W64 1))) (sint.nat b - sint.nat a) ⌝ ∗
    "%HSegSorted" ∷ ⌜∀ (i j : nat) (xi xj : E),
                    (i < j)%nat
                    ∧ sint.nat a + (sint.nat b - sint.nat a)%nat ≤ j ∧ (sint.nat a <= j < sint.nat b)%nat
                    ∧ (sint.nat a <= i < sint.nat b)%nat
                    → xs' !! i = Some xi → xs' !! j = Some xj → ¬ xj ≺ xi⌝ ∗
    "%Houtside1" ∷ ⌜ outside_same xs xs' (sint.nat a) (sint.nat b) ⌝
  )%I with "[Hxs lo hi i]" as "HI1".
  { iFrame. iPureIntro. split.
    - rewrite Hdiv. word.
    - split; try auto. split.
      + unfold is_heap_seg. split; intros; word.
      + split; try apply outside_same_refl.
        intros. word. }

  wp_for "HI1".
  assert(length xs = length xs') by (apply Permutation_length; auto).
  wp_if_destruct.
  - wp_apply ((wp_siftDownCmpFunc data (i_val) (word.sub b a) a b) with "[Hxs1]").
    { iFrame.
      replace (sint.nat (word.sub b a)) with (sint.nat b - sint.nat a)%nat by word.
     iSplit; auto. iSplit; first word.
     replace (sint.nat (word.add i_val (W64 1))) with (sint.nat i_val + 1)%nat in Heap1 by word.
     auto. }
     replace (sint.nat (word.sub b a)) with (sint.nat b - sint.nat a)%nat by word.
    iIntros (xs'') "Hxs2". iNamed "Hxs2". wp_auto.
    wp_for_post. iFrame. iPureIntro.
    split; first word. split.
    { eapply perm_trans; eauto. }
    { split.
      - replace (sint.nat (w64_word_instance .(word.add) (w64_word_instance .(word.sub) i_val (W64 1)) (W64 1))) with (sint.nat i_val) by word.
        auto.
      - split; auto. eapply outside_same_trans; eauto. }
  - iAssert(
    "Hxs1" ∷ data ↦* xs' ∗

    "%HPerm1" ∷ ⌜ Permutation xs xs' ⌝ ∗
    "%Heap1" ∷ ⌜ is_heap_seg xs' (sint.nat a) (sint.nat b) 0%nat (sint.nat b - sint.nat a) ⌝ ∗
    "%HSegSorted" ∷ ⌜∀ (i j : nat) (xi xj : E),
                    (i < j)%nat
                    ∧ sint.nat a + (sint.nat b - sint.nat a)%nat ≤ j ∧ (sint.nat a <= j < sint.nat b)%nat
                    ∧ (sint.nat a <= i < sint.nat b)%nat
                    → xs' !! i = Some xi → xs' !! j = Some xj → ¬ xj ≺ xi⌝ ∗
    "%Houtside1" ∷ ⌜ outside_same xs xs' (sint.nat a) (sint.nat b) ⌝
    )%I with "[Hxs1]" as "Hmid".
    { iFrame. iSplit; auto. iSplit; auto.
      replace (sint.nat (w64_word_instance .(word.add) i_val (W64 1))) with 0%nat in Heap1 by word.
      auto. }
    clear i_val irange Heap1 n.
    iNamed "Hmid".

    iAssert( ∃ (i_val: w64) xs',
    "Hxs1" ∷ data ↦* xs' ∗

    "i" ∷ i_ptr ↦ i_val ∗
    "%irange" ∷ ⌜ sint.Z (W64 (-1)) ≤ sint.Z i_val ≤ sint.Z b - sint.Z a - 1 ⌝ ∗


    "%HPerm1" ∷ ⌜ Permutation xs xs' ⌝ ∗
    "%Heap1" ∷ ⌜ is_heap_seg xs' (sint.nat a) (sint.nat b) 0%nat (sint.nat (word.add i_val (W64 1))) ⌝ ∗
    "%HSegSorted" ∷ ⌜∀ (i j : nat) (xi xj : E),
                    (i < j)%nat
                    ∧ sint.nat a + (sint.nat i_val) < j ∧
                    (sint.nat a <= j < sint.nat b)%nat ∧
                    (sint.nat a <= i < sint.nat b)%nat
                    → xs' !! i = Some xi → xs' !! j = Some xj → ¬ xj ≺ xi⌝ ∗
    "%Houtside1" ∷ ⌜ outside_same xs xs' (sint.nat a) (sint.nat b) ⌝
    )%I with "[Hxs1 i]" as "HI2".
    { iFrame. iSplit; first word. iPureIntro.
      split; auto.
      replace ((sint.nat
(w64_word_instance .(word.add)
(w64_word_instance .(word.sub)
(w64_word_instance .(word.sub) b a) (W64 1))
(W64 1)))) with (sint.nat b - sint.nat a)%nat by word.
      split; auto. split; auto.
      intros. word.  }
    wp_for "HI2".
    + assert(length xs = length xs'0) by (apply Permutation_length; auto).
      iDestruct (own_slice_len with "Hxs1") as "%Hlen".
      wp_if_destruct.
      * assert(Hindex_i: sint.nat (word.add a i_val) = (sint.nat a + sint.nat i_val)%nat) by word.
        assert(∃ x : E, xs'0 !! (sint.nat a +  sint.nat i_val)%nat = Some x). { apply list_lookup_lt. lia. }
        destruct H1 as [xi Hxi].

        assert(∃ x : E, xs'0 !! (sint.nat a) = Some x). { apply list_lookup_lt. lia. }
        destruct H1 as [x0 Hx0].

        rewrite -> decide_True; last word.
        wp_apply (wp_load_slice_index with "[$Hxs1]") as "Hxs1".
        { word. } { rewrite Hindex_i. auto. }

        rewrite -> decide_True; last word.
        wp_apply (wp_load_slice_index with "[$Hxs1]") as "Hxs1".
        { word. } { auto. }

        rewrite -> decide_True; last word. wp_auto.
        wp_apply (wp_store_slice_index with "[$Hxs1]") as "Hxs1"; first word.

        assert(length (<[sint.nat a:=xi]> xs'0) = length xs'0) by apply length_insert.
        rewrite -> decide_True; last word. wp_auto.
        wp_apply (wp_store_slice_index with "[$Hxs1]") as "Hxs1"; first word.

        clear xs' HPerm1 HPerm0 H Houtside0 HSegSorted Houtside1 Heap1 HSegSorted0.
        destruct (Nat.eq_dec (sint.nat i_val) 0%nat) as [Heq3 | Hneq3].
        {
          replace i_val with (W64 0) in * by word.
          replace (sint.nat a + sint.nat (W64 0))%nat with (sint.nat a) in Hxi by lia.
          rewrite Hxi in Hx0. inv Hx0.
          assert(<[sint.nat (w64_word_instance .(word.add) a (W64 0)):=x0]> (<[sint.nat a:=x0]> xs'0) = xs'0).
          {
            replace (sint.nat (word.add a (W64 0))) with (sint.nat a)by word.
            rewrite list_insert_id; auto.
            - apply list_insert_id; eauto.
            - apply list_lookup_insert_eq. lia.
          }
          rewrite H.
          wp_apply ((wp_siftDownCmpFunc_Trivial data a b) with "[$Hxs1]").
          { iSplit; auto. iPureIntro. lia. }
          {
            iIntros "Hxs". wp_auto. wp_for_post.
            iFrame. iSplit; first word.
            iSplit; auto. iSplit; auto.
            iPureIntro. unfold is_heap_seg. intros. word.
          }
        }
        wp_apply ((wp_siftDownCmpFunc data (W64 0) (i_val) a b) with "[$Hxs1]").
        {
          rewrite Hindex_i.
          assert(length (<[(sint.nat a + sint.nat i_val)%nat:=x0]> (<[sint.nat a:=xi]> xs'0)) = length xs'0).
          { rewrite length_insert; apply length_insert. }
          iSplit; auto. iSplit. { word. }
          iSplit. {
            iPureIntro. intros.
            destruct (Nat.eq_dec j (sint.nat a + sint.nat i_val)%nat) as [Heq | Hneq].
            - rewrite list_lookup_insert_ne in H3; try lia.
              rewrite Heq in H4. rewrite list_lookup_insert_eq in H4; try lia.
              inv H4. rename xj into x0.
              destruct (Nat.eq_dec i (sint.nat a)%nat) as [Heq1 | Hneq1].
              + rewrite Heq1 in H3.
                rewrite list_lookup_insert_eq in H3; try lia. inv H3.
                eapply heap_top_greatest; eauto.
                * replace (sint.nat (w64_word_instance .(word.add) i_val (W64 1))) with (sint.nat i_val + 1)%nat in Heap0 by word.
                  eapply Heap0.
                * lia.
                * lia.
              + rewrite list_lookup_insert_ne in H3; auto.
                eapply heap_top_greatest.
                * replace (sint.nat (w64_word_instance .(word.add) i_val (W64 1))) with (sint.nat i_val + 1)%nat in Heap0 by word.
                  eapply Heap0.
                * eauto.
                * replace i with (sint.nat a + (i - sint.nat a))%nat in H3 by lia.
                  apply H3.
                * lia.
                * lia.
            - rewrite list_lookup_insert_ne in H4; try lia.
              rewrite list_lookup_insert_ne in H4; try lia.
              destruct (Nat.eq_dec i (sint.nat a + sint.nat i_val)%nat) as [Heq1 | Hneq1].
              + rewrite Heq1 in H3. rewrite list_lookup_insert_eq in H3; try lia.
                inv H3. eapply HSegSorted1; eauto. lia.
              + rewrite list_lookup_insert_ne in H3; auto.
                destruct (Nat.eq_dec i (sint.nat a)%nat) as [Heq2 | Hneq2].
                * rewrite <- Heq2 in H3. rewrite list_lookup_insert_eq in H3; try lia.
                  inv H3. eapply HSegSorted1; eauto. lia.
                * rewrite list_lookup_insert_ne in H3; auto.
                  eapply HSegSorted1; eauto. lia.
          }
          {
            replace (sint.nat (W64 0) + 1) with 1 by word.
            replace (sint.nat (w64_word_instance .(word.add) i_val (W64 1))) with (sint.nat i_val + 1)%nat in Heap0 by word.
            iPureIntro. unfold is_heap_seg.
            unfold is_heap_seg in Heap0.
            intros.
            rewrite list_lookup_insert_ne in H3; try lia.
            rewrite list_lookup_insert_ne in H3; try lia.
            split; intros.
            - rewrite list_lookup_insert_ne in H5; try lia.
              rewrite list_lookup_insert_ne in H5; try lia.
              destruct (Heap0 i xi0 xls xls); auto; try lia.
              apply H6; eauto; lia.
            - rewrite list_lookup_insert_ne in H5; try lia.
              rewrite list_lookup_insert_ne in H5; try lia.
              destruct (Heap0 i xi0 xrs xrs); auto; try lia.
              apply H7; eauto; lia.
          }
        }
        iIntros (xs') "Hpost". iNamed "Hpost".
        wp_auto. wp_for_post. iFrame. iPureIntro.
        split; first word.
        split. { eapply perm_trans; try eapply HPermPost.
          eapply perm_trans; try apply HPerm2.
          replace (sint.nat (word.add a i_val)) with (sint.nat a + sint.nat i_val)%nat by word.
          eapply swap_perm; eauto.
          }
        split. { replace (sint.nat (w64_word_instance .(word.add) (w64_word_instance .(word.sub) i_val (W64 1)) (W64 1))) with (sint.nat i_val) by word. auto. }
        split. { intros. eapply HSegSortedPost; eauto. word. }
        { eapply outside_same_trans; eauto.
          assert(outside_same xs'0 (<[sint.nat (w64_word_instance .(word.add) a i_val):=x0]> (<[sint.nat a:=xi]> xs'0)) (sint.nat a) (sint.nat b)).
          { unfold outside_same.
            intros.
            rewrite list_lookup_insert_ne; try lia.
            rewrite list_lookup_insert_ne; try lia. auto.  }
          eapply outside_same_trans; try eapply H. auto. }
      * iApply "HΦ". iFrame.
        iSplit; auto. iSplit; auto.
        iPureIntro. unfold is_sorted_seg.
        intros. eapply HSegSorted1; eauto. word.
Qed.

End proof.
