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

Definition is_partitioned_pre (xs: list E) (a b i_val j_val: nat) :=
    ∀ i xi xa, xs !! i = Some xi -> xs !! a = Some xa ->
        (((a < i < i_val)%nat -> xa ≽ xi) ∧
        ((j_val < i < b)%nat -> xi ≽ xa) ).

Definition is_partitioned (xs: list E) (a b r: nat) :=
    ∀ i xr xi, xs !! i = Some xi -> xs !! r = Some xr ->
        (((a <= i < r)%nat -> xr ≽ xi) ∧
        ((r < i < b)%nat -> xi ≽ xr) ).

Lemma is_partitioned_pre_advance_left:
  forall xs a b i_val j_val xa xi,
  is_partitioned_pre xs a b i_val j_val ->
  xs !! a = Some xa -> xs !! i_val = Some xi -> xa ≽ xi ->
  is_partitioned_pre xs a b (i_val + 1)%nat j_val.
Proof.
  unfold is_partitioned_pre. intros.
  rewrite H4 in H0. inv H0.
  destruct (H i xi0 xa); eauto. split; auto.
  destruct (Nat.eq_dec i_val i).
  - subst i_val. rewrite H3 in H1. inv H1.
    intros. auto.
  - intros. apply H0. lia.
Qed.

Lemma is_partitioned_pre_advance_right:
  forall xs a b i_val j_val xa xj,
  is_partitioned_pre xs a b i_val j_val ->
  xs !! a = Some xa -> xs !! j_val = Some xj -> xj ≽ xa ->
  is_partitioned_pre xs a b i_val (j_val - 1)%nat.
Proof.
  unfold is_partitioned_pre. intros.
  rewrite H4 in H0. inv H0.
  destruct (H i xi xa); eauto. split; auto.
  destruct (Nat.eq_dec j_val i).
  - subst j_val. rewrite H3 in H1. inv H1.
    intros. auto.
  - intros. apply H5. lia.
Qed.

Lemma partition_conclude:
  forall xs a b i_val j_val xa xj,
  (i_val > j_val)%nat ->
  (a < i_val)%nat ∧ (j_val >= a)%nat ->
  is_partitioned_pre xs a b i_val j_val ->
  xs !! a = Some xa -> xs !! j_val = Some xj ->
  is_partitioned (<[a := xj]> (<[j_val := xa]> xs)) a b j_val.
Proof.
  unfold is_partitioned_pre. unfold is_partitioned. intros.
  assert(length (<[j_val := xa]> xs) = length xs) by apply length_insert.
  assert((j_val < length xs)%nat). { eapply lookup_lt_Some. eauto. }
  assert((a < length xs)%nat). { eapply lookup_lt_Some. eauto. }
  assert(xr = xa). {
    destruct (Nat.eq_dec a j_val).
    - subst j_val.
      rewrite list_lookup_insert_eq in H5; try lia.
      inv H4. auto.
    - rewrite list_lookup_insert_ne in H5; auto.
      rewrite list_lookup_insert_eq in H5; try lia. inv H5. auto.
  }
  subst xr. split; intros.
  + destruct (Nat.eq_dec a i).
    * subst i. rewrite list_lookup_insert_eq in H4; try lia. inv H4.
      edestruct H1; eauto. apply H4. lia.
    * rewrite list_lookup_insert_ne in H4; auto.
      rewrite list_lookup_insert_ne in H4; try lia.
      edestruct H1; eauto. apply H10. lia.
  + rewrite list_lookup_insert_ne in H4; try lia.
    rewrite list_lookup_insert_ne in H4; try lia.
    edestruct H1; eauto.
Qed.

Lemma partition_restore_invariant:
  forall xs a b i_val j_val xi xj xa,
  (a < i_val <= j_val)%nat ∧ (j_val < b)%nat ∧ (b <= length xs) ->
  is_partitioned_pre xs a b i_val j_val ->
  xs !! a = Some xa -> xs !! i_val = Some xi -> xs !! j_val = Some xj ->
  xi ≽ xa -> xa ≽ xj ->
  is_partitioned_pre (<[j_val:=xi]> (<[i_val:=xj]> xs)) a b (i_val + 1)%nat (j_val - 1)%nat.
Proof.
  unfold is_partitioned_pre. intros.
  rewrite list_lookup_insert_ne in H7; try lia.
  rewrite list_lookup_insert_ne in H7; try lia.
  rewrite H7 in H1. inv H1.
  assert(length (<[i_val:=xj]> xs) = length xs) by apply length_insert.
  destruct (Nat.eq_dec i j_val).
  - subst j_val. rewrite list_lookup_insert_eq in H6; try lia.
    inv H6. destruct (Nat.eq_dec i_val i).
    + subst i_val. rewrite H2 in H3. inv H3. auto.
    + split; intros; try lia. edestruct H0; eauto.
  - rewrite list_lookup_insert_ne in H6; auto.
    destruct (Nat.eq_dec i_val i).
    + subst i_val. rewrite list_lookup_insert_eq in H6; try lia.
      inv H6. split; intros; try lia. auto.
    + rewrite list_lookup_insert_ne in H6; auto.
      edestruct (H0 i xi0); eauto.
      split; intros.
      * apply H8. lia.
      * apply H9. lia.
Qed.

Lemma wp_partitionCmpFunc (data: slice.t) (a b pivot: w64) (cmp_code: func.t)
                       (xs: list E):
  {{{ is_pkg_init slices ∗
      "Hxs" ∷ data ↦* xs ∗
      "%Hab_bound" ∷ ⌜ 0 ≤ sint.Z a < sint.Z b ∧ sint.Z b <= length xs <= 2 ^ 62⌝ ∗
      "#Hcmp" ∷ cmp_implements R cmp_code ∗
      "%pivot_range" ∷ ⌜ sint.Z a <= sint.Z pivot < sint.Z b ⌝
  }}}
    #(functions slices.partitionCmpFunc [Et]) #data #a #b #pivot #cmp_code
  {{{ (xs': list E) (bl: bool) (r: w64), RET (#r, #bl);
      data ↦* xs' ∗
      "%range" ∷ ⌜ sint.Z a <= sint.Z r < sint.Z b ⌝ ∗
      "%Hperm" ∷ ⌜ Permutation xs xs' ⌝ ∗
      "%Hpart" ∷ ⌜ is_partitioned xs' (sint.nat a) (sint.nat b) (sint.nat r) ⌝ ∗
      "%Houtside" ∷ ⌜ outside_same xs xs' (sint.nat a) (sint.nat b) ⌝
  }}}.
Proof using StrictWeakOrder0 + RelDecision0 + W.
  wp_start as "H". iNamed "H". wp_auto.
  iDestruct (own_slice_len with "Hxs") as "%Hlen".
  (* swap(data[a], data[pivot]) *)
  rewrite -> decide_True; last lia.
  assert(∃ x : E, xs !! sint.nat pivot = Some x). { apply list_lookup_lt. lia. } destruct H as [xp Hxp].
  wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

  rewrite -> decide_True; last lia.
  assert(∃ x : E, xs !! sint.nat a = Some x). { apply list_lookup_lt. lia. } destruct H as [xa Hxa].
  wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

  rewrite -> decide_True; last lia. wp_auto.
  wp_apply (wp_store_slice_index with "[$Hxs]") as "Hxs"; eauto; first word.

  assert(Hlen1: length (<[sint.nat a:=xp]> xs) = length xs) by apply length_insert.
  rewrite -> decide_True; last lia. wp_auto.
  wp_apply (wp_store_slice_index with "[$Hxs]") as "Hxs"; eauto; try word.

  set HI0 := ( ∃ xs1 (i_val j_val: w64),
    "Hxs" ∷ data ↦* xs1 ∗
    "i" ∷ i_ptr ↦ i_val ∗
    "j" ∷ j_ptr ↦ j_val ∗
    "%ij_bound" ∷ ⌜ sint.Z a + 1 <= sint.Z i_val <= sint.Z b ∧
                   sint.Z a <= sint.Z j_val <= sint.Z b - 1 ∧
                   sint.Z a <= sint.Z j_val ⌝ ∗
    "%Hpart" ∷ ⌜ is_partitioned_pre xs1 (sint.nat a) (sint.nat b) (sint.nat i_val) (sint.nat j_val) ⌝ ∗

    "%Hpivot" ∷ ⌜ xs1 !! (sint.nat a) = Some xp ⌝ ∗
    "%HPerm1" ∷ ⌜ Permutation xs xs1 ⌝ ∗
    "%Houtside1" ∷ ⌜ outside_same xs xs1 (sint.nat a) (sint.nat b) ⌝ ∗
    "a" ∷ a_ptr ↦ a ∗
    "data" ∷ data_ptr ↦ data ∗
    "cmp" ∷ cmp_ptr ↦ cmp_code
  )%I.
  set HI1 := ( ∃ xs1 (i_val j_val: w64),
    "Hxs" ∷ data ↦* xs1 ∗
    "i" ∷ i_ptr ↦ i_val ∗
    "j" ∷ j_ptr ↦ j_val ∗
    "%ij_bound" ∷ ⌜ sint.Z a + 1 <= sint.Z i_val <= sint.Z b ∧
                   sint.Z a <= sint.Z j_val <= sint.Z b - 1 ∧
                   sint.Z a <= sint.Z j_val ⌝ ∗
    "%Hpart" ∷ ⌜ is_partitioned_pre xs1 (sint.nat a) (sint.nat b) (sint.nat i_val) (sint.nat j_val) ⌝ ∗

    "%Hpivot" ∷ ⌜ xs1 !! (sint.nat a) = Some xp ⌝ ∗
    "%HPerm1" ∷ ⌜ Permutation xs xs1 ⌝ ∗
    "%Houtside1" ∷ ⌜ outside_same xs xs1 (sint.nat a) (sint.nat b) ⌝ ∗
    "%HBr1" ∷ ⌜ sint.Z i_val > sint.Z j_val ∨ forall xi, xs1 !! (sint.nat) i_val = Some xi -> xi ≽ xp ⌝ ∗
    "a" ∷ a_ptr ↦ a ∗
    "data" ∷ data_ptr ↦ data ∗
    "cmp" ∷ cmp_ptr ↦ cmp_code
  )%I.
  set HI2 := ( ∃ xs1 (i_val j_val: w64),
    "Hxs" ∷ data ↦* xs1 ∗
    "i" ∷ i_ptr ↦ i_val ∗
    "j" ∷ j_ptr ↦ j_val ∗
    "%ij_bound" ∷ ⌜ sint.Z a + 1 <= sint.Z i_val <= sint.Z b ∧
                   sint.Z a <= sint.Z j_val <= sint.Z b - 1 ∧
                   sint.Z a <= sint.Z j_val ⌝ ∗
    "%Hpart" ∷ ⌜ is_partitioned_pre xs1 (sint.nat a) (sint.nat b) (sint.nat i_val) (sint.nat j_val) ⌝ ∗

    "%Hpivot" ∷ ⌜ xs1 !! (sint.nat a) = Some xp ⌝ ∗
    "%HPerm1" ∷ ⌜ Permutation xs xs1 ⌝ ∗
    "%Houtside1" ∷ ⌜ outside_same xs xs1 (sint.nat a) (sint.nat b) ⌝ ∗
    "%HBr1" ∷ ⌜ sint.Z i_val > sint.Z j_val ∨ forall xi, xs1 !! (sint.nat) i_val = Some xi -> xi ≽ xp ⌝ ∗
    "%HBr2" ∷ ⌜ sint.Z i_val > sint.Z j_val ∨ forall xj, xs1 !! (sint.nat) j_val = Some xj -> xp ≽ xj ⌝ ∗
    "a" ∷ a_ptr ↦ a ∗
    "data" ∷ data_ptr ↦ data ∗
    "cmp" ∷ cmp_ptr ↦ cmp_code
  )%I.
  wp_bind. iApply ((wp_wand _ _ _ (fun v => ⌜ v = execute_val ⌝ ∗ HI1)%I) with "[a Hxs i j data cmp]").
  {
    iAssert(HI0) with "[a Hxs i j data cmp]" as "HI". {
      iFrame. iPureIntro. split; first word. split. { unfold is_partitioned_pre. intros. word. } split.
      - destruct (Nat.eq_dec (sint.nat pivot) (sint.nat a)) as [Heq | Hneq].
        + rewrite Heq in Hxp. rewrite Hxa in Hxp. inv Hxp.
          rewrite Heq. apply list_lookup_insert_eq. lia.
        + rewrite list_lookup_insert_ne; auto. apply list_lookup_insert_eq. lia.
      - split; try eapply swap_perm; eauto.
        apply outside_same_swap; lia.
    }
    wp_for "HI". wp_if_destruct.
    - assert(Hlen2: length xs = length xs1). { apply Permutation_length. auto. }
      assert(∃ x : E, xs1 !! sint.nat i_val = Some x). { apply list_lookup_lt. lia. } destruct H as [xi Hxi].

      rewrite -> decide_True; last lia.
      wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

      rewrite -> decide_True; last lia.
      wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

      wp_apply "Hcmp". iIntros (r) "%Hcmp_r". wp_auto. wp_if_destruct.
      + wp_for_post. iFrame. iPureIntro. split; first word. split. 2: split; eauto.
        replace (sint.nat (word.add i_val (W64 1))) with (sint.nat i_val + 1%nat)%nat by word.
        eapply is_partitioned_pre_advance_left; eauto.
        apply Hcmp_r in l0. apply R_antisym; auto.
      + iSplit; auto. unfold HI1. iFrame.
        iPureIntro. split; try lia. split; auto.
        split; auto. split; auto. split; auto.
        right. intros. rewrite H in Hxi. inv Hxi.
        apply comparison_negate in Hcmp_r. apply Hcmp_r. auto.
    - iSplit; auto. unfold HI1. iFrame.
      iPureIntro. split; auto.
      split; auto. split; auto. split; auto. split; auto. lia.
  }
  iIntros (v) "[%Hv HI]". subst v. wp_auto.

  wp_bind. iApply ((wp_wand _ _ _ (fun v => ⌜ v = execute_val ⌝ ∗ HI2)%I) with "[HI]").
  {
    wp_for "HI". wp_if_destruct.
    - assert(Hlen2: length xs = length xs1). { apply Permutation_length. auto. }
      assert(∃ x : E, xs1 !! sint.nat j_val = Some x). { apply list_lookup_lt. lia. } destruct H as [xj Hxj].

      rewrite -> decide_True; last lia.
      wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

      rewrite -> decide_True; last lia.
      wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

      wp_apply "Hcmp". iIntros (r) "%Hcmp_r". wp_auto. wp_if_destruct.
      + iSplit; auto. unfold HI2. iFrame.
        iPureIntro. split; try lia.
        split; auto. split; auto. split; auto. split; auto. split; auto.
        right. intros. rewrite H in Hxj. inv Hxj. apply R_antisym; auto.
        apply Hcmp_r. auto.
      + wp_for_post. iFrame. iPureIntro. split; first word.
        apply comparison_negate in Hcmp_r. apply Hcmp_r in n.
        split. 2: split; eauto.
        * replace (sint.nat (word.sub j_val (W64 1))) with (sint.nat j_val - 1%nat)%nat by word.
          eapply is_partitioned_pre_advance_right; eauto.
        * split; auto. split; auto. destruct HBr1; try lia. auto.
    - iSplit; auto. unfold HI2. iFrame. iPureIntro. split; auto; split; auto; split; auto.
      split; auto. split; auto. lia.
  }
  iIntros (v) "[%Hv HI]". subst v.
  unfold HI2.
  iNamed "HI". wp_auto.
  assert(Hlen2: length xs = length xs1). { apply Permutation_length. auto. }
  assert(∃ x : E, xs1 !! sint.nat j_val = Some x). { apply list_lookup_lt. lia. } destruct H as [xj Hxj].

  wp_if_destruct. {
    rewrite -> decide_True; last lia.
    wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

    rewrite -> decide_True; last lia.
    wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

    rewrite -> decide_True; last lia. wp_auto.
    wp_apply (wp_store_slice_index with "[$Hxs]") as "Hxs"; eauto; first word.

    rewrite -> decide_True; last lia. wp_auto.
    wp_apply (wp_store_slice_index with "[$Hxs]") as "Hxs"; eauto.
    { rewrite length_insert. word. }

    iApply "HΦ". iFrame. iPureIntro. split; first lia. split; try split.
    - eapply perm_trans; try eapply HPerm1. apply swap_perm; eauto.
    - eapply partition_conclude; try eapply Hpart; eauto; lia.
    - eapply outside_same_trans; try eapply Houtside1.
      eapply outside_same_swap; lia.
  }

  assert(∃ x : E, xs1 !! sint.nat i_val = Some x). { apply list_lookup_lt. lia. } destruct H as [xi Hxi].

  rewrite -> decide_True; last lia.
  wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

  rewrite -> decide_True; last lia.
  wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

  rewrite -> decide_True; last lia. wp_auto.
  wp_apply (wp_store_slice_index with "[$Hxs]") as "Hxs"; eauto; first word.

  assert(length (<[sint.nat i_val:=xj]> xs1) = length xs1) by apply length_insert.

  rewrite -> decide_True; last lia. wp_auto.
  wp_apply (wp_store_slice_index with "[$Hxs]") as "Hxs"; eauto; first word.

  iAssert HI0 with "[a Hxs i j data cmp]" as "HI".
  { unfold HI0. iFrame.
    iPureIntro. split; first word. split.
    - replace (sint.nat (word.add i_val (W64 1))) with (sint.nat i_val + 1%nat)%nat by word.
      replace (sint.nat (word.sub j_val (W64 1))) with (sint.nat j_val - 1%nat)%nat by word.
      eapply partition_restore_invariant; eauto; try lia.
      + destruct HBr1; try lia. auto.
      + destruct HBr2; try lia. auto.
    - split; try split.
      + rewrite list_lookup_insert_ne; try lia. rewrite list_lookup_insert_ne; try lia. auto.
      + eapply perm_trans; try eapply HPerm1. apply swap_perm; auto.
      + eapply outside_same_trans; try eapply Houtside1. apply outside_same_swap; lia.  }
  clear dependent xs1 xi xj. wp_for "HI".
  {
    wp_bind. iApply ((wp_wand _ _ _ (fun v => ⌜ v = execute_val ⌝ ∗ HI1)%I) with "[a Hxs i j data cmp]").
    {
      iAssert(HI0) with "[a Hxs i j data cmp]" as "HI". {
        iFrame. iPureIntro. split; first word. split; auto; split; auto.
      }
      clear dependent i_val j_val xs1.
      wp_for "HI". wp_if_destruct.
      - assert(Hlen2: length xs = length xs1). { apply Permutation_length. auto. }
        assert(∃ x : E, xs1 !! sint.nat i_val = Some x). { apply list_lookup_lt. lia. } destruct H as [xi Hxi].

        rewrite -> decide_True; last lia.
        wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

        rewrite -> decide_True; last lia.
        wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

        wp_apply "Hcmp". iIntros (r) "%Hcmp_r". wp_auto. wp_if_destruct.
        + wp_for_post. iFrame. iPureIntro. split; first word. split. 2: split; eauto.
          replace (sint.nat (word.add i_val (W64 1))) with (sint.nat i_val + 1%nat)%nat by word.
          eapply is_partitioned_pre_advance_left; eauto.
          apply Hcmp_r in l0. apply R_antisym; auto.
        + iSplit; auto. unfold HI1. iFrame.
          iPureIntro. split; try lia. split; auto.
          split; auto. split; auto. split; auto.
          right. intros. rewrite H in Hxi. inv Hxi.
          apply comparison_negate in Hcmp_r. apply Hcmp_r. auto.
      - iSplit; auto. unfold HI1. iFrame.
        iPureIntro. split; auto.
        split; auto. split; auto. split; auto. split; auto. lia.
    }
    iIntros (v) "[%Hv HI]". subst v. wp_auto.

    wp_bind. iApply ((wp_wand _ _ _ (fun v => ⌜ v = execute_val ⌝ ∗ HI2)%I) with "[HI]").
    {
      clear dependent i_val j_val xs1.
      wp_for "HI". wp_if_destruct.
      - assert(Hlen2: length xs = length xs1). { apply Permutation_length. auto. }
        assert(∃ x : E, xs1 !! sint.nat j_val = Some x). { apply list_lookup_lt. lia. } destruct H as [xj Hxj].

        rewrite -> decide_True; last lia.
        wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

        rewrite -> decide_True; last lia.
        wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

        wp_apply "Hcmp". iIntros (r) "%Hcmp_r". wp_auto. wp_if_destruct.
        + iSplit; auto. unfold HI2. iFrame.
          iPureIntro. split; try lia.
          split; auto. split; auto. split; auto. split; auto. split; auto.
          right. intros. rewrite H in Hxj. inv Hxj. apply R_antisym; auto.
          apply Hcmp_r. auto.
        + wp_for_post. iFrame. iPureIntro. split; first word.
          apply comparison_negate in Hcmp_r. apply Hcmp_r in n.
          split. 2: split; eauto.
          * replace (sint.nat (word.sub j_val (W64 1))) with (sint.nat j_val - 1%nat)%nat by word.
            eapply is_partitioned_pre_advance_right; eauto.
          * split; auto. split; auto. destruct HBr1; try lia. auto.
      - iSplit; auto. unfold HI2. iFrame. iPureIntro. split; auto; split; auto; split; auto.
        split; auto. split; auto. lia.
    }
      iIntros (v) "[%Hv HI]". subst v. wp_auto.
      clear dependent i_val j_val xs1.
      unfold HI2. iNamed "HI".

      assert(Hlen2: length xs = length xs1). { apply Permutation_length. auto. }
      assert(∃ x : E, xs1 !! sint.nat j_val = Some x). { apply list_lookup_lt. lia. } destruct H as [xj Hxj].
      wp_auto. wp_if_destruct. {
        wp_for_post.
        rewrite -> decide_True; last lia.
        wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

        rewrite -> decide_True; last lia.
        wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

        rewrite -> decide_True; last lia. wp_auto.
        wp_apply (wp_store_slice_index with "[$Hxs]") as "Hxs"; eauto; first word.

        rewrite -> decide_True; last lia. wp_auto.
        wp_apply (wp_store_slice_index with "[$Hxs]") as "Hxs"; eauto.
        { rewrite length_insert. word. }

        iApply "HΦ". iFrame. iPureIntro. split; first lia. split; try split.
        - eapply perm_trans; try eapply HPerm1. apply swap_perm; eauto.
        - eapply partition_conclude; try eapply Hpart; eauto; lia.
        - eapply outside_same_trans; try eapply Houtside1.
          eapply outside_same_swap; lia.
    }
    assert(∃ x : E, xs1 !! sint.nat i_val = Some x). { apply list_lookup_lt. lia. } destruct H as [xi Hxi].

    rewrite -> decide_True; last lia.
    wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

    rewrite -> decide_True; last lia.
    wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

    rewrite -> decide_True; last lia. wp_auto.
    wp_apply (wp_store_slice_index with "[$Hxs]") as "Hxs"; eauto; first word.

    assert(length (<[sint.nat i_val:=xj]> xs1) = length xs1) by apply length_insert.

    rewrite -> decide_True; last lia. wp_auto.
    wp_apply (wp_store_slice_index with "[$Hxs]") as "Hxs"; eauto; first word.

    wp_for_post. iFrame. iPureIntro. split; first word. split.
      - replace (sint.nat (word.add i_val (W64 1))) with (sint.nat i_val + 1%nat)%nat by word.
        replace (sint.nat (word.sub j_val (W64 1))) with (sint.nat j_val - 1%nat)%nat by word.
        eapply partition_restore_invariant; eauto; try lia.
        + destruct HBr1; try lia. auto.
        + destruct HBr2; try lia. auto.
      - split; try split.
        + rewrite list_lookup_insert_ne; try lia. rewrite list_lookup_insert_ne; try lia. auto.
        + eapply perm_trans; try eapply HPerm1. apply swap_perm; auto.
        + eapply outside_same_trans; try eapply Houtside1. apply outside_same_swap; lia.
    }
Qed.


Lemma wp_medianCmpFunc (data: slice.t) (a b c: w64) (swaps_l: loc) (cmp_code: func.t)
                       dq (xs: list E) (swaps: w64):
  {{{ is_pkg_init slices ∗
      "Hxs" ∷ data ↦*{dq} xs ∗
      "%Hbounds" ∷ ⌜ 0 <= sint.Z a < Z.of_nat (length xs) ∧
                    0 <= sint.Z b < Z.of_nat (length xs) ∧
                    0 <= sint.Z c < Z.of_nat (length xs) ⌝ ∗
      "Hswaps" ∷ swaps_l ↦ swaps ∗
      "#Hcmp" ∷ cmp_implements R cmp_code
  }}}
    #(functions slices.medianCmpFunc [Et]) #data #a #b #c #swaps_l #cmp_code
  {{{ (r: w64) (swaps': w64), RET (#r);
      data ↦*{dq} xs ∗
      ⌜ (r = a) ∨ (r = b) ∨ (r = c) ⌝ ∗
      swaps_l ↦ swaps'
  }}}.
Proof using StrictWeakOrder0 + W.
  wp_start as "H". iNamed "H". wp_auto.
  assert( ∃ xa, xs !! sint.nat a = Some xa). { apply list_lookup_lt. lia. } destruct H as [xa Hxa].
  assert( ∃ xb, xs !! sint.nat b = Some xb). { apply list_lookup_lt. lia. } destruct H as [xb Hxb].
  assert( ∃ xc, xs !! sint.nat c = Some xc). { apply list_lookup_lt. lia. } destruct H as [xc Hxc].
  wp_apply (wp_order2CmpFunc with "[$Hxs $Hswaps]"); try lia. { iSplit; eauto. }
  iIntros (a1 b1 swaps1) "Hpost1". iDestruct "Hpost1" as "(Hxs & %Ha1b1 & Hswap1)".
  wp_auto. destruct Ha1b1; destruct H as (Ha1 & Hb1 & _); subst a1; subst b1.
  - wp_apply (wp_order2CmpFunc with "[$Hxs $Hswap1]"); try lia. { iSplit; eauto. }
    iIntros (b1 c1 swaps2) "Hpost1". iDestruct "Hpost1" as "(Hxs & %Hb1c1 & Hswap1)".
    destruct Hb1c1; destruct H as (Ha1 & Hb1 & _); subst b1; subst c1.
    + wp_auto. wp_apply (wp_order2CmpFunc with "[$Hxs $Hswap1]"); try lia. { iSplit; eauto. }
      iIntros (b1 c1 swaps3) "Hpost1". iDestruct "Hpost1" as "(Hxs & %Hb1c1 & Hswap1)".
      wp_auto. iApply "HΦ". iFrame. destruct Hb1c1; destruct H as (Ha1 & Hb1 & _); subst b1; subst c1; auto.
    + wp_auto. wp_apply (wp_order2CmpFunc with "[$Hxs $Hswap1]"); try lia. { iSplit; eauto. }
      iIntros (b1 c1 swaps3) "Hpost1". iDestruct "Hpost1" as "(Hxs & %Hb1c1 & Hswap1)".
      wp_auto. iApply "HΦ". iFrame. destruct Hb1c1; destruct H as (Ha1 & Hb1 & _); subst b1; subst c1; auto.
  - wp_apply (wp_order2CmpFunc with "[$Hxs $Hswap1]"); try lia. { iSplit; eauto. }
    iIntros (b1 c1 swaps2) "Hpost1". iDestruct "Hpost1" as "(Hxs & %Hb1c1 & Hswap1)".
    destruct Hb1c1; destruct H as (Ha1 & Hb1 & _); subst b1; subst c1.
    + wp_auto. wp_apply (wp_order2CmpFunc with "[$Hxs $Hswap1]"); try lia. { iSplit; eauto. }
      iIntros (b1 c1 swaps3) "Hpost1". iDestruct "Hpost1" as "(Hxs & %Hb1c1 & Hswap1)".
      wp_auto. iApply "HΦ". iFrame. destruct Hb1c1; destruct H as (Ha1 & Hb1 & _); subst b1; subst c1; auto.
    + wp_auto. wp_apply (wp_order2CmpFunc with "[$Hxs $Hswap1]"); try lia. { iSplit; eauto. }
      iIntros (b1 c1 swaps3) "Hpost1". iDestruct "Hpost1" as "(Hxs & %Hb1c1 & Hswap1)".
      wp_auto. iApply "HΦ". iFrame. destruct Hb1c1; destruct H as (Ha1 & Hb1 & _); subst b1; subst c1; auto.
Qed.

Lemma wp_medianAdjacentCmpFunc (data: slice.t) (a: w64) (swaps_l: loc) (cmp_code: func.t)
                       dq (xs: list E) (swaps: w64):
  {{{ is_pkg_init slices ∗
      "Hxs" ∷ data ↦*{dq} xs ∗
      "%Hbounds" ∷ ⌜ 1 <= sint.Z a < length xs - 1 ∧ length xs <= 2 ^ 62 ⌝ ∗
      "Hswaps" ∷ swaps_l ↦ swaps ∗
      "#Hcmp" ∷ cmp_implements R cmp_code
  }}}
    #(functions slices.medianAdjacentCmpFunc [Et]) #data #a #swaps_l #cmp_code
  {{{ (r: w64) (swaps': w64), RET (#r);
      data ↦*{dq} xs ∗
      ⌜ (sint.Z a - 1 <= sint.Z r <= sint.Z a + 1) ⌝ ∗
      swaps_l ↦ swaps'
  }}}.
Proof using StrictWeakOrder0 + W.
  wp_start as "H". iNamed "H". wp_auto.
  wp_apply (wp_medianCmpFunc with "[$Hxs $Hswaps]").
  { iFrame. iSplit; auto. word. }
  iIntros (r swaps1) "(Hxs & %Hr & HSwap)".
  wp_auto. iApply "HΦ". iFrame. word.
Qed.

Lemma wp_choosePivotCmpFunc (data: slice.t) (a b: w64) (cmp_code: func.t)
                       (xs: list E):
  {{{ is_pkg_init slices ∗
      "Hxs" ∷ data ↦* xs ∗
      "#Hcmp" ∷ cmp_implements R cmp_code ∗
      "%Hab_bound" ∷ ⌜ 0 ≤ sint.Z a < sint.Z b ∧ sint.Z b ≤ length xs ∧ length xs <= 2 ^ 62⌝
  }}}
    #(functions slices.choosePivotCmpFunc [Et]) #data #a #b #cmp_code
  {{{ (r: w64) (hint: slices.sortedHint.t), RET (#r, #hint);
      data ↦* xs ∗
      "%Hr_bound" ∷ ⌜ sint.Z a ≤ sint.Z r < sint.Z b ⌝
  }}}.
Proof using StrictWeakOrder0 + W.
  wp_start as "H". iNamed "H". wp_auto.
  assert(Hword1: sint.Z (word.sub b a) = sint.Z b - sint.Z a) by word.
  assert(Hword2: sint.Z (word.divs (word.sub b a) (W64 4)) = (sint.Z b - sint.Z a) / 4).
  { pose proof Automation.word.word_signed_divs_nowrap_pos (word.sub b a) (W64 4).
    rewrite Hword1 in H. apply H. word. }
  wp_if_destruct.
  - wp_if_destruct.
    + wp_apply (wp_medianAdjacentCmpFunc with "[$Hxs $swaps]"). { iSplit; first word. auto. }
      iIntros (r1 swap1) "Hpost". iDestruct "Hpost" as "(Hxs & %Hbounds1 & swaps)". wp_auto.

      wp_apply (wp_medianAdjacentCmpFunc with "[$Hxs $swaps]"). { iSplit; first word. auto. }
      iIntros (r2 swap2) "Hpost". iDestruct "Hpost" as "(Hxs & %Hbounds2 & swaps)". wp_auto.

      wp_apply (wp_medianAdjacentCmpFunc with "[$Hxs $swaps]"). { iSplit; first word. auto. }
      iIntros (r3 swap3) "Hpost". iDestruct "Hpost" as "(Hxs & %Hbounds3 & swaps)". wp_auto.

      wp_apply (wp_medianCmpFunc with "[$Hxs $swaps]"). { iSplit; first word. auto. }
      iIntros (r4 swap4) "Hpost". iDestruct "Hpost" as "(Hxs & %Hbounds4 & swaps)". wp_auto.

      assert(sint.Z a <= sint.Z r4 < sint.Z b). { word. }
      wp_if_destruct.
      * iApply "HΦ". iFrame; auto.
      * wp_if_destruct.
        -- iApply "HΦ". iFrame; auto.
        -- iApply "HΦ". iFrame; auto.
    + wp_apply (wp_medianCmpFunc with "[$Hxs $swaps]"). { iSplit; first word. auto. }
      iIntros (r swap) "Hpost". iDestruct "Hpost" as "(Hxs & %Hbounds4 & swaps)". wp_auto.
      assert(sint.Z a <= sint.Z r < sint.Z b). { word. }
      wp_if_destruct.
      * iApply "HΦ". iFrame; auto.
      * wp_if_destruct.
        -- iApply "HΦ". iFrame; auto.
        -- iApply "HΦ". iFrame; auto.
  - iApply "HΦ". iFrame. iPureIntro. split; word.
Qed.

Lemma wp_breakPatternsCmpFunc (data: slice.t) (a b: w64) (cmp_code: func.t)
                       (xs: list E):
  {{{ is_pkg_init slices ∗
      "Hxs" ∷ data ↦* xs ∗
      "%Hab_bound" ∷ ⌜ 0 ≤ sint.Z a < sint.Z b ∧ sint.Z b <= length xs <= 2 ^ 62⌝ ∗
      "#Hcmp" ∷ cmp_implements R cmp_code ∗
      "%pivot_range" ∷ ⌜ sint.Z a < sint.Z b ⌝
  }}}
    #(functions slices.breakPatternsCmpFunc [Et]) #data #a #b #cmp_code
  {{{ (xs': list E), RET #();
      data ↦* xs' ∗
      "%Hperm" ∷ ⌜ Permutation xs xs' ⌝ ∗
      "%Houtside" ∷ ⌜ outside_same xs xs' (sint.nat a) (sint.nat b) ⌝
  }}}.
Admitted.

Definition is_eq_seg (xs: list E) a b :=
  forall i j xi xj, (a <= i < j)%nat ∧ (j < b)%nat ->
  xs !! i = Some xi -> xs !! j = Some xj -> xj ≽ xi /\ xi ≽ xj.


Theorem is_eq_seg_extend:
  forall xs a i xp xi,
  xs !! a = Some xp -> is_eq_seg xs a i ->
  xs !! i%nat = Some xi ->
  xi ≽ xp /\ xp ≽ xi ->
  is_eq_seg xs a (i + 1)%nat.
Proof using StrictWeakOrder0.
  unfold is_eq_seg. intros.
  destruct StrictWeakOrder0. destruct strict_weak_order_equiv.
  destruct (Nat.eq_dec i j) as [Heq | Hneq].
  - subst j. rewrite H1 in H5. inv H5.
    rename xi0 into xi. rename i into j. rename i0 into i.
    eapply Equivalence_Transitive; eauto.
    destruct (Nat.eq_dec i a) as [Heq2 | Hneq2].
    + subst a. rewrite H in H4. inv H4. split; apply notR_refl; auto.
    + edestruct H0. 2: eapply H. 2: eapply H4. 1: lia. auto.
  - eapply H0; eauto. lia.
Qed.

Theorem is_eq_seg__is_sorted_seg:
  forall xs a b,
  is_eq_seg xs a b -> is_sorted_seg R xs a b.
Proof.
  unfold is_eq_seg. unfold is_sorted_seg. intros.
  edestruct H; eauto.
Qed.

Definition is_eq_partitioned (xs: list E) (a b r: nat) :=
    ∀ i j xi xj,
      xs !! i = Some xi -> xs !! j = Some xj ->
        ((a <= i)%nat /\ (i < j < b)%nat /\ (i < r)%nat)-> xj ≽ xi.

Lemma wp_partitionEqualCmpFunc (data: slice.t) (a b pivot: w64) (cmp_code: func.t)
                       (xs: list E):
  {{{ is_pkg_init slices ∗
      "Hxs" ∷ data ↦* xs ∗
      "%Hab_bound" ∷ ⌜ 0 ≤ sint.Z a < sint.Z b ∧ sint.Z b <= length xs <= 2 ^ 62⌝ ∗
      "#Hcmp" ∷ cmp_implements R cmp_code ∗
      "%pivot_range" ∷ ⌜ sint.Z a <= sint.Z pivot < sint.Z b ⌝ ∗
      "%Hmin" ∷ ⌜ one_le_seg R xs (sint.nat pivot) (sint.nat a) (sint.nat b) ⌝
  }}}
    #(functions slices.partitionEqualCmpFunc [Et]) #data #a #b #pivot #cmp_code
  {{{ (xs': list E) (r: w64), RET (#r);
      data ↦* xs' ∗
      "%range" ∷ ⌜ sint.Z a < sint.Z r <= sint.Z b ⌝ ∗
      "%Hperm" ∷ ⌜ Permutation xs xs' ⌝ ∗
      "%Hpart" ∷ ⌜ is_eq_partitioned xs' (sint.nat a) (sint.nat b) (sint.nat r) ⌝ ∗
      "%Houtside" ∷ ⌜ outside_same xs xs' (sint.nat a) (sint.nat b) ⌝
  }}}.
Proof using StrictWeakOrder0 + RelDecision0 + W.
  wp_start as "H". iNamed "H". wp_auto.
  iDestruct (own_slice_len with "Hxs") as "%Hlen".
  (* swap(data[a], data[pivot]) *)
  rewrite -> decide_True; last lia.
  assert(∃ x : E, xs !! sint.nat pivot = Some x). { apply list_lookup_lt. lia. } destruct H as [xp Hxp].
  wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

  rewrite -> decide_True; last lia.
  assert(∃ x : E, xs !! sint.nat a = Some x). { apply list_lookup_lt. lia. } destruct H as [xa Hxa].
  wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

  rewrite -> decide_True; last lia. wp_auto.
  wp_apply (wp_store_slice_index with "[$Hxs]") as "Hxs"; eauto; first word.

  assert(Hlen1: length (<[sint.nat a:=xp]> xs) = length xs) by apply length_insert.
  rewrite -> decide_True; last lia. wp_auto.
  wp_apply (wp_store_slice_index with "[$Hxs]") as "Hxs"; eauto; try word.

  set Hunchanged := (
    "a" ∷ a_ptr ↦ a ∗
    "data" ∷ data_ptr ↦ data ∗
    "cmp" ∷ cmp_ptr ↦ cmp_code
  )%I.
  set HI0 := ( ∃ xs1 (i_val j_val: w64),
    "Hxs" ∷ data ↦* xs1 ∗
    "i" ∷ i_ptr ↦ i_val ∗
    "j" ∷ j_ptr ↦ j_val ∗
    "%ij_bound" ∷ ⌜ sint.Z a + 1 <= sint.Z i_val <= sint.Z b ∧
                   sint.Z a <= sint.Z j_val <= sint.Z b - 1 ∧
                   sint.Z a <= sint.Z j_val ⌝ ∗
    "%Hsorted" ∷ ⌜ is_eq_seg xs1 (sint.nat a) (sint.nat i_val) ⌝ ∗
    "%Hpivot" ∷ ⌜ xs1 !! (sint.nat a) = Some xp ⌝ ∗
    "%Hmin" ∷ ⌜ one_le_seg R xs1 (sint.nat a) (sint.nat a) (sint.nat b) ⌝ ∗
    "%HPerm1" ∷ ⌜ Permutation xs xs1 ⌝ ∗
    "%Houtside1" ∷ ⌜ outside_same xs xs1 (sint.nat a) (sint.nat b) ⌝ ∗
    Hunchanged
  )%I.
  set HI1 := ( ∃ xs1 (i_val j_val: w64),
    "Hxs" ∷ data ↦* xs1 ∗
    "i" ∷ i_ptr ↦ i_val ∗
    "j" ∷ j_ptr ↦ j_val ∗
    "%ij_bound" ∷ ⌜ sint.Z a + 1 <= sint.Z i_val <= sint.Z b ∧
                   sint.Z a <= sint.Z j_val <= sint.Z b - 1 ∧
                   sint.Z a <= sint.Z j_val ⌝ ∗
    "%Hsorted" ∷ ⌜ is_eq_seg xs1 (sint.nat a) (sint.nat i_val) ⌝ ∗
    "%Hpivot" ∷ ⌜ xs1 !! (sint.nat a) = Some xp ⌝ ∗
    "%Hmin" ∷ ⌜ one_le_seg R xs1 (sint.nat a) (sint.nat a) (sint.nat b) ⌝ ∗
    "%HPerm1" ∷ ⌜ Permutation xs xs1 ⌝ ∗
    "%Houtside1" ∷ ⌜ outside_same xs xs1 (sint.nat a) (sint.nat b) ⌝ ∗
    "%HBr1" ∷ ⌜ sint.Z i_val > sint.Z j_val ∨ forall xi, xs1 !! (sint.nat) i_val = Some xi -> xi ≽ xp ⌝ ∗
    Hunchanged
  )%I.
  set HI2 := ( ∃ xs1 (i_val j_val: w64),
    "Hxs" ∷ data ↦* xs1 ∗
    "i" ∷ i_ptr ↦ i_val ∗
    "j" ∷ j_ptr ↦ j_val ∗
    "%ij_bound" ∷ ⌜ sint.Z a + 1 <= sint.Z i_val <= sint.Z b ∧
                   sint.Z a <= sint.Z j_val <= sint.Z b - 1 ∧
                   sint.Z a <= sint.Z j_val ⌝ ∗
    "%Hsorted" ∷ ⌜ is_eq_seg xs1 (sint.nat a) (sint.nat i_val) ⌝ ∗
    "%Hpivot" ∷ ⌜ xs1 !! (sint.nat a) = Some xp ⌝ ∗
    "%Hmin" ∷ ⌜ one_le_seg R xs1 (sint.nat a) (sint.nat a) (sint.nat b) ⌝ ∗
    "%HPerm1" ∷ ⌜ Permutation xs xs1 ⌝ ∗
    "%Houtside1" ∷ ⌜ outside_same xs xs1 (sint.nat a) (sint.nat b) ⌝ ∗
    "%HBr1" ∷ ⌜ sint.Z i_val > sint.Z j_val ∨ forall xi, xs1 !! (sint.nat) i_val = Some xi -> xi ≽ xp ⌝ ∗
    "%HBr2" ∷ ⌜ sint.Z i_val > sint.Z j_val ∨ forall xj, xs1 !! (sint.nat) j_val = Some xj -> xp ≽ xj ⌝ ∗
    Hunchanged
  )%I.

  iAssert HI0 with "[a Hxs i j data cmp]" as "HI".
  { unfold HI0. iFrame.
    iPureIntro. replace (sint.Z (word.add a (W64 1))) with (sint.Z a + 1) by word.
    replace (sint.Z (word.sub b (W64 1))) with (sint.Z b - 1) by word. split; first lia.
    assert(length (<[sint.nat pivot:=xp]> xs) = length xs) by apply length_insert. split.
    - unfold is_eq_seg. intros. lia.
    - split; try split; try split.
      + destruct (Nat.eq_dec (sint.nat a) (sint.nat pivot)) as [Heq | Hneq].
        * rewrite Heq. rewrite list_lookup_insert_eq; try lia.
          rewrite Heq in Hxa. rewrite <- Hxa. auto.
        * rewrite list_lookup_insert_ne; auto.
          rewrite list_lookup_insert_eq; auto. lia.
      + {
        clear HI0 HI1 HI2 Hunchanged. unfold one_le_seg in *.
        destruct (Nat.eq_dec (sint.nat a) (sint.nat pivot)) as [Heq | Hneq].
        - inv Heq. intros. rewrite list_lookup_insert_eq in H2; try lia. inv H1.
          rewrite <- H5 in Hxp, H, Hmin.
          destruct (Nat.eq_dec (sint.nat a) j) as [Heq1 | Hneq1].
          + inv Heq1. rewrite list_lookup_insert_eq in H3; try lia.
            inv H3. apply notR_refl. auto.
          + rewrite list_lookup_insert_ne in H3; auto.
            rewrite list_lookup_insert_ne in H3; auto.
            eapply Hmin; eauto.
        - intros. rewrite list_lookup_insert_ne in H1; auto.
          rewrite list_lookup_insert_eq in H1; try lia. inv H1.
          destruct (Nat.eq_dec (sint.nat pivot) j) as [Heq1 | Hneq1].
          + inv Heq1. rewrite list_lookup_insert_eq in H2; try lia. inv H2.
            eapply Hmin; try eapply Hxp; try eapply Hxa. lia.
          + rewrite list_lookup_insert_ne in H2; auto.
            destruct (Nat.eq_dec (sint.nat a) j) as [Heq2 | Hneq2].
            * inv Heq2. rewrite list_lookup_insert_eq in H2; try lia.
              inv H2. apply notR_refl. auto.
            * rewrite list_lookup_insert_ne in H2; auto.
              eapply Hmin; eauto.
      }
      + apply swap_perm; auto.
      + apply outside_same_swap; lia.  }
  wp_for "HI".
  {
    wp_bind. iApply ((wp_wand _ _ _ (fun v => ⌜ v = execute_val ⌝ ∗ HI1)%I) with "[a Hxs i j data cmp]").
    {
      iAssert(HI0) with "[a Hxs i j data cmp]" as "HI". {
        iFrame. iPureIntro. split; first word. split; auto; split; auto.
      }
      clear dependent i_val j_val xa xs1.
      wp_for "HI". wp_if_destruct.
      - assert(Hlen2: length xs = length xs1). { apply Permutation_length. auto. }

        rewrite -> decide_True; last lia.
        wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

        assert(∃ x : E, xs1 !! sint.nat i_val = Some x). { apply list_lookup_lt. lia. }
        destruct H as [xi Hxi].

        rewrite -> decide_True; last lia.
        wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

        wp_apply "Hcmp". iIntros (r) "%Hcmp_r". wp_auto. wp_if_destruct.
        + iSplit; auto. unfold HI1. iFrame.
          iPureIntro. split; first word.
          split; auto. split; auto. split; auto.
          split; auto. split; auto. right. intros.
          rewrite H in Hxi. inv Hxi. apply R_antisym; auto.
          apply Hcmp_r. auto.
        + wp_for_post. unfold HI0. iFrame.
          replace (sint.Z (word.add i_val (W64 1))) with (sint.Z i_val + 1) by word.
          iPureIntro. split; first lia. split.
          * replace (Z.to_nat (sint.Z i_val + 1)) with (sint.nat i_val + 1)%nat by lia.
            eapply is_eq_seg_extend; eauto.
            apply comparison_negate in Hcmp_r.
            apply Hcmp_r in n. split; auto.
            unfold one_le_seg in Hmin0.
            eapply Hmin0; eauto. lia.
          * auto.
      - iSplit; auto. unfold HI1. iFrame.
        iPureIntro. split; auto.
        split; auto. split; auto. split; auto. split; auto.
        split; auto. lia.
    }
    iIntros (v) "[%Hv HI]". subst v. wp_auto.

    wp_bind. iApply ((wp_wand _ _ _ (fun v => ⌜ v = execute_val ⌝ ∗ HI2)%I) with "[HI]").
    {
      clear dependent i_val j_val xs1.
      wp_for "HI". wp_if_destruct.
      - assert(Hlen2: length xs = length xs1). { apply Permutation_length. auto. }

        rewrite -> decide_True; last lia.
        wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

        assert(∃ x : E, xs1 !! sint.nat j_val = Some x). { apply list_lookup_lt. lia. }
        destruct H as [xj Hxj].

        rewrite -> decide_True; last lia.
        wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

        wp_apply "Hcmp". iIntros (r) "%Hcmp_r". wp_auto. wp_if_destruct.
        + wp_for_post. unfold HI1. iFrame. iPureIntro.
          replace (sint.Z (word.sub j_val (W64 1))) with (sint.Z j_val - 1) by word.
          split; first lia.
          split; auto. split; auto. split; auto. split; auto.
          split; auto. destruct HBr1; auto.
        + iSplit; auto. unfold HI2. iFrame.
          iPureIntro. split; try lia.
          split; auto. split; auto. split; auto. split; auto. split; auto.
          split; auto.
          right. intros. rewrite H in Hxj. inv Hxj.
          apply comparison_negate in Hcmp_r. apply Hcmp_r. apply n.
      - iSplit; auto. unfold HI2. iFrame. iPureIntro. split; auto; split; auto; split; auto.
        split; auto. split; auto. split; auto. split; auto.
        left. lia.
    }
    iIntros (v) "[%Hv HI]". subst v. wp_auto.
    clear dependent i_val j_val xs1.
    unfold HI2. iNamed "HI".
    wp_auto. wp_if_destruct. {
      wp_for_post. iApply "HΦ". iFrame. iPureIntro.
      split; first lia.
      split; first auto. split; auto.
      unfold is_eq_partitioned. intros. unfold is_eq_seg in Hsorted.
      destruct (decide (j < sint.nat i_val)).
      - edestruct (Hsorted i j); eauto. lia.
      - assert(¬ xi ≺ xp ∧ ¬ xp ≺ xi). {
          destruct (Nat.eq_dec i (sint.nat a)).
          - subst i. rewrite H in Hpivot. inv Hpivot.
          split; apply notR_refl; auto.
          - eapply Hsorted; eauto. lia.  }
        destruct H2. eapply notR_trans; eauto.
        unfold one_le_seg in Hmin0. eapply Hmin0; eauto. lia.
    }

    assert(Hlen2: length xs = length xs1). { apply Permutation_length. auto. }
    assert(∃ x : E, xs1 !! sint.nat j_val = Some x).
    { apply list_lookup_lt. lia. } destruct H as [xj Hxj].

    assert(∃ x : E, xs1 !! sint.nat i_val = Some x).
    { apply list_lookup_lt. lia. } destruct H as [xi Hxi].

    rewrite -> decide_True; last lia.
    wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

    rewrite -> decide_True; last lia.
    wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto; try lia.

    rewrite -> decide_True; last lia. wp_auto.
    wp_apply (wp_store_slice_index with "[$Hxs]") as "Hxs"; eauto; first word.

    assert(length (<[sint.nat i_val:=xj]> xs1) = length xs1) by apply length_insert.

    rewrite -> decide_True; last lia. wp_auto.
    wp_apply (wp_store_slice_index with "[$Hxs]") as "Hxs"; eauto; first word.

    wp_for_post. iFrame. iPureIntro. clear HI0 HI1 HI2 Hunchanged. split; first word.
    destruct HBr2 as [HBr2 | HBr2]; try lia. split.
      - replace (sint.nat (word.add i_val (W64 1))) with (sint.nat i_val + 1%nat)%nat by word.
        eapply (is_eq_seg_extend _ _ _ xp xj).
        + rewrite list_lookup_insert_ne; try lia. rewrite list_lookup_insert_ne; try lia. eauto.
        + unfold is_eq_seg in *. intros.
          rewrite list_lookup_insert_ne in H1; try lia. rewrite list_lookup_insert_ne in H1; try lia.
          rewrite list_lookup_insert_ne in H2; try lia. rewrite list_lookup_insert_ne in H2; try lia.
          eapply Hsorted; eauto.
        + destruct (Nat.eq_dec (sint.nat i_val) (sint.nat j_val)).
          * rewrite e. rewrite e in H Hxi. rewrite Hxi in Hxj. symmetry in Hxj.
            injection Hxj. intros. subst xi.
            rewrite list_lookup_insert_eq; try lia. eauto.
          * rewrite list_lookup_insert_ne; auto. rewrite list_lookup_insert_eq; try lia.
            auto.
        + split; auto. unfold one_le_seg in Hmin0. eapply Hmin0; eauto. lia.
      - split; try split; try split.
        + rewrite list_lookup_insert_ne; try lia. rewrite list_lookup_insert_ne; try lia. auto.
        + unfold one_le_seg. rewrite list_lookup_insert_ne; try lia.
          rewrite list_lookup_insert_ne; try lia. intros.
          rewrite H1 in Hpivot. inv Hpivot.
          unfold one_le_seg in Hmin0. {
            destruct (Nat.eq_dec (sint.nat j_val) j) as [Heq | Hneq].
            - subst j. rewrite list_lookup_insert_eq in H2; try lia. inv H2.
              eapply Hmin0; try eapply Hxi; eauto. lia.
            - rewrite list_lookup_insert_ne in H2; auto.
              destruct (Nat.eq_dec (sint.nat i_val) j) as [Heq2 | Hneq2].
              + subst j. rewrite list_lookup_insert_eq in H2; try lia. inv H2.
                eapply Hmin0; try eapply Hxj; eauto. lia.
              + rewrite list_lookup_insert_ne in H2; auto.
                eapply Hmin0; eauto.
          }
        + eapply perm_trans; eauto. eapply swap_perm; eauto.
        + eapply outside_same_trans; try eapply Houtside1. apply outside_same_swap; lia.
    }
Qed.

End proof.
