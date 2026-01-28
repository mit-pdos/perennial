From New.generatedproof Require Import slices.
From New.proof Require Import proof_prelude.
From New.proof.slices_proof Require Import slices_init.
From New.proof.slices_proof.pdqSort Require Import sort_basics partition insertionSort heapSort.

Section proof.
Context  `{hG: heapGS Σ, !ffi_semantics _ _} `{!globalsGS Σ} {go_ctx : GoContext}.

Context `{!IntoVal E} `{!IntoValTyped E Et} `{!BoundedTypeSize Et}.
Context (R: E → E → Prop) `{!StrictWeakOrder R} `{!RelDecision R}.

#[local] Infix "≺" := R (at level 70).
#[local] Notation "x ≽ y" := (¬ R x y) (at level 70, only parsing).

Definition is_partially_sorted_seg (l: list E) (a b: nat) (a1 b1: nat) :=
  forall i j xi xj, (a <= i < j)%nat ∧ (j < b)%nat ->
  (i < a1)%nat ∨ (j >= b1)%nat ->
  l !! i = Some xi -> l !! j = Some xj -> xj ≽ xi.
  
Theorem close_segment: forall xs xs' a b a_val b_val,
  outside_same xs xs' a_val b_val ->
  Permutation xs xs' ->
  is_partially_sorted_seg xs a b a_val b_val ->
  is_sorted_seg R xs' a_val b_val ->
  (a_val <= b_val)%nat ∧ (a <= a_val)%nat ∧ (b >= b_val)%nat ∧ (b <= length xs)%nat ->
  is_sorted_seg R xs' a b.
Proof.
  unfold is_sorted_seg. intros. 
  rename H1 into Hold. rename H2 into Hnew.
  assert(Hlen: length xs = length xs') by (apply Permutation_length; auto).
  destruct (decide (i < a_val)%nat); destruct (decide (j >= b_val)%nat).
  - rewrite <- H in H5; try lia. 
    rewrite <- H in H6; try lia.
    eapply Hold; eauto.
  - rewrite <- H in H5; try lia.
    destruct (decide (j < a_val)%nat).
    + rewrite <- H in H6; try lia. eapply Hold; eauto.
    + pose proof (Permutation_existsIndex xs' xs j a_val b_val xj).
      destruct H1; eauto. { symmetry. auto. } 
      { unfold outside_same in *. intros. rewrite H; auto. }
      { lia. } rename x into j0. destruct H1. 
      eapply Hold; try eapply H1; eauto. lia.
    
  - rewrite <- H in H6; try lia.
    destruct (decide (i >= b_val)%nat).
    + rewrite <- H in H5; try lia. eapply Hold; eauto.
    + pose proof (Permutation_existsIndex xs' xs i a_val b_val xi).
      destruct H1; eauto. { symmetry. auto. }
      { unfold outside_same in *. intros. rewrite H; auto. }
      { lia. } rename x into i0. destruct H1.
      eapply Hold; try eapply H1; eauto. lia.
  - eapply Hnew; eauto. lia.
Qed.

Theorem is_partially_sorted_seg__perserve:
  forall xs xs' a b a_val b_val,
  is_partially_sorted_seg xs a b a_val b_val ->
  Permutation xs xs' ->
  outside_same xs xs' a_val b_val ->
  (b_val <= length xs)%nat ∧ (a <= a_val)%nat ∧ (b >= b_val)%nat ->
  is_partially_sorted_seg xs' a b a_val b_val.
Proof.
  unfold is_partially_sorted_seg. unfold outside_same. 
  intros. assert(length xs = length xs'). { apply Permutation_length. auto. }
  destruct (decide (i < a_val)%nat); destruct (decide (j >= b_val)%nat).
  - rewrite <- H1 in H5; try lia. rewrite <- H1 in H6; try lia.
    eapply H; eauto.
  - rewrite <- H1 in H5; try lia. destruct H4; try lia.
    destruct (decide (j < a_val)%nat).
    + rewrite <- H1 in H6; try lia. eapply H; eauto. 
    + destruct (Permutation_existsIndex xs' xs j a_val b_val xj); eauto.
      { symmetry. auto. } { unfold outside_same in *. intros. rewrite H1; auto. } { lia. }
      destruct H8. eapply H; try eapply H8; eauto. lia. 
  - rewrite <- H1 in H6; try lia. destruct H3; try lia.
    destruct (decide (i >= b_val)%nat).
    + rewrite <- H1 in H5; try lia. eapply H; eauto.
    + destruct (Permutation_existsIndex xs' xs i a_val b_val xi); eauto.
      { symmetry. auto. } { unfold outside_same in *. intros. rewrite H1; auto. } { lia. }
      destruct H9. eapply H; try eapply H9; eauto. lia.
  - lia.
Qed.

Theorem restore_invariant1:
  forall xs2 xs3 (a_val b_val a b r0: nat),
    Permutation xs2 xs3 ->
    is_sorted_seg R xs3 a_val r0 ->
    outside_same xs2 xs3 a_val r0 ->
    is_partially_sorted_seg xs2 a b a_val b_val ->
    is_partitioned R xs2 a_val b_val r0 ->
    (a ≤ a_val ≤ r0)%nat ∧ (r0 < b_val ≤ b)%nat ∧ b <= length xs3 ->

    is_partially_sorted_seg xs3 a b (r0 + 1%nat)%nat b_val.
Proof using StrictWeakOrder0.
  intros. assert(length xs2 = length xs3). { apply Permutation_length. auto. }
  assert(is_partially_sorted_seg xs3 a b a_val b_val). 
  { eapply is_partially_sorted_seg__perserve; eauto; try lia.
    eapply outside_same_loosen; eauto; lia. }
  assert(is_partitioned R xs3 a_val b_val r0).
  { 
    unfold outside_same in H1. unfold is_partitioned in *. intros.
    rewrite <- H1 in H8; try lia. split; intros.
    - symmetry in H. edestruct (Permutation_existsIndex xs3 xs2 i a_val r0); eauto; try lia.
      { unfold outside_same. intros. rewrite H1; auto. }
      edestruct H3; try eapply H10; eauto. apply H11. lia.
    - rewrite <- H1 in H7; try lia. eapply H3; eauto.
  }
  clear dependent xs2. rename xs3 into xs.
  unfold is_partitioned, is_partially_sorted_seg, is_sorted_seg in *. intros.
  destruct (decide (i < a_val)%nat); first eapply H6; eauto.
  destruct (decide (j >= b_val)%nat); first eapply H6; eauto.
  destruct H1; try lia. destruct (Nat.eq_dec i r0).
  { subst r0. destruct (H7 j xi xj); eauto. apply H8. lia. }
  assert(∃ xp, xs !! r0 = Some xp). { apply list_lookup_lt. lia. } destruct H5 as [xp Hxp].
  assert(xp ≽ xi). { edestruct H7; try eapply H2; eauto. apply H5. lia. }
  destruct (decide (j >= r0)%nat).
  - eapply notR_trans; eauto. destruct (decide (j = r0)%nat).
    + subst r0. rewrite Hxp in H3. inv H3. apply notR_refl. auto.
    + edestruct H7; try apply H3; eauto. apply H9. lia.
  - eapply H0; eauto. lia.
Qed.

Theorem restore_invariant2:
  forall xs2 xs3 (a_val b_val a b r0: nat),
    Permutation xs2 xs3 ->
    is_sorted_seg R xs3 (r0 + 1)%nat b_val ->
    outside_same xs2 xs3 (r0 + 1)%nat b_val ->
    is_partially_sorted_seg xs2 a b a_val b_val ->
    is_partitioned R xs2 a_val b_val r0 ->
    (a ≤ a_val ≤ r0)%nat ∧ (r0 < b_val ≤ b)%nat ∧ b <= length xs3 ->

    is_partially_sorted_seg xs3 a b a_val r0.
Proof using StrictWeakOrder0.
  intros. assert(length xs2 = length xs3). { apply Permutation_length. auto. }
  assert(is_partially_sorted_seg xs3 a b a_val b_val). 
  { eapply is_partially_sorted_seg__perserve; eauto; try lia.
    eapply outside_same_loosen; eauto; lia. }
  assert(is_partitioned R xs3 a_val b_val r0).
  { 
    unfold outside_same in H1. unfold is_partitioned in *. intros.
    rewrite <- H1 in H8; try lia. split; intros.
    - rewrite <- H1 in H7; try lia. destruct (H3 i xr xi); auto. 
    - symmetry in H. edestruct (Permutation_existsIndex xs3 xs2 i (r0 + 1)%nat b_val); eauto; try lia.
      { unfold outside_same. intros. rewrite H1; auto. }
      edestruct H3; try eapply H10; eauto. apply H12. lia.
  }
  clear dependent xs2. rename xs3 into xs.
  unfold is_partitioned, is_partially_sorted_seg, is_sorted_seg in *. intros.
  destruct (decide (i < a_val)%nat); first eapply H6; eauto.
  destruct (decide (j >= b_val)%nat); first eapply H6; eauto.
  destruct H1; try lia. destruct (Nat.eq_dec j r0).
  { subst r0. destruct (H7 i xj xi); eauto. apply H5. lia. }
  assert(∃ xp, xs !! r0 = Some xp). { apply list_lookup_lt. lia. } destruct H5 as [xp Hxp].
  assert(xj ≽ xp). { edestruct H7; try eapply H3; eauto. apply H8. lia. }
  destruct (decide (i <= r0)%nat).
  - eapply notR_trans; eauto. destruct (decide (i = r0)%nat).
    + subst r0. rewrite Hxp in H2. inv H2. apply notR_refl. auto.
    + edestruct H7; try apply H2; eauto. apply H8. lia.
  - eapply H0; eauto. lia.
Qed.

Theorem partition__header:
  forall xs a b r, is_partitioned R xs a b r ->
    header R xs (r + 1)%nat b.
Proof.
  intros. unfold header. 
  destruct (decide ((r + 1)%nat = 0%nat)) as [Heq | Hneq]; auto.
  unfold one_le_seg. unfold is_partitioned in H.
  intros. eapply (H j xi); eauto.
  - replace (r + 1 - 1)%nat with r in H1; auto. lia.
  - lia.
Qed. 

Lemma wp_reverseRangeCmpFunc (data: slice.t) (a b: w64) (cmp_code: func.t)
                       (xs: list E):
  {{{ is_pkg_init slices ∗
      "Hxs" ∷ data ↦* xs ∗
      "%Hab_bound" ∷ ⌜ 0 ≤ sint.Z a < sint.Z b ∧ sint.Z b <= length xs <= 2 ^ 62⌝ ∗ 
      "#Hcmp" ∷ cmp_implements R cmp_code ∗ 
      "%pivot_range" ∷ ⌜ sint.Z a < sint.Z b ⌝ 
  }}}
    @! slices.reverseRangeCmpFunc #Et #data #a #b #cmp_code
  {{{ (xs': list E), RET #();
      data ↦* xs' ∗
      "%Hperm" ∷ ⌜ Permutation xs xs' ⌝ ∗
      "%Houtside" ∷ ⌜ outside_same xs xs' (sint.nat a) (sint.nat b) ⌝ 
  }}}.
Proof.
  wp_start as "H". iNamed "H". wp_auto.
  iAssert( ∃ xs1 (i_val j_val: w64),
    "Hxs" ∷ data ↦* xs1 ∗ 
    "i" ∷ i_ptr ↦ i_val ∗
    "j" ∷ j_ptr ↦ j_val ∗
    "%ij_bound" ∷ ⌜ sint.Z a <= sint.Z i_val ∧ 
                   sint.Z j_val < sint.Z b ⌝ ∗

    "%HPerm1" ∷ ⌜ Permutation xs xs1 ⌝ ∗ 
    "%Houtside1" ∷ ⌜ outside_same xs xs1 (sint.nat a) (sint.nat b) ⌝
  )%I with "[Hxs i j]" as "HI".
  { iFrame. iPureIntro. split; first word. split; auto.
    unfold outside_same. auto. }
  wp_for "HI". wp_if_destruct.
  - assert(length xs = length xs1). { apply Permutation_length. auto. }
    iAssert(⌜length xs1 = sint.nat data .(slice.len_f) ∧ 0 ≤ sint.Z data .(slice.len_f)⌝)%I
    with "[Hxs]" as "%Hlen". { iApply own_slice_len. iFrame. }

    wp_pure; try word. 
    assert(exists xj, xs1 !! (sint.nat j_val) = Some xj). { apply list_lookup_lt. lia. }
    destruct H0 as [xj Hxj].
    wp_apply (wp_load_slice_elem with "[$Hxs]") as "Hxs"; auto; first lia.

    wp_pure; try word. 
    assert(exists xi, xs1 !! (sint.nat i_val) = Some xi). { apply list_lookup_lt. lia. }
    destruct H0 as [xi Hxi].
    wp_apply (wp_load_slice_elem with "[$Hxs]") as "Hxs"; auto; first lia.

    wp_pure; try word.
    wp_apply (wp_store_slice_elem with "[$Hxs]") as "Hxs"; first (iPureIntro; lia).

    assert(length (<[sint.nat i_val:=xj]> xs1) = length xs1) by apply length_insert.

    wp_pure; try word.
    wp_apply (wp_store_slice_elem with "[$Hxs]") as "Hxs"; first (iPureIntro; lia).

    wp_for_post. iFrame. iPureIntro.
    split; first word.
    split. { eapply perm_trans; try eapply HPerm1. apply swap_perm; auto. }
    eapply outside_same_trans; try apply Houtside1. apply outside_same_swap; lia.
  - iApply "HΦ". iFrame. auto.
Qed.

Lemma wp_pdqsortCmpFunc (data: slice.t) (a b limit: w64) (cmp_code: func.t)
                       (xs: list E):
  {{{ is_pkg_init slices ∗
      "Hxs" ∷ data ↦* xs ∗
      "%Hab_bound" ∷ ⌜ 0 ≤ sint.Z a ≤  sint.Z b ∧ sint.Z b <= length xs <= 2 ^ 62⌝ ∗ 
      "%Header" ∷ ⌜ header R xs (sint.nat a) (sint.nat b) ⌝ ∗
      "#Hcmp" ∷ cmp_implements R cmp_code
  }}}
    @! slices.pdqsortCmpFunc #Et #data #a #b #limit #cmp_code
  {{{ (xs': list E), RET #();
      "Hxs" ∷ data ↦* xs' ∗
      "%Hperm" ∷ ⌜ Permutation xs xs' ⌝ ∗
      "%Hsorted" ∷ ⌜ is_sorted_seg R xs' (sint.nat a) (sint.nat b) ⌝ ∗
      "%Houtside" ∷ ⌜ outside_same xs xs' (sint.nat a) (sint.nat b) ⌝ 
  }}}.
Proof using RelDecision0 StrictWeakOrder0 globalsGS0 BoundedTypeSize0.
  iLöb as "IH" forall (data a b limit xs).
  wp_start as "H". iNamed "H". wp_auto.  
  (* Loop Invariant for the outer loop *)
  iAssert( ∃ (a_val b_val limit: w64) (bl1 bl2: bool) xs', 
    "a" ∷ a_ptr ↦ a_val ∗ 
    "b" ∷ b_ptr ↦ b_val ∗ 
    "limit" ∷ limit_ptr ↦ limit ∗ 
    "wasPartitioned" ∷ wasPartitioned_ptr ↦ bl1 ∗ 
    "wasBalanced" ∷ wasBalanced_ptr ↦ bl2 ∗ 
    (* "alreadyPartitioned" ∷ wasBalanced_ptr ↦ bl3 ∗  *)
 
    "Hxs" ∷ data ↦* xs' ∗ 
    "%ab_range" ∷ ⌜ sint.Z a <= sint.Z a_val ∧ sint.Z a_val ≤ sint.Z b_val ∧ sint.Z b_val <= sint.Z b ⌝ ∗ 
    "%HPerm1" ∷ ⌜ Permutation xs xs' ⌝ ∗ 
    "%Header" ∷ ⌜ header R xs' (sint.nat a_val) (sint.nat b_val) ⌝ ∗
    "%HPartialsorted" ∷ ⌜ is_partially_sorted_seg xs' (sint.nat a) (sint.nat b) (sint.nat a_val) (sint.nat b_val) ⌝ ∗
    "%Houtside1" ∷ ⌜ outside_same xs xs' (sint.nat a) (sint.nat b) ⌝
  )%I with "[a b limit Hxs wasPartitioned wasBalanced]" as "HI".
  { iFrame. iPureIntro. split; first lia.
    split; auto. split;  auto; try split; try apply outside_same_refl.
    unfold is_partially_sorted_seg. intros. lia. }
  wp_for "HI". 
  assert(Hlen_x': length xs = length xs'). { apply Permutation_length. auto. }
  wp_if_destruct. { (* Falls to insertionSort *)
    wp_apply (wp_insertionSortCmpFunc with "[$Hxs]").
    { iSplit; auto. iPureIntro; lia. }
    iIntros (xs'') "Hpost". 
    iDestruct "Hpost" as "(Hxs & %Hperm1 & %Hsorted & %Houtside)".
    wp_auto. wp_for_post. iApply "HΦ".
    iFrame. iPureIntro. split; try split.
    - eapply perm_trans; eauto.
    - eapply close_segment; eauto. lia.
    - eapply outside_same_trans; try eapply Houtside1.
      eapply outside_same_loosen; eauto; lia.
  }
  wp_if_destruct. { (* Falls to heapSort *)
    wp_apply (wp_heapSortCmpFunc with "[$Hxs]").
    { iSplit; auto. iPureIntro. word. }
    iIntros (xs'') "Hpost". 
    iDestruct "Hpost" as "(Hxs & %Hperm1 & %Hsorted & %Houtside)".
    wp_auto. wp_for_post. iApply "HΦ".
    iFrame. iPureIntro. split; try split.
    - eapply perm_trans; eauto.
    - eapply close_segment; eauto. lia.
    - eapply outside_same_trans; try eapply Houtside1.
      eapply outside_same_loosen; eauto; lia.
  }
  wp_bind. iApply ((wp_wand _ _ _ (fun v => ⌜ v = execute_val ⌝ ∗ ∃ (limit: w64) xs', 
    "a" ∷ a_ptr ↦ a_val ∗ 
    "b" ∷ b_ptr ↦ b_val ∗ 
    "limit" ∷ limit_ptr ↦ limit ∗ 
    "wasPartitioned" ∷ wasPartitioned_ptr ↦ bl1 ∗ 
    "wasBalanced" ∷ wasBalanced_ptr ↦ bl2 ∗ 
    "cmp" ∷ cmp_ptr ↦ cmp_code ∗ 
    (* "alreadyPartitioned" ∷ wasBalanced_ptr ↦ bl3 ∗  *)
 
    "Hxs" ∷ data ↦* xs' ∗ 
    "data" ∷ data_ptr ↦ data ∗
    "%ab_range" ∷ ⌜ sint.Z a <= sint.Z a_val ∧ sint.Z a_val ≤ sint.Z b_val ∧ sint.Z b_val <= sint.Z b ⌝ ∗ 
    "%HPerm1" ∷ ⌜ Permutation xs xs' ⌝ ∗ 
    "%HPartialsorted" ∷ ⌜ is_partially_sorted_seg xs' (sint.nat a) (sint.nat b) (sint.nat a_val) (sint.nat b_val) ⌝ ∗
    "%Header" ∷ ⌜ header R xs' (sint.nat a_val) (sint.nat b_val) ⌝ ∗
    "%Houtside1" ∷ ⌜ outside_same xs xs' (sint.nat a) (sint.nat b) ⌝)%I) with "[a b Hxs limit wasPartitioned wasBalanced data cmp]"). 
  1: { (* Pattern-Break  *)
    wp_if_destruct. {
      iSplit; first auto. iFrame. iPureIntro.
      split; first lia. split;  auto.
    }
    wp_apply (wp_breakPatternsCmpFunc with "[$Hxs]").
    { iSplit; first word. iSplit; auto. word. }
    iIntros (xs2) "Hpost". iDestruct "Hpost" as "(Hxs & %Hperm2 & %Houtside2)".
    wp_auto. iSplit; first auto.
    iFrame. iPureIntro. split; first lia. split; try split; try split.
    - eapply perm_trans; eauto.
    - eapply is_partially_sorted_seg__perserve; eauto. lia.
    - eapply header__preserve; try eapply Header0; eauto. lia.
    - eapply outside_same_trans; try eapply Houtside1.
      eapply outside_same_loosen; eauto; lia.
  }
  iIntros (v) "[%Hv Hpost]". subst v. iNamed "Hpost".
  clear dependent xs'. rename xs'0 into xs'.
  
  wp_auto. assert(length xs = length xs'). { apply Permutation_length. auto. }
  wp_apply (wp_choosePivotCmpFunc with "[$Hxs]"). { iSplit; auto. word. }
  iIntros (r hint) "(Hxs & %Hrbound)". wp_auto. 

  wp_bind. iApply ((wp_wand _ _ _ (fun v => ⌜ v = execute_val ⌝ ∗ ∃ xs' (hint: slices.sortedHint.t) (r: w64), 
    "a" ∷ a_ptr ↦ a_val ∗ 
    "b" ∷ b_ptr ↦ b_val ∗ 
    "limit" ∷ limit_ptr ↦ limit1 ∗ 
    "wasPartitioned" ∷ wasPartitioned_ptr ↦ bl1 ∗ 
    "wasBalanced" ∷ wasBalanced_ptr ↦ bl2 ∗ 
    "cmp" ∷ cmp_ptr ↦ cmp_code ∗ 
    (* "alreadyPartitioned" ∷ wasBalanced_ptr ↦ bl3 ∗  *)
 
    "hint" ∷ hint_ptr ↦ hint ∗ 
    "pivot" ∷ pivot_ptr ↦ r ∗ 
    "Hxs" ∷ data ↦* xs' ∗ 
    "data" ∷ data_ptr ↦ data ∗
    "%ab_range" ∷ ⌜ sint.Z a <= sint.Z a_val ∧ sint.Z a_val ≤ sint.Z b_val ∧ sint.Z b_val <= sint.Z b ⌝ ∗ 
    "%HPerm1" ∷ ⌜ Permutation xs xs' ⌝ ∗ 
    "%HPartialsorted" ∷ ⌜ is_partially_sorted_seg xs' (sint.nat a) (sint.nat b) (sint.nat a_val) (sint.nat b_val) ⌝ ∗
    "%Houtside1" ∷ ⌜ outside_same xs xs' (sint.nat a) (sint.nat b) ⌝ ∗
    "%Header" ∷ ⌜ header R xs' (sint.nat a_val) (sint.nat b_val) ⌝ ∗
    "%rrange" ∷ ⌜ sint.Z a_val ≤ sint.Z r < sint.Z b_val ⌝
    )%I) with "[a b Hxs limit wasPartitioned wasBalanced data cmp hint pivot]").
  {
    wp_if_destruct.
    - wp_apply (wp_reverseRangeCmpFunc with "[$Hxs]").
      { iSplit; first word. iSplit; first eauto. iPureIntro. lia. }
      iIntros (xs'0) "Hpost". iDestruct "Hpost" as "(Hxs & %Hperm & %Houtside)".
      wp_auto. iSplit; first auto.
      iFrame. iPureIntro. split; first lia. 
      split. { eapply perm_trans; try eapply HPerm0; auto. }
      split. { eapply is_partially_sorted_seg__perserve; eauto. lia. }
      split. { eapply outside_same_trans; eauto. eapply outside_same_loosen; eauto; lia. }
      split. { eapply header__preserve; try eapply Header1; eauto. lia. }
      word.
    - iSplit; first auto. iFrame. iPureIntro. split; auto.
  }
  
  iIntros (v) "[%Hv Hpost]". subst v. iNamed "Hpost".
  clear dependent xs' hint. rename xs'0 into xs'. rename hint0 into hint. wp_auto.
  wp_bind ((if: if: if: # bl2 then ![# boolT] (# wasPartitioned_ptr) else # false
then ![# slices.sortedHint] (# hint_ptr) = slices.increasingHint else # false
then if: let: "$a0" := ![# sliceT] (# data_ptr) in
let: "$a1" := ![# intT] (# a_ptr) in
let: "$a2" := ![# intT] (# b_ptr) in
let: "$a3" := ![# funcT] (# cmp_ptr) in
func_call (# slices.partialInsertionSortCmpFunc) (# Et) "$a0" "$a1" "$a2" "$a3"
then return: # () else do: # () else do: # ()))%E.
iApply ((wp_wand _ _ _ (fun v => ∃ xs'', 
    "a" ∷ a_ptr ↦ a_val ∗ 
    "b" ∷ b_ptr ↦ b_val ∗ 
    "limit" ∷ limit_ptr ↦ limit1 ∗ 
    "wasPartitioned" ∷ wasPartitioned_ptr ↦ bl1 ∗ 
    "wasBalanced" ∷ wasBalanced_ptr ↦ bl2 ∗ 
    "cmp" ∷ cmp_ptr ↦ cmp_code ∗ 
 
    "hint" ∷ hint_ptr ↦ hint ∗ 
    "pivot" ∷ pivot_ptr ↦ r0 ∗ 
    "Hxs" ∷ data ↦* xs'' ∗ 
    "data" ∷ data_ptr ↦ data ∗
    "%ab_range" ∷ ⌜ sint.Z a <= sint.Z a_val ∧ sint.Z a_val ≤ sint.Z b_val ∧ sint.Z b_val <= sint.Z b ⌝ ∗ 
    "%HPerm1" ∷ ⌜ Permutation xs' xs'' ⌝ ∗ 
    "%Houtside1" ∷ ⌜ outside_same xs' xs'' (sint.nat a_val) (sint.nat b_val) ⌝ ∗
    "%Header" ∷ ⌜ header R xs'' (sint.nat a_val) (sint.nat b_val) ⌝ ∗
    "%Hpost" ∷ ⌜ v = return_val #()%V /\ is_sorted_seg R xs'' (sint.nat a) (sint.nat b)  \/
      v = execute_val ⌝ 
    )%I) with "[a b Hxs limit wasPartitioned wasBalanced data cmp hint pivot]"). {
      wp_if_destruct. 2: {
        iFrame. iPureIntro. split_and!; auto; try lia.
        apply outside_same_refl.
      }
      wp_if_destruct. 2: {
        iFrame. iPureIntro. split_and!; auto; try lia.
        apply outside_same_refl.
      }
      wp_if_destruct. 2: {
        iFrame. iPureIntro. split_and!; auto; try lia.
        apply outside_same_refl.
      }
      assert(length xs = length xs') by (apply Permutation_length; auto).
      wp_apply (wp_partialInsertionSortCmpFunc with "[Hxs]").
      { iFrame. iSplit; first auto. 
        iPureIntro; split_and!; auto; try lia. }
      iIntros (xs'0 bl) "Hpost". iDestruct "Hpost" as "(Hxs & Hpost)". 
      iNamed "Hpost". wp_if_destruct. {
        iFrame. iPureIntro. split; first lia. split_and!; auto.
        - eapply header__preserve; eauto; lia. 
        - left. split; auto. eapply close_segment; eauto; lia.
      } {
        iFrame. iPureIntro. split; first lia. split_and!; auto.
        eapply header__preserve; eauto; lia.
      }
    }
  iIntros (v) "Hpost". iNamed "Hpost". wp_auto. destruct Hpost. { 
    destruct H. subst v. wp_auto. wp_for_post.
    iApply "HΦ". iFrame. iPureIntro; split_and!; eauto.
    - eapply perm_trans; eauto.
    - eapply outside_same_trans; eauto. 
      eapply outside_same_loosen; eauto; lia.
  }
  assert(length xs = length xs') by (apply Permutation_length; auto).
  assert(is_partially_sorted_seg xs'' (sint.nat a) (sint.nat b) (sint.nat a_val) (sint.nat b_val)).
  { eapply is_partially_sorted_seg__perserve; eauto. lia. }
  assert(Permutation xs xs''). { eapply perm_trans; eauto. }
  assert(length xs = length xs''). { apply Permutation_length. eauto. }
  assert(Houtside4: outside_same xs xs'' (sint.nat a)  (sint.nat b) ). {
    eapply outside_same_trans; eauto. eapply outside_same_loosen; eauto; lia. 
  }
  clear dependent xs'. rename xs'' into xs'.
  subst v. rename Header1 into Header0. wp_auto.

  wp_bind (if: if: # (bool_decide (sint.Z a_val > sint.Z (W64 0))%Z)
then ~
int_lt
(let: "$a0" := ![# Et] (slice.elem_ref (# Et) ![# sliceT] (# data_ptr)
(_)) in
let: "$a1" := ![# Et] (slice.elem_ref (# Et) ![# sliceT] (# data_ptr) ![# intT] (# pivot_ptr)) in
![# funcT] (# cmp_ptr) "$a0" "$a1") (# (W64 0)) else # false
then let: "mid" := alloc (type.zero_val (# intT)) in
let: "$r0" := let: "$a0" := ![# sliceT] (# data_ptr) in
let: "$a1" := ![# intT] (# a_ptr) in
let: "$a2" := ![# intT] (# b_ptr) in
let: "$a3" := ![# intT] (# pivot_ptr) in
let: "$a4" := ![# funcT] (# cmp_ptr) in
func_call (# slices.partitionEqualCmpFunc) (# Et) "$a0" "$a1" "$a2" "$a3" "$a4" in
(do: "mid" <-[# intT] "$r0") ;;;
let: "$r0" := ![# intT] "mid" in (do: # a_ptr <-[# intT] "$r0") ;;;
continue: # () else do: # ())%E. 
rename xs' into xs3.
assert(length xs = length xs3). { apply Permutation_length; auto. }
clear dependent r.
iApply ((wp_wand _ _ _ (fun v => ∃ xs' (new_a: w64), 
    "a" ∷ a_ptr ↦ new_a ∗ 
    "b" ∷ b_ptr ↦ b_val ∗ 
    "limit" ∷ limit_ptr ↦ limit1 ∗ 
    "wasPartitioned" ∷ wasPartitioned_ptr ↦ bl1 ∗ 
    "wasBalanced" ∷ wasBalanced_ptr ↦ bl2 ∗ 
    "cmp" ∷ cmp_ptr ↦ cmp_code ∗ 
 
    "pivot" ∷ pivot_ptr ↦ r0 ∗ 
    "Hxs" ∷ data ↦* xs' ∗ 
    "data" ∷ data_ptr ↦ data ∗
    "%ab_range" ∷ ⌜ sint.Z a <= sint.Z new_a ∧ sint.Z new_a ≤ sint.Z b_val ∧ sint.Z b_val <= sint.Z b ⌝ ∗ 
    "%HPerm1" ∷ ⌜ Permutation xs xs' ⌝ ∗ 
    "%Houtside1" ∷ ⌜ outside_same xs3 xs' (sint.nat a_val) (sint.nat b_val) ⌝ ∗
    "%Header" ∷ ⌜ header R xs' (sint.nat a_val) (sint.nat b_val) ⌝ ∗
    "%Hpost" ∷ ⌜ v = continue_val /\ sint.Z new_a > sint.Z a_val /\ is_eq_partitioned R xs' (sint.nat a_val) (sint.nat b_val) (sint.nat new_a)  \/
      v = execute_val /\ xs' = xs3 /\  new_a = a_val ⌝ 
    )%I) with "[a b Hxs limit wasPartitioned wasBalanced data cmp pivot]").
  {
    wp_if_destruct. 2: (iFrame; iPureIntro; repeat (split; auto)).

    iAssert(⌜length xs3 = sint.nat data .(slice.len_f) ∧ 0 ≤ sint.Z data .(slice.len_f)⌝)%I
    with "[Hxs]" as "%Hlen". { iApply own_slice_len. iFrame. }
    
    
    assert(exists xa, xs3 !! sint.nat (w64_word_instance .(word.sub) a_val (W64 1)) = Some xa).
    { apply list_lookup_lt. word. } destruct H0 as [xa Hxa].
    wp_pure; try word.
    wp_apply (wp_load_slice_elem with "[$Hxs]") as "Hxs"; eauto; first word.

    assert(exists xr, xs3 !! sint.nat r0 = Some xr).
    { apply list_lookup_lt. lia. } destruct H0 as [xr Hxr].
    wp_pure; try lia.
    wp_apply (wp_load_slice_elem with "[$Hxs]") as "Hxs"; eauto; first word.

    wp_apply "Hcmp". iIntros (cmp0) "%Hcmp_r". wp_auto.
    wp_if_destruct. {
      iFrame. iPureIntro. repeat(split; auto).
    }
    wp_apply (wp_partitionEqualCmpFunc with "[$Hxs]"). 
    { iSplit; first word. iSplit; first auto. iPureIntro.
      split; first lia. 
      apply comparison_negate in Hcmp_r.
      apply Hcmp_r in n1. unfold one_le_seg.
      intros. rewrite H4 in Hxr. inv Hxr.
      eapply notR_trans; eauto. 
      unfold header in Header0. 
      destruct (decide (sint.nat a_val = 0%nat)) as [Heq1|Hneq1].
      - word.
      - eapply Header0; eauto. 
        replace (sint.nat (word.sub a_val (W64 1))) with (sint.nat a_val - 1)%nat in Hxa by word.
        auto.
    }
    iIntros (xs4 new_a) "Hpost". iDestruct "Hpost" as "(Hxs & Hpost)".
    iNamed "Hpost". wp_auto. iFrame. iPureIntro.
    split; first lia.
    split. { eapply perm_trans; eauto. }
    split. { eapply outside_same_trans; eauto. apply outside_same_refl. }
    split. { eapply header__preserve; eauto. lia. }
    left. split; auto. split; auto. lia.
  }
  iIntros (v) "Hpost". iNamed "Hpost". destruct Hpost. {
    assert(length xs = length xs'). { apply Permutation_length. auto. }
    destruct H0. subst v. wp_auto. wp_for_post. iFrame. iPureIntro.
    split; first lia. split; auto.
    assert(is_partially_sorted_seg xs' (sint.nat a) (sint.nat b) (sint.nat a_val) (sint.nat b_val)).
    { eapply is_partially_sorted_seg__perserve; try eapply H1; eauto.
      - eapply perm_trans; try eapply HPerm1. symmetry. auto.
      - lia. } 
    destruct H5.  
    split. {
      unfold header. destruct (decide (sint.nat new_a = 0%nat)); auto.
      unfold one_le_seg. intros.
      eapply H6; eauto. lia.
    }
    split. {
      unfold is_partially_sorted_seg. intros. destruct H8.
      - destruct (decide (i < sint.nat a_val)%nat).
        + eapply H0; eauto.
        + destruct (decide (j < sint.nat b_val)%nat).
          * eapply H6; eauto. lia.
          * eapply H0; eauto. lia.
      - eapply H0; eauto. 
    } 
    eapply outside_same_trans; eauto. 
    eapply outside_same_loosen; eauto; lia.
  }
  destruct H0 as (H41 & H42 & H43). subst v. subst xs'. subst new_a.
  
  rename xs3 into xs'. 
  assert(Hlen: length xs = length xs'). { apply Permutation_length. auto. }
  wp_auto. wp_apply (wp_partitionCmpFunc with "[$Hxs]"). { iSplit; iSplit; auto; iPureIntro; lia. }
  iIntros (xs2 bl r1) "[Hxs %irange]". destruct irange as (rrange1 & Hperm2 & Hpart & Houtside2).
  
  assert(Permutation xs xs2). { eapply perm_trans; eauto. }
  assert(outside_same xs xs2 (sint.nat a) (sint.nat b)). { eapply outside_same_trans; eauto. eapply outside_same_loosen; eauto; lia. }
  assert(is_partially_sorted_seg xs2 (sint.nat a) (sint.nat b) (sint.nat a_val) (sint.nat b_val)).
  { eapply is_partially_sorted_seg__perserve; eauto. lia. }
  assert(header R xs2 (sint.nat a_val) (sint.nat b_val)). 
  { eapply header__preserve; try eapply Hperm2; eauto. lia. }
  assert(length xs = length xs2). { apply Permutation_length. eauto. }
  
  clear dependent xs'. wp_auto. wp_if_destruct.
  - wp_apply ("IH" with "[$Hxs]"). { 
      iSplit; auto; first word. iSplit; auto. 
      iPureIntro. unfold header. unfold header in H6. 
      destruct (decide (sint.nat a_val = 0%nat)); auto. unfold one_le_seg in *.
      intros. eapply H6; eauto. lia. }
    iIntros (xs3) "(Hxs & %Hperm3 & %Hsorted3 & %Houtside3)". wp_auto. 
    wp_for_post. iFrame. iSplit; first word. iPureIntro. 
    split. { eapply perm_trans; eauto. }
    replace (sint.nat (word.add r1 (W64 1))) with (sint.nat r1 + 1%nat)%nat by word.
    split. { unfold header. destruct (decide ((sint.nat r1 + 1)%nat = 0%nat)); try auto. 
    replace (sint.nat r1 + 1 - 1)%nat with (sint.nat r1) by lia. unfold one_le_seg.
    unfold outside_same in Houtside3. intros. rewrite <- Houtside3 in H2; try lia.
    rewrite <- Houtside3 in H1; try lia. unfold is_partitioned in Hpart. 
    edestruct Hpart; eauto. apply H8. lia.
     }
    split. 2: { eapply outside_same_trans; eauto. eapply outside_same_loosen; eauto; lia. }
    
    eapply restore_invariant1; eauto. 
    assert(length xs2 = length xs3). { apply Permutation_length. eauto. } lia.

  - wp_apply ("IH" with "[$Hxs]"). { iSplit; first word. iSplit; auto.
    iPureIntro.
    replace (sint.nat (word.add r1 (W64 1))) with (sint.nat r1 + 1%nat)%nat by word. 
    eapply partition__header; eauto. }

    iIntros (xs3) "(Hxs & %Hperm3 & %Hsorted3 & %Houtside3)". 
    replace (sint.nat (word.add r1 (W64 1))) with (sint.nat r1 + 1%nat)%nat in * by word. 
    wp_auto. wp_for_post. iFrame. iSplit; first word. iPureIntro. 
    split. { eapply perm_trans; eauto. }
    split. { unfold header.  unfold header in H6. unfold one_le_seg in *. intros.
    destruct (decide ((sint.nat a_val)%nat = 0%nat)); try auto.
    unfold outside_same in Houtside3. intros. 
    rewrite <- Houtside3 in H2; try lia.
    eapply H6; eauto; first lia.
    rewrite Houtside3; eauto. lia. }
    split. 2: { eapply outside_same_trans; try eapply H0; eauto. eapply outside_same_loosen; eauto; try lia. }
    eapply restore_invariant2; eauto.
    assert(length xs2 = length xs3). { apply Permutation_length. eauto. } lia.
Qed.

End proof.
