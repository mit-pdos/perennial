From New.generatedproof Require Import slices.
From New.proof Require Import proof_prelude.
From New.proof.slices_proof Require Import slices_init.

Goal True.
  idtac " > NOTE: The `pdqSort` proof (./new/proof/slices_proof/pdqSort/*.v) may take minutes to compile.".
  exact I.
Qed.

Class WeakOrder {A} (R: A → A → Prop) :=
  { weak_order_irrefl :> Irreflexive R;
    weak_order_anti_symm : ∀ x y, R x y ↔ ¬R y x;
    weak_order_trans :> Transitive R;
  }.

Lemma WeakOrder_Improper: forall (R: Z -> Z -> Prop),
  WeakOrder R -> False.
Proof.
  intros. destruct H.
  assert(¬(R 0 0)) by apply weak_order_irrefl0.
  apply H. apply weak_order_anti_symm0 in H. apply H.
Qed.

Class StrictWeakOrder {A} (R: A -> A -> Prop) := {
  strict_weak_order_irrefl :> Irreflexive R;
  strict_weak_order_trans :> Transitive R;
  strict_weak_order_equiv :> Equivalence (fun x y => ¬ R x y ∧ ¬ R y x )
}.

Lemma StrictWeakOrder_unsigned_lt:  StrictWeakOrder
  (fun (a b: w64) =>  word.unsigned a < word.unsigned b).
Proof.
  split.
  - unfold Irreflexive. unfold Reflexive. unfold complement. intros. word.
  - unfold Transitive. intros. word.
  - split.
    + unfold Reflexive. intros. word.
    + unfold Symmetric. intros. word.
    + unfold Transitive. intros. word.
Qed.

Lemma StrictWeakOrder_signed_lt:  StrictWeakOrder
  (fun (a b: w64) =>  word.signed a < word.signed b).
Proof.
  split.
  - unfold Irreflexive. unfold Reflexive. unfold complement. intros. word.
  - unfold Transitive. intros. word.
  - split.
    + unfold Reflexive. intros. word.
    + unfold Symmetric. intros. word.
    + unfold Transitive. intros. word.
Qed.

Lemma swap_perm:
  forall T, forall (xs: list T) i j xi xj,
  xs !! i = Some xi ->
  xs !! j = Some xj ->
  Permutation xs (<[i:=xj]> (<[j:=xi]> xs)).
Proof.
  intros. symmetry.
  apply Permutation_insert_swap; eauto.
Qed.

Definition outside_same {T} (xs xs': list T) a b :=
  forall i, (i < a)%nat ∨ (i >= b)%nat -> xs !! i = xs' !! i.

Lemma outside_same_refl:
  ∀ T (xs: list T) a b,
  outside_same xs xs a b.
Proof.
  unfold outside_same. intros. auto.
Qed.

Lemma outside_same_trans:
  forall T a b (xs0 xs1 xs2: list T),
  outside_same xs0 xs1 a b -> outside_same xs1 xs2 a b ->
  outside_same xs0 xs2 a b.
Proof.
  unfold outside_same. intros.
  rewrite H; auto.
Qed.

Lemma outside_same_swap:
  ∀ T (xs: list T) i j xi xj a b,
  (a <= i < b)%nat -> (a <= j < b)%nat ->
  outside_same xs (<[i:=xj]> (<[j:=xi]> xs)) a b.
Proof.
  unfold outside_same. intros.
  rewrite list_lookup_insert_ne; try lia.
  rewrite list_lookup_insert_ne; try lia.
  auto.
Qed.

Theorem outside_same_loosen:
  forall T (xs xs': list T) a b a1 b1,
  outside_same xs xs' a b ->
  (a1 <= a)%nat ->
  (b1 >= b)%nat ->
  outside_same xs xs' a1 b1.
Proof.
  unfold outside_same. intros.
  apply H. lia.
Qed.

Theorem outside_same__decompose:
  forall {T} (xsa xsb: list T) a b, outside_same xsa xsb a b -> a <= b ->
  xsa = (take a xsa) ++ (take (b - a) (drop a xsa)) ++ (drop b xsa) ∧
  xsb = (take a xsa) ++ (take (b - a) (drop a xsb)) ++ (drop b xsa).
Proof.
  intros. split.
  - replace (take a xsa ++ take (b - a) (drop a xsa) ++ drop b xsa)
    with (take a xsa ++ drop a xsa).
    + symmetry. apply take_drop.
    + assert(drop a xsa = take (b - a) (drop a xsa) ++ drop b xsa).
      { pose proof (drop_drop xsa (b - a) a).
        replace (a + (b - a))%nat with b in H1 by lia.
        rewrite <- H1. symmetry. apply take_drop.  }
      rewrite <- H1. auto.
  - assert(drop b xsa = drop b xsb).
    {
      apply list_eq. intros.
      unfold outside_same in H.
      rewrite lookup_drop. rewrite lookup_drop.
      apply H. lia.
    }
    assert(take a xsa = take a xsb).
    {
      apply list_eq. intros.
      rewrite lookup_take. rewrite lookup_take.
      destruct (decide (i < a)%nat); auto.
    }
    rewrite H1. rewrite H2.
    replace (take (b - a) (drop a xsb) ++ drop b xsb) with (drop a xsb).
    + symmetry. apply take_drop.
    + replace (drop b xsb) with (drop (b - a) (drop a xsb)).
      * symmetry. apply take_drop.
      * pose proof drop_drop xsb (b - a) a.
        replace (a + (b - a))%nat with b in H3 by lia.
        auto.
Qed.

Theorem Permutation_existsIndex:
  forall {T} (xs xs': list T) (i a b: nat) x,
  Permutation xs xs' ->
  outside_same xs xs' a b ->
  (a <= i < b)%nat ∧ (b <= length xs)%nat ->
  xs !! i = Some x ->
  exists i0, xs' !! i0 = Some x  ∧  (a <= i0 < b)%nat.
Proof.
  intros. pose proof (outside_same__decompose xs xs' a b H0).
  destruct H3 as (Hxs & Hxs'); first lia.
  set xs0 := take (b - a) (drop a xs).
  set xs'0 := take (b - a) (drop a xs').
  assert(xs0 ≡ₚ xs'0).
  { rewrite Hxs in H. rewrite Hxs' in H.
    apply Permutation_app_inv_l in H.
    apply Permutation_app_inv_r in H. auto. }
  assert(forall j xj, xs0 !! j = Some xj -> exists j0, xs'0 !! j0 = Some xj).
  { intros. pose proof (Permutation_inj xs0 xs'0). apply H5 in H3.
    destruct H3. destruct H6 as [f [_ H6]]. exists (f j). rewrite <- H6. auto. }
  rewrite Hxs in H2.
  assert(length(take a xs) = a). { apply length_take_le. lia. }
  rewrite lookup_app_r in H2; try lia. rewrite H5 in H2.
  assert(length (take (b - a) (drop a xs)) = (b - a)%nat). { apply length_take_le. rewrite length_drop. lia. }
  rewrite lookup_app_l in H2; try lia.
  edestruct H4 as [j0 H7]; try eapply H2.
  exists (a + j0)%nat. rewrite Hxs'.
  pose proof (Permutation_length H3).
  pose proof (lookup_lt_Some xs'0 j0 x).
  assert(j0 < b - a). {
    apply lookup_lt_Some in H7.
    unfold xs0, xs'0 in *. lia. }
  split; try lia.
  rewrite lookup_app_r; try lia.
  rewrite lookup_app_l.
  - replace (length (take a xs)) with a.
    replace (a + j0 - a)%nat with j0 by lia.
    apply H7.
  - rewrite H5. apply lookup_lt_Some in H7.
    unfold xs0, xs'0 in *. lia.
Qed.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : slices.Assumptions}.

Context `[!ZeroVal E] `[!TypedPointsto E] `[!IntoValTyped E Et].
Context (R: E → E → Prop) `{!StrictWeakOrder R} `{!RelDecision R}.
Collection W := sem + package_sem + IntoValTyped0.

#[local] Infix "≺" := R (at level 70).
#[local] Notation "x ≽ y" := (¬ R x y) (at level 70, only parsing).

Theorem R_antisym:
  ∀ x y, x ≺ y -> ¬ y ≺ x.
Proof using StrictWeakOrder0.
  unfold not. intros. destruct StrictWeakOrder0.
  assert(x ≺ x). { eapply strict_weak_order_trans0; eauto. }
  unfold Irreflexive in *. unfold Reflexive in *. unfold complement in *.
  eapply strict_weak_order_irrefl0. eauto.
Qed.

Theorem notR_refl:
  ∀ x, x ≽ x.
Proof using StrictWeakOrder0.
  intros. destruct StrictWeakOrder0. unfold Irreflexive in *. unfold Reflexive in *.
  unfold complement in *. unfold not. apply strict_weak_order_irrefl0.
Qed.

Theorem notR_trans:
  ∀ x y z, z ≽ y -> y ≽ x -> z ≽ x.
Proof using StrictWeakOrder0.
  intros x y z Hxy Hyz Hzx.
  destruct StrictWeakOrder0 as [irrefl trans1 equiv].
  destruct equiv as [refl symm trans2].
  assert(x ≺ y ∨ ¬ x ≺ y) by apply Classical_Prop.classic.
  assert(y ≺ z ∨ ¬ y ≺ z) by apply Classical_Prop.classic.
  destruct H; destruct H0.
  - apply (R_antisym x z); auto. eapply trans1; eauto.
  - assert(z ≺ y) by (eapply trans1; eauto). auto.
  - assert(y ≺ x) by (eapply trans1; eauto). auto.
  - unfold Transitive in *. assert(¬ z ≺ x ∧ ¬ x ≺ z) by (eapply trans2; split; eauto).
    destruct H1. auto.
Qed.

Theorem notR_comparable:
  ∀ x y, x ≽ y ∨ y ≽ x.
Proof using StrictWeakOrder0.
  intros. apply Classical_Prop.not_and_or. intros [H1 H2].
  destruct (R_antisym x y); auto.
Qed.

Definition cmp_implements (cmp_code: func.t) : iProp Σ :=
  ∀ (x y: E),
  {{{ True }}}
    #cmp_code #x #y
  {{{ (r: w64), RET #r;
      (* the sort implementation only ever checks cmp x y < 0; it does not
      distinguish between 0 and positive comparisons *)
      ⌜sint.Z r < 0 ↔ x ≺ y⌝
      }}}.

#[export] Instance cmp_implements_persistent cmp_code :
  Persistent (cmp_implements cmp_code).
Proof. apply _. Qed.

Lemma comparison_negate (r: w64) (x y: E) :
  (sint.Z r < 0 ↔ x ≺ y) →
  ¬(sint.Z r < 0) ↔ x ≽ y.
Proof.
  intros H. tauto.
Qed.

Definition is_sorted (l: list E) := forall i j xi xj, (i < j)%nat ->
  l !! i = Some xi -> l !! j = Some xj -> xj ≽ xi.

Definition is_sorted_seg (l: list E) (st ed: nat) :=
  forall i j xi xj, (st <= i < j)%nat ∧ (j < ed)%nat ->
  l !! i = Some xi -> l !! j = Some xj -> xj ≽ xi.

Lemma is_sorted_seg__is_sorted:
  forall l, is_sorted_seg l 0 (length l) -> is_sorted l.
Proof.
  intros l. unfold is_sorted. unfold is_sorted_seg.
  intros. apply (H i j); auto.
  split.
  - lia.
  - eapply lookup_lt_Some. eauto.
Qed.

Definition one_le_seg (xs: list E) i l r :=
  forall xi j xj, (l <= j < r)%nat ->
    xs !! i = Some xi -> xs !! j = Some xj ->
    xj ≽ xi.

Definition header xs a b :=
  if decide (a = 0%nat) then True else one_le_seg xs (a - 1)%nat a b.

Theorem header__preserve:
  forall xs xs' a b,
  header xs a b ->
  Permutation xs xs' ->
  outside_same xs xs' a b ->
  (b <= length xs)%nat ->
  header xs' a b.
Proof.
  unfold header. unfold outside_same. unfold one_le_seg. intros.
  destruct (decide (a = 0%nat)) as [Heq | Hneq]; first auto. intros.
  rewrite <- H1 in H4; try lia.
  pose proof Permutation_existsIndex xs' xs j a b xj.
  destruct H6; auto; try lia.
  - symmetry. auto.
  - unfold outside_same. intros. rewrite H1; auto.
  - replace (length xs') with (length xs); try lia.
    apply Permutation_length. auto.
  - destruct H6. eapply H; eauto.
Qed.

Lemma wp_order2CmpFunc (data: slice.t) (a b: w64) (swaps_l: loc) (cmp_code: func.t)
                       dq (xs: list E) (swaps: w64) (xa xb: E) :
  0 ≤ sint.Z a →
  0 ≤ sint.Z b →
  {{{ is_pkg_init slices ∗
      "Hxs" ∷ data ↦*{dq} xs ∗
      "%Hxa" ∷ ⌜xs !! sint.nat a = Some xa⌝ ∗
      "%Hxb" ∷ ⌜xs !! sint.nat b = Some xb⌝ ∗
      "Hswaps" ∷ swaps_l ↦ swaps ∗
      "#Hcmp" ∷ cmp_implements cmp_code
  }}}
    #(functions slices.order2CmpFunc [Et]) #data #a #b #swaps_l #cmp_code
  {{{ (a' b': w64) (swaps': w64), RET (#a', #b');
      data ↦*{dq} xs ∗
      ⌜(a' = a ∧ b' = b ∧ xb ≽ xa) ∨
       (a' = b ∧ b' = a ∧ xb ≺ xa)⌝ ∗
      swaps_l ↦ swaps'
  }}}.
Proof using StrictWeakOrder0 + W.
  intros Ha_bound Hb_bound.
  wp_start as "H". iNamed "H".
  wp_auto.
  pose proof (lookup_lt_Some _ _ _ Hxa).
  pose proof (lookup_lt_Some _ _ _ Hxb).
  iDestruct (own_slice_len with "Hxs") as %Hlen.
  rewrite -> decide_True; last word.
  wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto.
  rewrite -> decide_True; last word.
  wp_apply (wp_load_slice_index with "[$Hxs]") as "Hxs"; eauto.
  wp_apply "Hcmp".
  iIntros (ba_r) "%Hba_r".
  wp_auto.
  change (sint.Z (W64 0)) with 0.
  wp_if_destruct.
  - iApply "HΦ". iFrame.
    iPureIntro. intuition.
  - iApply "HΦ". iFrame.
    iPureIntro. apply comparison_negate in Hba_r.
    intuition.
Qed.

End proof.
