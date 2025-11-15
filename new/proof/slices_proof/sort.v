From New.generatedproof Require Import slices.
From New.proof Require Import proof_prelude.
From New.proof.slices_proof Require Import slices_init.

Class WeakOrder {A} (R: A → A → Prop) :=
  { weak_order_irrefl :> Irreflexive R;
    weak_order_anti_symm : ∀ x y, R x y ↔ ¬R y x;
    weak_order_trans :> Transitive R;
  }.

Section proof.
Context  `{hG: heapGS Σ, !ffi_semantics _ _} `{!globalsGS Σ} {go_ctx : GoContext}.

Context `{!IntoVal E} `{!IntoValTyped E Et} `{!BoundedTypeSize Et}.
Context (R: E → E → Prop) `{!WeakOrder R} `{!RelDecision R}.

#[local] Infix "≺" := R (at level 70).
#[local] Notation "x ⪰ y" := (R y x) (at level 70, only parsing).

Definition cmp_implements (cmp_code: func.t) : iProp Σ :=
  ∀ (x y: E),
  {{{ True }}}
    #cmp_code #x #y
  {{{ (r: w64), RET #r;
      (* the sort implementation only ever checks cmp x y < 0; it does not
      distinguish between 0 and positive comparisons *)
      ⌜sint.Z r < 0 ↔ R x y⌝
      }}}.

#[export] Instance cmp_implements_persistent cmp_code :
  Persistent (cmp_implements cmp_code).
Proof. apply _. Qed.

Lemma comparison_negate (r: w64) (x y: E) :
  (sint.Z r < 0 ↔ x ≺ y) →
  ¬(sint.Z r < 0) ↔ x ⪰ y.
Proof using WeakOrder0.
  intros H.
  rewrite weak_order_anti_symm.
  intuition.
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
    @! slices.order2CmpFunc #Et #data #a #b #swaps_l #cmp_code
  {{{ (a' b': w64) (swaps': w64), RET (#a', #b');
      data ↦*{dq} xs ∗
      ⌜(a' = a ∧ b' = b ∧ xa ≺ xb) ∨
       (a' = b ∧ b' = a ∧ xa ⪰ xb)⌝ ∗
      swaps_l ↦ swaps'
  }}}.
Proof using WeakOrder0.
  intros Ha_bound Hb_bound.
  wp_start as "H". iNamed "H".
  wp_auto.
  pose proof (lookup_lt_Some _ _ _ Hxa).
  pose proof (lookup_lt_Some _ _ _ Hxb).
  iDestruct (own_slice_len with "Hxs") as %Hlen.
  wp_pure; first word.
  wp_apply (wp_load_slice_elem with "[$Hxs]") as "Hxs"; eauto.
  wp_pure; first word.
  wp_apply (wp_load_slice_elem with "[$Hxs]") as "Hxs"; eauto.
  wp_apply "Hcmp".
  iIntros (ba_r) "%Hba_r".
  wp_auto.
  change (sint.Z (W64 0)) with 0.
  wp_if_destruct.
  - iApply "HΦ". iFrame.
    iPureIntro.
    intuition.
  - iApply "HΦ". iFrame.
    iPureIntro. apply comparison_negate in Hba_r.
    intuition.
Qed.

End proof.
