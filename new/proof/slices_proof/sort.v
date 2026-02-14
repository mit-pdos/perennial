From New.generatedproof Require Import slices.
From New.proof Require Import proof_prelude.
From New.proof Require Import math.bits.
From New.proof.slices_proof Require Import slices_init.
From New.proof.slices_proof.pdqSort Require Import sort_basics pdqSort.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : slices.Assumptions}.

#[global] Instance : IsPkgInit (iProp Σ) slices := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) slices := build_get_is_pkg_init_wf.
Context `{!ZeroVal E} `{!TypedPointsto E} `{!IntoValTyped E Et}.
Context (R: E → E → Prop) `{!RelDecision R}.
Collection W := sem + package_sem + IntoValTyped0.

(*
  We assume a binary relation R on elements, which is a "strict weak order".
  The comparison function cmp_code implements R:
      cmp_code x y < 0  ↔  iff R x y
  The sorting procedure returns a permutation of the input slice and ensures
  that the output is ordered with respect to R.

  For integer, R can be (<), and the postcondition "%Hsorted" gives (informally):
      ∀ i < j,  data[i] ≤ data[j]
*)

Lemma wp_SortFunc [S] `[!S ↓u go.SliceType Et] (data: slice.t) (cmp_code: func.t) (xs: list E) :
      StrictWeakOrder R ->
  {{{ is_pkg_init slices ∗
      "Hxs" ∷ data ↦* xs ∗
      "%Hlength_bound" ∷ ⌜ length xs <= 2 ^ 62⌝ ∗
      "#Hcmp" ∷ cmp_implements R cmp_code
  }}}
    #(functions slices.SortFunc [S; Et]) #data #cmp_code
  {{{ (xs': list E), RET #();
      "Hxs" ∷ data ↦* xs' ∗
      "%Hperm" ∷ ⌜ xs ≡ₚ xs' ⌝ ∗
      "%Hsorted" ∷ ⌜ ∀ (i j: nat) (xi xj: E), xs' !! i = Some xi -> xs' !! j = Some xj -> (i < j)%nat -> ¬ (R xj xi) ⌝
  }}}.
Proof using RelDecision0 + W.
  intros SWO. wp_start as "H". iNamed "H". wp_auto.
  iDestruct (own_slice_len with "Hxs") as "%Hlen".
  wp_apply (wp_Len). iIntros (y) "_". wp_auto.
  wp_apply (wp_pdqsortCmpFunc with "[$Hxs]"). {
    iSplit.
    - word.
    - auto.
  }
  iIntros (xs') "Hpost". iNamed "Hpost".
  wp_auto. iApply "HΦ". iFrame.
  iPureIntro. split.
  - assumption.
  - intros. eapply is_sorted_seg__is_sorted; eauto.
    destruct Hlen. replace (length xs') with (length xs).
    + rewrite H3. apply Hsorted.
    + apply Permutation_length. assumption.
Qed.

End proof.
