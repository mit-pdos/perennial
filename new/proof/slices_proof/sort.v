From New.generatedproof Require Import slices.
From New.proof Require Import proof_prelude.
From New.proof.slices_proof Require Import slices_init.
From New.proof.slices_proof.pdqSort Require Import sort_basics pdqSort.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : slices.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) slices := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) slices := build_get_is_pkg_init_wf.
Context `{!ZeroVal E} `{!TypedPointsto E} `{!IntoValTyped E Et}.
Context (R: E → E → Prop) `{!RelDecision R}.

(*
  We assume a binary relation R on elements, which is a "strict weak order".
  The comparison function cmp_code implements R:
      cmp_code x y < 0  ↔  iff R x y
  The sorting procedure returns a permutation of the input slice and ensures
  that the output is ordered with respect to R.

  For integer, R can be (<), and the postcondition "%Hsorted" gives (informally):
      ∀ i < j,  data[i] ≤ data[j]
*)

Lemma wp_pdqsortCmpFunc (data: slice.t) (cmp_code: func.t) (xs: list E):
      StrictWeakOrder R ->
  {{{ is_pkg_init slices ∗
      "Hxs" ∷ data ↦* xs ∗
      "%Hlength_bound" ∷ ⌜ length xs <= 2 ^ 62⌝ ∗
      "#Hcmp" ∷ cmp_implements R cmp_code
  }}}
    @! slices.SortFunc #sliceT #Et #data #cmp_code
  {{{ (xs': list E), RET #();
      "Hxs" ∷ data ↦* xs' ∗
      "%Hperm" ∷ ⌜ xs ≡ₚ xs' ⌝ ∗
      "%Hsorted" ∷ ⌜ ∀ (i j: nat) (xi xj: E), xs' !! i = Some xi -> xs' !! j = Some xj -> (i < j)%nat -> ¬ (R xj xi) ⌝
  }}}.
Proof using globalsGS0 RelDecision0 BoundedTypeSize0.
  intros SWO. wp_start as "H". iNamed "H". wp_auto.
  iAssert(⌜length xs = sint.nat data .(slice.len_f) ∧ 0 ≤ sint.Z data .(slice.len_f)⌝)%I with "[Hxs]" as "%Hlen".
  { iApply own_slice_len. iFrame. }
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
    + rewrite H2. apply Hsorted.
    + apply Permutation_length. assumption.
Qed.

End proof.
