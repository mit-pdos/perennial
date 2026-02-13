From New.generatedproof Require Import slices.
From New.proof Require Import proof_prelude.
From New.proof.math_proof Require Import bits_init.

Module slices.
Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : slices.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) slices := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) slices := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop slices get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    slices.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init slices }}}.
Proof using W.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

End proof.
End slices.
