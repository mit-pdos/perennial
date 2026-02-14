From New.generatedproof Require Import unsafe.
From New.proof Require Import proof_prelude.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : unsafe.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) unsafe := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) unsafe := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop unsafe get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    unsafe.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init unsafe }}}.
Proof using W.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ") as "Hown".
  { destruct Hinit as (-> & ?); done. }
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

End wps.
