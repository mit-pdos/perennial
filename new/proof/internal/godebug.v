From New.generatedproof Require Import internal.godebug.
From New.proof Require Import proof_prelude sync.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : godebug.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) godebug := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) godebug := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop godebug get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    godebug.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init godebug }}}.
Proof using W.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ") as "Hown".
  { destruct Hinit as (-> & ?); done. }
Admitted.

End wps.
