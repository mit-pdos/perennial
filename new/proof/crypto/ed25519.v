From New.proof Require Import proof_prelude.
From New.generatedproof.crypto Require Import ed25519.

Module ed25519.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : ed25519.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) ed25519 := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) ed25519 := build_get_is_pkg_init_wf.
Local Lemma wp_cryptocustomrand_init :
  {{{ True }}} ed25519.cryptocustomrand'init #() {{{ RET #(); True }}}.
Proof. Admitted.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop ed25519 get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    ed25519.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init ed25519 }}}.
Proof using W.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ") as "Hown".
  { destruct Hinit as (-> & ?); done. }
  wp_apply wp_cryptocustomrand_init.
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

End proof.
End ed25519.
