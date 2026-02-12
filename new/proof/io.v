From New.generatedproof Require Import io.
From New.proof Require Import sync errors.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : io.Assumptions}.
Local Set Default Proof Using "All".

#[global] Instance : IsPkgInit (iProp Σ) io := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) io := build_get_is_pkg_init_wf.

Lemma wp_blackHolePool_init :
  {{{ is_pkg_init sync }}}
    io.blackHolePool'init #()
  {{{ RET #(); True }}}.
Proof.
Admitted.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop io get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    io.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init io }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  repeat wp_apply wp_GlobalAlloc as "?".
  wp_apply (sync.wp_initialize' with "[$Hown]") as "(Hown & #?)"; first naive_solver.
  wp_apply (errors.wp_initialize' with "[$Hown]") as "(Hown & #?)"; first naive_solver.
  repeat wp_apply wp_New as "% _".
  wp_apply wp_blackHolePool_init.
  wp_apply wp_New as "% _".
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

End wps.
