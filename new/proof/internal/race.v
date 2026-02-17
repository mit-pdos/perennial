Require Export New.code.internal.race.
From New.proof Require Export proof_prelude.
Require Export New.generatedproof.internal.race.

Section init.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : race.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) race := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) race := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop race get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    race.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init race }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

End init.
