From New.generatedproof Require Import math.
From New.proof Require Import proof_prelude.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : math.Assumptions}.
Local Set Default Proof Using "All".

#[global] Instance : IsPkgInit (iProp Σ) math := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) math := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop math get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    math.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init math }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#".
Admitted.

End wps.
