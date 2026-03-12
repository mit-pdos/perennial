From New.generatedproof Require Import cmp.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : cmp.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) cmp := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) cmp := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop cmp get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    cmp.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init cmp }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

End wps.
