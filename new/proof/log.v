Require Import New.code.log.
Require Import New.generatedproof.log.
Require Import New.proof.proof_prelude.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : log.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) log := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) log := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop log get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    log.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init log }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#".
Admitted.

Theorem wp_Printf (msg: go_string) (arg: slice.t) :
  {{{ is_pkg_init log }}}
    @! log.Printf #msg #arg
  {{{ RET #(); True }}}.
Proof.
  wp_start as "_". iApply "HΦ". done.
Qed.

End wps.
