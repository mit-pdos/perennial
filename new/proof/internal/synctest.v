From New.proof Require Export proof_prelude.
Require Export New.generatedproof.internal.synctest.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : synctest.Assumptions}.
Local Set Default Proof Using "All".

#[global] Instance : IsPkgInit (iProp Σ) synctest := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) synctest := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop synctest get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    synctest.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init synctest }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

(** synctest.Run is not supported by Perennial; it changes the semantics of go
    programs because it messes with runtime state (i.e. it creates a new
    bubble). *)
Lemma wp_Run (v : func.t) :
  {{{ is_pkg_init synctest ∗ False }}}
    @! synctest.Run #v
  {{{ RET #(); True }}}.
Proof. by wp_start. Qed.

(** synctest.IsInBubble always returns false since Perennial doesn't permit `synctest.Run`. *)
Lemma wp_IsInBubble :
  {{{ is_pkg_init synctest }}}
    @! synctest.IsInBubble #()
  {{{ RET #false; True }}}.
Proof. wp_start. wp_end. Qed.

End wps.
