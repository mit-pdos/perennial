From New.proof Require Export proof_prelude.
Require Export New.generatedproof.internal.synctest.

Section wps.
Context `{heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit synctest := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf synctest := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop synctest get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init ∗ is_go_context ∗ □ is_pkg_defined synctest }}}
    synctest.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init synctest }}}.
Proof.
  intros Hinit. wp_start as "(Hown & #? & #Hdef)".
  wp_call. wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto. wp_call.
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
Proof. wp_start. by iApply "HΦ". Qed.

End wps.
