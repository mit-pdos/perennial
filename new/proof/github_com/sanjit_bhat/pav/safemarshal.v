From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From New.generatedproof.github_com.sanjit_bhat.pav Require Import safemarshal.
From Perennial.Helpers Require Import NamedProps.

From New.proof.github_com.tchajed Require Import marshal.

Module safemarshal.
Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit safemarshal := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf safemarshal := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop safemarshal get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init ∗ is_go_context ∗ □ is_pkg_defined safemarshal }}}
    safemarshal.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init safemarshal }}}.
Proof.
  intros Hinit. wp_start as "(Hown & #? & #Hdef)".
  wp_call. wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.

  wp_apply (marshal.wp_initialize' with "[$Hown]").
  { naive_solver. }
  { iModIntro. iEval simpl_is_pkg_defined in "Hdef". iPkgInit. }
  iIntros "(Hown & #?)". wp_auto.
  wp_call. iFrame. iEval (rewrite is_pkg_init_unfold).
  simpl. iFrame "#". done.
Qed.

End proof.
End safemarshal.
