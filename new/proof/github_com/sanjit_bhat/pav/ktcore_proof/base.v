From New.generatedproof.github_com.sanjit_bhat.pav Require Import ktcore.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

From New.proof.github_com.sanjit_bhat.pav Require Import
  cryptoffi cryptoutil safemarshal.
From New.proof.github_com.tchajed Require Import marshal.

Module ktcore.
Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit ktcore := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf ktcore := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop ktcore get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init ∗ is_go_context ∗ □ is_pkg_defined ktcore }}}
    ktcore.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init ktcore }}}.
Proof.
  intros Hinit. wp_start as "(Hown & #? & #Hdef)".
  wp_call. wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  wp_apply (marshal.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  { iModIntro. iEval simpl_is_pkg_defined in "Hdef". iPkgInit. }
  wp_apply (safemarshal.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  { iModIntro. iEval simpl_is_pkg_defined in "Hdef". iPkgInit. }
  wp_apply (cryptoutil.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  { iModIntro. iEval simpl_is_pkg_defined in "Hdef". iPkgInit. }
  wp_apply (cryptoffi.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  { iModIntro. iEval simpl_is_pkg_defined in "Hdef". iPkgInit. }
  wp_call. iEval (rewrite is_pkg_init_unfold /=). by iFrame "∗#".
Qed.

End proof.
End ktcore.
