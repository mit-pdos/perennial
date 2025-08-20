From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From New.generatedproof.github_com.sanjit_bhat.pav Require Import safemarshal.
From Perennial.Helpers Require Import NamedProps.

From New.proof.github_com.tchajed Require Import marshal.

Module safemarshal.
Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit safemarshal := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf safemarshal := build_get_is_pkg_init.
#[global] Instance : IsPkgDefinedTransitiveClosure safemarshal := build_is_pkg_defined_tc.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init safemarshal = (is_pkg_init safemarshal) →
  {{{ own_initializing ∗ is_initialization get_is_pkg_init ∗ is_pkg_defined safemarshal }}}
    safemarshal.initialize' #()
  {{{ RET #(); own_initializing ∗ is_pkg_init safemarshal }}}.
Proof.
  intros Hinit. wp_start as "(Hown & #Hinit & #Hdef)".
  wp_call. wp_apply (wp_package_init with "[$Hown $Hinit]").
  2:{ rewrite Hinit //. }
  iIntros "Hown". wp_auto.
Admitted.

End proof.
End safemarshal.
