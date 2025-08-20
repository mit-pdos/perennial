From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From New.generatedproof.github_com.sanjit_bhat.pav Require Import cryptoutil.
(* TODO(goose): brittleness with NamedProps import.
if iris import comes after, overrides custom syntax.
(shouldn't it be imported in overall prelude?) *)
From Perennial.Helpers Require Import NamedProps.
From New.proof.github_com.sanjit_bhat.pav Require Import cryptoffi.

Module cryptoutil.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit cryptoutil := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf cryptoutil := build_get_is_pkg_init.
#[global] Instance : IsPkgDefinedTransitiveClosure cryptoutil := build_is_pkg_defined_tc.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init cryptoutil = (is_pkg_init cryptoutil) →
  {{{ own_initializing ∗ is_initialization get_is_pkg_init ∗ is_pkg_defined cryptoutil }}}
    cryptoutil.initialize' #()
  {{{ RET #(); own_initializing ∗ is_pkg_init cryptoutil }}}.
Proof.
  intros Hinit. wp_start as "(Hown & #Hinit & #Hdef)".
  wp_call. wp_apply (wp_package_init with "[$Hown $Hinit]").
  2: { rewrite Hinit //. }
  iIntros "Hown". wp_auto.
  wp_apply (cryptoffi.wp_initialize' with "[$Hown]").
  2: { iFrame "#".
    (* TODO: don't transitively know [is_pkg_defined].
    could add [is_pkg_defined] deps as assumption,
    or that could be implicit in [is_pkg_defined] def. *)
    admit. }
Admitted.

Lemma wp_Hash sl_b d0 b :
  {{{
    is_pkg_init cryptoutil ∗
    "Hsl_b" ∷ sl_b ↦*{d0} b
  }}}
  @! cryptoutil.Hash #sl_b
  {{{
    sl_hash hash, RET #sl_hash;
    "Hsl_b" ∷ sl_b ↦*{d0} b ∗
    "Hsl_hash" ∷ sl_hash ↦* hash ∗
    "#His_hash" ∷ cryptoffi.is_hash (Some b) hash
  }}}.
Proof.
  wp_start. iNamed "Hpre".
  wp_auto.
  wp_apply cryptoffi.wp_NewHasher as "* @".
  wp_apply (cryptoffi.wp_Hasher_Write with "[$Hown_hr $Hsl_b]") as "@".
  wp_apply (cryptoffi.wp_Hasher_Sum with "[$Hown_hr]") as "* @".
  { iApply own_slice_nil. }
  iApply "HΦ".
  list_simplifier.
  iFrame "∗#".
Qed.

End proof.
End cryptoutil.
