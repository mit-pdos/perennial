From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From New.generatedproof.github_com.sanjit_bhat.pav Require Import cryptoutil.
(* TODO(goose): brittleness with NamedProps import.
if iris import comes after, overrides custom syntax.
(shouldn't it be imported in overall prelude?) *)
From Perennial.Helpers Require Import NamedProps.
From New.proof.github_com.sanjit_bhat.pav Require Import cryptoffi.

Module cryptoutil.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !goGlobalsGS Σ}.

#[global]
Program Instance is_pkg_init_cryptoutil : IsPkgInit cryptoutil := ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_cryptoutil.
#[local] Transparent is_pkg_init_cryptoutil.

Lemma wp_Hash sl_b d0 b :
  {{{
    is_pkg_init cryptoutil ∗
    "Hsl_b" ∷ sl_b ↦*{d0} b
  }}}
  cryptoutil @ "Hash" #sl_b
  {{{
    sl_hash hash, RET #sl_hash;
    "Hsl_b" ∷ sl_b ↦*{d0} b ∗
    "Hsl_hash" ∷ sl_hash ↦* hash ∗
    "#His_hash" ∷ cryptoffi.is_hash b hash
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
