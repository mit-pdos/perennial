From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From New.generatedproof.github_com.sanjit_bhat.pav Require Import cryptoutil.
From New.proof.github_com.sanjit_bhat.pav Require Import cryptoffi.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !goGlobalsGS Σ}.
Context `{!cryptoffi.GlobalAddrs, !cryptoutil.GlobalAddrs}.

#[global]
Program Instance is_pkg_init_cryptoutil : IsPkgInit cryptoutil := ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_cryptoutil.

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
    "#His_hash" ∷ is_hash b hash
  }}}.
Proof.
  wp_start. iNamed "Hpre".
  (* XXX: should have been done by wp_start. *)
  wp_func_call.
  {
    About cryptoutil.is_pkg_defined_instance.
    Fail iPkgInit. Fail solve_pkg_init.
    admit.
  }
Admitted.

End proof.
