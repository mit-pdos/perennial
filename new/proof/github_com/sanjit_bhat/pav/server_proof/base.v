From New.generatedproof.github_com.sanjit_bhat.pav Require Import server.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

From New.proof Require Import sync time.
From New.proof.github_com.goose_lang Require Import std.
From New.proof.github_com.sanjit_bhat.pav Require Import
  advrpc cryptoffi hashchain ktcore merkle safemarshal.
From New.proof.github_com.tchajed Require Import marshal.

Module server.
Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit server := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf server := build_get_is_pkg_init_wf.

End proof.
End server.
