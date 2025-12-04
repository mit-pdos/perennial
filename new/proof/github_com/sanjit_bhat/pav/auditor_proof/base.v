From New.generatedproof.github_com.sanjit_bhat.pav Require Import auditor.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

From New.proof Require Import bytes sync.
From New.proof.github_com.sanjit_bhat.pav Require Import
  advrpc cryptoffi hashchain ktcore merkle safemarshal server.

Module auditor.
Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit auditor := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf auditor := build_get_is_pkg_init_wf.

End proof.
End auditor.
