From New.generatedproof.github_com.sanjit_bhat.pav Require Import advrpc.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

From New.proof.github_com.sanjit_bhat.pav Require Import
  safemarshal netffi.

Module advrpc.
Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit advrpc := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf advrpc := build_get_is_pkg_init_wf.

End proof.
End advrpc.
