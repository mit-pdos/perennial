From New.generatedproof.github_com.sanjit_bhat.pav Require Import client.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

From New.proof Require Import bytes.
From New.proof.github_com.sanjit_bhat.pav Require Import
  cryptoffi ktcore.

From New.proof.github_com.sanjit_bhat.pav.client_proof Require Import
  base.

Module client.
Import base.client.
Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

End proof.
End client.
