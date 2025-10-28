From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From New.generatedproof.github_com.sanjit_bhat.pav Require Import ktcore.
From Perennial.Helpers Require Import NamedProps.

From New.proof.github_com.sanjit_bhat.pav Require Import
  cryptoffi cryptoutil.

Module ktcore.
Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Inductive Blame :=
  | BlameServSig
  | BlameServFull
  | BlameAdtrSig
  | BlameAdtrFull
  | BlameClients
  | BlameUnknown.

End proof.
End ktcore.
