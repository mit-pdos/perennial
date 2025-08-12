From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From New.generatedproof.github_com.sanjit_bhat.pav Require Import safemarshal.
From Perennial.Helpers Require Import NamedProps.

From New.proof.github_com.tchajed Require Import marshal.

Module safemarshal.
Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} `{!GoContext}.

Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'safemarshal).
#[global] Program Instance : IsPkgInit safemarshal :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

End proof.
End safemarshal.
