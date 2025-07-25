From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From New.generatedproof.github_com.sanjit_bhat.pav Require Import safemarshal.
From Perennial.Helpers Require Import NamedProps.

From New.proof.github_com.tchajed Require Import marshal.

Module safemarshal.
Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !goGlobalsGS Σ}.

#[global]
Program Instance is_pkg_init_safemarshal : IsPkgInit safemarshal := ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_safemarshal.
#[local] Transparent is_pkg_init_safemarshal.

End proof.
End safemarshal.
