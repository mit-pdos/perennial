(* autogenerated by goose proofgen; do not modify *)
Require Export New.proof.proof_prelude.
Require Export New.golang.theory.

Require Export New.code.strconv.

Set Default Proof Using "Type".

Module strconv.

Section names.

Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Global Instance is_pkg_defined_instance : IsPkgDefined strconv :=
{|
  is_pkg_defined := is_global_definitions strconv var_addrs;
|}.

Definition own_allocated : iProp Σ :=
True.

End names.
End strconv.
