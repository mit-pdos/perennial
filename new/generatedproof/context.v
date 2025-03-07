(* autogenerated by goose proofgen; do not modify *)
Require Export New.proof.proof_prelude.
Require Export New.golang.theory.

Require Export New.code.context.
Module context.
Axiom falso : False.

Module Context.
Section def.
Context `{ffi_syntax}.
Definition t := interface.t.
End def.
End Context.

Module CancelFunc.
Section def.
Context `{ffi_syntax}.
Definition t := func.t.
End def.
End CancelFunc.

Section names.

Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Global Instance is_pkg_defined_instance : IsPkgDefined context :=
{|
  is_pkg_defined := is_global_definitions context var_addrs;
|}.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

End names.
End context.
