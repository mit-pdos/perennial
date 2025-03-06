(* autogenerated by goose proofgen (types); do not modify *)
Require Export New.proof.proof_prelude.
Require Export New.code.context.
Require Export New.golang.theory.

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

Definition is_defined := is_global_definitions context.pkg_name' var_addrs context.functions' context.msets'.

Global Instance is_pkg_defined : PkgIsDefined context.pkg_name' is_defined :=
  ltac:(prove_pkg_is_defined).

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

End names.
End context.
