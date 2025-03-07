(* autogenerated by goose proofgen (types); do not modify *)
Require Export New.proof.proof_prelude.
Require Export New.code.os.
Require Export New.golang.theory.

Module os.
Axiom falso : False.

Section names.

Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Global Instance is_pkg_defined_instance : IsPkgDefined os.pkg_name' :=
{|
  is_pkg_defined := is_global_definitions os.pkg_name' var_addrs;
|}.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

End names.
End os.
