(* autogenerated by goose proofgen (types); do not modify *)
Require Export New.proof.proof_prelude.
Require Export New.code.slices.
Require Export New.golang.theory.

Module slices.
Definition imported_pkgs: list go_string := [].
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

Definition is_defined := is_global_definitions slices.pkg_name' var_addrs slices.functions' slices.msets'.

Global Instance is_pkg_defined : PkgIsDefined slices.pkg_name' is_defined :=
  ltac:(prove_pkg_is_defined).

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

End names.
End slices.
