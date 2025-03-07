(* autogenerated by goose proofgen (types); do not modify *)
Require Export New.proof.proof_prelude.
Require Export New.manualproof.log.
Require Export New.code.log.
Require Export New.golang.theory.

Module log.
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

Global Instance is_pkg_defined_instance : IsPkgDefined log.pkg_name' :=
{|
  is_pkg_defined := is_global_definitions log.pkg_name' var_addrs;
|}.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

Global Instance wp_func_call_Printf :
  WpFuncCall log.pkg_name' "Printf" _ (is_pkg_defined log.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Println :
  WpFuncCall log.pkg_name' "Println" _ (is_pkg_defined log.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

End names.
End log.
