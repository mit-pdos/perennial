(* autogenerated by goose proofgen; do not modify *)
Require Export New.proof.disk_prelude.
Require Export New.manualproof.github_com.goose_lang.primitive.disk.
Require Export New.golang.theory.

Require Export New.code.github_com.goose_lang.primitive.disk.
Module disk.
Axiom falso : False.

Section names.

Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Global Instance is_pkg_defined_instance : IsPkgDefined disk :=
{|
  is_pkg_defined := is_global_definitions disk var_addrs;
|}.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

Global Instance wp_func_call_Get :
  WpFuncCall disk "Get" _ (is_pkg_defined disk) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Read :
  WpFuncCall disk "Read" _ (is_pkg_defined disk) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Write :
  WpFuncCall disk "Write" _ (is_pkg_defined disk) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Size :
  WpFuncCall disk "Size" _ (is_pkg_defined disk) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Barrier :
  WpFuncCall disk "Barrier" _ (is_pkg_defined disk) :=
  ltac:(apply wp_func_call'; reflexivity).

End names.
End disk.
