(* autogenerated by goose proofgen (types); do not modify *)
From New.code Require Import github_com.tchajed.marshal.
From New.golang Require Import theory.

Axiom falso : False.

(* autogenerated by proofgen (names); do not modify *)
Require Import New.code.github_com.tchajed.marshal.
Require Export New.proof.proof_prelude.
Module marshal.
Section defs.
Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Definition is_defined := is_global_definitions marshal.pkg_name' var_addrs marshal.functions' marshal.msets'.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

Global Instance wp_func_call_compute_new_cap : 
  WpFuncCall marshal.pkg_name' "compute_new_cap" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_reserve : 
  WpFuncCall marshal.pkg_name' "reserve" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_ReadInt : 
  WpFuncCall marshal.pkg_name' "ReadInt" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_ReadInt32 : 
  WpFuncCall marshal.pkg_name' "ReadInt32" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_ReadBytes : 
  WpFuncCall marshal.pkg_name' "ReadBytes" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_ReadBytesCopy : 
  WpFuncCall marshal.pkg_name' "ReadBytesCopy" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_ReadBool : 
  WpFuncCall marshal.pkg_name' "ReadBool" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_WriteInt : 
  WpFuncCall marshal.pkg_name' "WriteInt" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_WriteInt32 : 
  WpFuncCall marshal.pkg_name' "WriteInt32" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_WriteBytes : 
  WpFuncCall marshal.pkg_name' "WriteBytes" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_WriteBool : 
  WpFuncCall marshal.pkg_name' "WriteBool" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_WriteLenPrefixedBytes : 
  WpFuncCall marshal.pkg_name' "WriteLenPrefixedBytes" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

End defs.
End marshal.
