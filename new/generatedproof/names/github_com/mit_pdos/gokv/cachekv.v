(* autogenerated by namegen; do not modify *)
Require Import New.code.github_com.mit_pdos.gokv.cachekv.
Require Export New.proof.grove_prelude.
Module cachekv.
Section defs.
Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{ffi_syntax}Context `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs `{!GlobalAddrs} : list (go_string * loc) := [
  ].

Definition is_defined := is_global_definitions cachekv.pkg_name' var_addrs cachekv.functions' cachekv.msets'.

Global Instance wp_func_call_DecodeValue : 
  WpFuncCall cachekv.pkg_name' "DecodeValue" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_EncodeValue : 
  WpFuncCall cachekv.pkg_name' "EncodeValue" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_max : 
  WpFuncCall cachekv.pkg_name' "max" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Make : 
  WpFuncCall cachekv.pkg_name' "Make" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_method_call_CacheKv'ptr_Get : 
  WpMethodCall cachekv.pkg_name' "CacheKv'ptr" "Get" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_CacheKv'ptr_GetAndCache : 
  WpMethodCall cachekv.pkg_name' "CacheKv'ptr" "GetAndCache" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_CacheKv'ptr_Put : 
  WpMethodCall cachekv.pkg_name' "CacheKv'ptr" "Put" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

End defs.
End cachekv.
