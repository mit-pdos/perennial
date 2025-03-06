(* autogenerated by goose proofgen (types); do not modify *)
Require Export New.proof.grove_prelude.
Require Export New.manualproof.github_com.mit_pdos.gokv.grove_ffi.
Require Export New.code.github_com.mit_pdos.gokv.grove_ffi.
Require Export New.golang.theory.

Module grove_ffi.
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

Definition is_defined := is_global_definitions grove_ffi.pkg_name' var_addrs.

Global Instance : PkgIsDefined grove_ffi.pkg_name' is_defined :=
  ltac:(prove_pkg_is_defined).

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

Global Instance wp_func_call_FileWrite :
  WpFuncCall grove_ffi.pkg_name' "FileWrite" _ (is_pkg_defined grove_ffi.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_FileRead :
  WpFuncCall grove_ffi.pkg_name' "FileRead" _ (is_pkg_defined grove_ffi.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_FileAppend :
  WpFuncCall grove_ffi.pkg_name' "FileAppend" _ (is_pkg_defined grove_ffi.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Listen :
  WpFuncCall grove_ffi.pkg_name' "Listen" _ (is_pkg_defined grove_ffi.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Accept :
  WpFuncCall grove_ffi.pkg_name' "Accept" _ (is_pkg_defined grove_ffi.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Connect :
  WpFuncCall grove_ffi.pkg_name' "Connect" _ (is_pkg_defined grove_ffi.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Send :
  WpFuncCall grove_ffi.pkg_name' "Send" _ (is_pkg_defined grove_ffi.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Receive :
  WpFuncCall grove_ffi.pkg_name' "Receive" _ (is_pkg_defined grove_ffi.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_GetTimeRange :
  WpFuncCall grove_ffi.pkg_name' "GetTimeRange" _ (is_pkg_defined grove_ffi.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_GetTSC :
  WpFuncCall grove_ffi.pkg_name' "GetTSC" _ (is_pkg_defined grove_ffi.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

End names.
End grove_ffi.
