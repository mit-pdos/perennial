(* autogenerated by goose proofgen (types); do not modify *)
Require Export New.proof.proof_prelude.
Require Export New.code.github_com.tchajed.marshal.
Require Export New.golang.theory.

Module marshal.
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

Definition is_defined := is_global_definitions marshal.pkg_name' var_addrs marshal.functions' marshal.msets'.

Global Instance is_pkg_defined : PkgIsDefined marshal.pkg_name' is_defined :=
  ltac:(prove_pkg_is_defined).

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

Global Instance wp_func_call_compute_new_cap :
  WpFuncCall marshal.pkg_name' "compute_new_cap" _ (pkg_defined marshal.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_reserve :
  WpFuncCall marshal.pkg_name' "reserve" _ (pkg_defined marshal.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_ReadInt :
  WpFuncCall marshal.pkg_name' "ReadInt" _ (pkg_defined marshal.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_ReadInt32 :
  WpFuncCall marshal.pkg_name' "ReadInt32" _ (pkg_defined marshal.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_ReadBytes :
  WpFuncCall marshal.pkg_name' "ReadBytes" _ (pkg_defined marshal.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_ReadBytesCopy :
  WpFuncCall marshal.pkg_name' "ReadBytesCopy" _ (pkg_defined marshal.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_ReadBool :
  WpFuncCall marshal.pkg_name' "ReadBool" _ (pkg_defined marshal.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_WriteInt :
  WpFuncCall marshal.pkg_name' "WriteInt" _ (pkg_defined marshal.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_WriteInt32 :
  WpFuncCall marshal.pkg_name' "WriteInt32" _ (pkg_defined marshal.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_WriteBytes :
  WpFuncCall marshal.pkg_name' "WriteBytes" _ (pkg_defined marshal.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_WriteBool :
  WpFuncCall marshal.pkg_name' "WriteBool" _ (pkg_defined marshal.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_WriteLenPrefixedBytes :
  WpFuncCall marshal.pkg_name' "WriteLenPrefixedBytes" _ (pkg_defined marshal.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

End names.
End marshal.
