(* autogenerated by goose proofgen (types); do not modify *)
Require Export New.proof.disk_prelude.
Require Export New.generatedproof.sync.
Require Export New.generatedproof.github_com.tchajed.marshal.
Require Export New.generatedproof.github_com.goose_lang.primitive.disk.
Require Export New.code.github_com.goose_lang.goose.testdata.examples.append_log.
Require Export New.golang.theory.

Module append_log.
Axiom falso : False.
Module Log.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  m' : loc;
  sz' : w64;
  diskSz' : w64;
}.
End def.
End Log.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_Log `{ffi_syntax}: Settable _ :=
  settable! Log.mk < Log.m'; Log.sz'; Log.diskSz' >.
Global Instance into_val_Log `{ffi_syntax} : IntoVal Log.t.
Admitted.

Global Instance into_val_typed_Log `{ffi_syntax} : IntoValTyped Log.t append_log.Log :=
{|
  default_val := Log.mk (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_Log_m `{ffi_syntax} : IntoValStructField "m" append_log.Log Log.m'.
Admitted.

Global Instance into_val_struct_field_Log_sz `{ffi_syntax} : IntoValStructField "sz" append_log.Log Log.sz'.
Admitted.

Global Instance into_val_struct_field_Log_diskSz `{ffi_syntax} : IntoValStructField "diskSz" append_log.Log Log.diskSz'.
Admitted.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_Log `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} m' sz' diskSz':
  PureWp True
    (struct.make append_log.Log (alist_val [
      "m" ::= #m';
      "sz" ::= #sz';
      "diskSz" ::= #diskSz'
    ]))%V
    #(Log.mk m' sz' diskSz').
Admitted.


Global Instance Log_struct_fields_split dq l (v : Log.t) :
  StructFieldsSplit dq l v (
    "Hm" ∷ l ↦s[append_log.Log :: "m"]{dq} v.(Log.m') ∗
    "Hsz" ∷ l ↦s[append_log.Log :: "sz"]{dq} v.(Log.sz') ∗
    "HdiskSz" ∷ l ↦s[append_log.Log :: "diskSz"]{dq} v.(Log.diskSz')
  ).
Admitted.

End instances.

Section names.

Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Definition is_defined := is_global_definitions append_log.pkg_name' var_addrs append_log.functions' append_log.msets'.

Global Instance is_pkg_defined : PkgIsDefined append_log.pkg_name' is_defined :=
  ltac:(prove_pkg_is_defined).

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

Global Instance wp_func_call_Init :
  WpFuncCall append_log.pkg_name' "Init" _ (pkg_defined append_log.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Open :
  WpFuncCall append_log.pkg_name' "Open" _ (pkg_defined append_log.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_writeAll :
  WpFuncCall append_log.pkg_name' "writeAll" _ (pkg_defined append_log.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_method_call_Log'ptr_Append :
  WpMethodCall append_log.pkg_name' "Log'ptr" "Append" _ (pkg_defined append_log.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Log'ptr_Get :
  WpMethodCall append_log.pkg_name' "Log'ptr" "Get" _ (pkg_defined append_log.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Log'ptr_Reset :
  WpMethodCall append_log.pkg_name' "Log'ptr" "Reset" _ (pkg_defined append_log.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Log'ptr_append :
  WpMethodCall append_log.pkg_name' "Log'ptr" "append" _ (pkg_defined append_log.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Log'ptr_get :
  WpMethodCall append_log.pkg_name' "Log'ptr" "get" _ (pkg_defined append_log.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Log'ptr_mkHdr :
  WpMethodCall append_log.pkg_name' "Log'ptr" "mkHdr" _ (pkg_defined append_log.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Log'ptr_reset :
  WpMethodCall append_log.pkg_name' "Log'ptr" "reset" _ (pkg_defined append_log.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Log'ptr_writeHdr :
  WpMethodCall append_log.pkg_name' "Log'ptr" "writeHdr" _ (pkg_defined append_log.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

End names.
End append_log.
