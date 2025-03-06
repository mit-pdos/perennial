(* autogenerated by goose proofgen (types); do not modify *)
Require Export New.proof.proof_prelude.
Require Export New.generatedproof.github_com.goose_lang.primitive.
Require Export New.generatedproof.github_com.mit_pdos.gokv.kv.
Require Export New.generatedproof.github_com.mit_pdos.gokv.lockservice.
Require Export New.generatedproof.github_com.tchajed.marshal.
Require Export New.code.github_com.mit_pdos.gokv.bank.
Require Export New.golang.theory.

Module bank.
Axiom falso : False.
Module BankClerk.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  lck' : loc;
  kvck' : kv.Kv.t;
  accts' : slice.t;
}.
End def.
End BankClerk.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_BankClerk `{ffi_syntax}: Settable _ :=
  settable! BankClerk.mk < BankClerk.lck'; BankClerk.kvck'; BankClerk.accts' >.
Global Instance into_val_BankClerk `{ffi_syntax} : IntoVal BankClerk.t.
Admitted.

Global Instance into_val_typed_BankClerk `{ffi_syntax} : IntoValTyped BankClerk.t bank.BankClerk :=
{|
  default_val := BankClerk.mk (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_BankClerk_lck `{ffi_syntax} : IntoValStructField "lck" bank.BankClerk BankClerk.lck'.
Admitted.

Global Instance into_val_struct_field_BankClerk_kvck `{ffi_syntax} : IntoValStructField "kvck" bank.BankClerk BankClerk.kvck'.
Admitted.

Global Instance into_val_struct_field_BankClerk_accts `{ffi_syntax} : IntoValStructField "accts" bank.BankClerk BankClerk.accts'.
Admitted.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_BankClerk `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} lck' kvck' accts':
  PureWp True
    (struct.make bank.BankClerk (alist_val [
      "lck" ::= #lck';
      "kvck" ::= #kvck';
      "accts" ::= #accts'
    ]))%V
    #(BankClerk.mk lck' kvck' accts').
Admitted.


Global Instance BankClerk_struct_fields_split dq l (v : BankClerk.t) :
  StructFieldsSplit dq l v (
    "Hlck" ∷ l ↦s[bank.BankClerk :: "lck"]{dq} v.(BankClerk.lck') ∗
    "Hkvck" ∷ l ↦s[bank.BankClerk :: "kvck"]{dq} v.(BankClerk.kvck') ∗
    "Haccts" ∷ l ↦s[bank.BankClerk :: "accts"]{dq} v.(BankClerk.accts')
  ).
Admitted.

End instances.

Section names.

Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Definition is_defined := is_global_definitions bank.pkg_name' var_addrs bank.functions' bank.msets'.

Global Instance is_pkg_defined : PkgIsDefined bank.pkg_name' is_defined :=
  ltac:(prove_pkg_is_defined).

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

Global Instance wp_func_call_acquire_two_good :
  WpFuncCall bank.pkg_name' "acquire_two_good" _ (pkg_defined bank.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_acquire_two :
  WpFuncCall bank.pkg_name' "acquire_two" _ (pkg_defined bank.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_release_two :
  WpFuncCall bank.pkg_name' "release_two" _ (pkg_defined bank.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_encodeInt :
  WpFuncCall bank.pkg_name' "encodeInt" _ (pkg_defined bank.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_decodeInt :
  WpFuncCall bank.pkg_name' "decodeInt" _ (pkg_defined bank.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_MakeBankClerkSlice :
  WpFuncCall bank.pkg_name' "MakeBankClerkSlice" _ (pkg_defined bank.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_MakeBankClerk :
  WpFuncCall bank.pkg_name' "MakeBankClerk" _ (pkg_defined bank.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_method_call_BankClerk'ptr_SimpleAudit :
  WpMethodCall bank.pkg_name' "BankClerk'ptr" "SimpleAudit" _ (pkg_defined bank.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_BankClerk'ptr_SimpleTransfer :
  WpMethodCall bank.pkg_name' "BankClerk'ptr" "SimpleTransfer" _ (pkg_defined bank.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_BankClerk'ptr_get_total :
  WpMethodCall bank.pkg_name' "BankClerk'ptr" "get_total" _ (pkg_defined bank.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_BankClerk'ptr_transfer_internal :
  WpMethodCall bank.pkg_name' "BankClerk'ptr" "transfer_internal" _ (pkg_defined bank.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

End names.
End bank.
