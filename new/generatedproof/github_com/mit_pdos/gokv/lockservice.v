(* autogenerated by goose proofgen (types); do not modify *)
Require Export New.proof.proof_prelude.
Require Export New.generatedproof.github_com.mit_pdos.gokv.kv.
Require Export New.code.github_com.mit_pdos.gokv.lockservice.
Require Export New.golang.theory.

Module lockservice.
Axiom falso : False.
Module LockClerk.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  kv' : kv.KvCput.t;
}.
End def.
End LockClerk.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_LockClerk `{ffi_syntax}: Settable _ :=
  settable! LockClerk.mk < LockClerk.kv' >.
Global Instance into_val_LockClerk `{ffi_syntax} : IntoVal LockClerk.t.
Admitted.

Global Instance into_val_typed_LockClerk `{ffi_syntax} : IntoValTyped LockClerk.t lockservice.LockClerk :=
{|
  default_val := LockClerk.mk (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_LockClerk_kv `{ffi_syntax} : IntoValStructField "kv" lockservice.LockClerk LockClerk.kv'.
Admitted.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_LockClerk `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} kv':
  PureWp True
    (struct.make lockservice.LockClerk (alist_val [
      "kv" ::= #kv'
    ]))%V
    #(LockClerk.mk kv').
Admitted.


Global Instance LockClerk_struct_fields_split dq l (v : LockClerk.t) :
  StructFieldsSplit dq l v (
    "Hkv" ∷ l ↦s[lockservice.LockClerk :: "kv"]{dq} v.(LockClerk.kv')
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

Definition is_defined := is_global_definitions lockservice.pkg_name' var_addrs lockservice.functions' lockservice.msets'.

Global Instance : PkgIsDefined lockservice.pkg_name' is_defined :=
  ltac:(prove_pkg_is_defined).

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

Global Instance wp_func_call_MakeLockClerk :
  WpFuncCall lockservice.pkg_name' "MakeLockClerk" _ (is_pkg_defined lockservice.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_method_call_LockClerk'ptr_Lock :
  WpMethodCall lockservice.pkg_name' "LockClerk'ptr" "Lock" _ (is_pkg_defined lockservice.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_LockClerk'ptr_Unlock :
  WpMethodCall lockservice.pkg_name' "LockClerk'ptr" "Unlock" _ (is_pkg_defined lockservice.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

End names.
End lockservice.
