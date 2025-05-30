(* autogenerated by goose proofgen; do not modify *)
Require Export New.proof.grove_prelude.
Require Export New.generatedproof.github_com.mit_pdos.gokv.grove_ffi.
Require Export New.generatedproof.github_com.mit_pdos.gokv.vrsm.apps.exactlyonce.
Require Export New.generatedproof.sync.
Require Export New.generatedproof.github_com.mit_pdos.gokv.kv.
Require Export New.generatedproof.github_com.mit_pdos.gokv.map_string_marshal.
Require Export New.generatedproof.github_com.mit_pdos.gokv.vrsm.storage.
Require Export New.generatedproof.github_com.tchajed.marshal.
Require Export New.golang.theory.

Require Export New.code.github_com.mit_pdos.gokv.vrsm.apps.vkv.

Set Default Proof Using "Type".

Module vkv.

(* type vkv.Clerk *)
Module Clerk.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  cl' : loc;
}.
End def.
End Clerk.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_Clerk : Settable Clerk.t :=
  settable! Clerk.mk < Clerk.cl' >.
Global Instance into_val_Clerk : IntoVal Clerk.t :=
  {| to_val_def v :=
    struct.val_aux vkv.Clerk [
    "cl" ::= #(Clerk.cl' v)
    ]%struct
  |}.

Global Program Instance into_val_typed_Clerk : IntoValTyped Clerk.t vkv.Clerk :=
{|
  default_val := Clerk.mk (default_val _);
|}.
Next Obligation. solve_to_val_type. Qed.
Next Obligation. solve_zero_val. Qed.
Next Obligation. solve_to_val_inj. Qed.
Final Obligation. solve_decision. Qed.

Global Instance into_val_struct_field_Clerk_cl : IntoValStructField "cl" vkv.Clerk Clerk.cl'.
Proof. solve_into_val_struct_field. Qed.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_Clerk cl':
  PureWp True
    (struct.make #vkv.Clerk (alist_val [
      "cl" ::= #cl'
    ]))%struct
    #(Clerk.mk cl').
Proof. solve_struct_make_pure_wp. Qed.


Global Instance Clerk_struct_fields_split dq l (v : Clerk.t) :
  StructFieldsSplit dq l v (
    "Hcl" ∷ l ↦s[vkv.Clerk :: "cl"]{dq} v.(Clerk.cl')
  ).
Proof.
  rewrite /named.
  apply struct_fields_split_intro.
  unfold_typed_pointsto; split_pointsto_app.

  rewrite -!/(typed_pointsto_def _ _ _) -!typed_pointsto_unseal.

  solve_field_ref_f.
Qed.

End instances.

(* type vkv.ClerkPool *)
Module ClerkPool.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  mu' : loc;
  cls' : slice.t;
  confHosts' : slice.t;
}.
End def.
End ClerkPool.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_ClerkPool : Settable ClerkPool.t :=
  settable! ClerkPool.mk < ClerkPool.mu'; ClerkPool.cls'; ClerkPool.confHosts' >.
Global Instance into_val_ClerkPool : IntoVal ClerkPool.t :=
  {| to_val_def v :=
    struct.val_aux vkv.ClerkPool [
    "mu" ::= #(ClerkPool.mu' v);
    "cls" ::= #(ClerkPool.cls' v);
    "confHosts" ::= #(ClerkPool.confHosts' v)
    ]%struct
  |}.

Global Program Instance into_val_typed_ClerkPool : IntoValTyped ClerkPool.t vkv.ClerkPool :=
{|
  default_val := ClerkPool.mk (default_val _) (default_val _) (default_val _);
|}.
Next Obligation. solve_to_val_type. Qed.
Next Obligation. solve_zero_val. Qed.
Next Obligation. solve_to_val_inj. Qed.
Final Obligation. solve_decision. Qed.

Global Instance into_val_struct_field_ClerkPool_mu : IntoValStructField "mu" vkv.ClerkPool ClerkPool.mu'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_ClerkPool_cls : IntoValStructField "cls" vkv.ClerkPool ClerkPool.cls'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_ClerkPool_confHosts : IntoValStructField "confHosts" vkv.ClerkPool ClerkPool.confHosts'.
Proof. solve_into_val_struct_field. Qed.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_ClerkPool mu' cls' confHosts':
  PureWp True
    (struct.make #vkv.ClerkPool (alist_val [
      "mu" ::= #mu';
      "cls" ::= #cls';
      "confHosts" ::= #confHosts'
    ]))%struct
    #(ClerkPool.mk mu' cls' confHosts').
Proof. solve_struct_make_pure_wp. Qed.


Global Instance ClerkPool_struct_fields_split dq l (v : ClerkPool.t) :
  StructFieldsSplit dq l v (
    "Hmu" ∷ l ↦s[vkv.ClerkPool :: "mu"]{dq} v.(ClerkPool.mu') ∗
    "Hcls" ∷ l ↦s[vkv.ClerkPool :: "cls"]{dq} v.(ClerkPool.cls') ∗
    "HconfHosts" ∷ l ↦s[vkv.ClerkPool :: "confHosts"]{dq} v.(ClerkPool.confHosts')
  ).
Proof.
  rewrite /named.
  apply struct_fields_split_intro.
  unfold_typed_pointsto; split_pointsto_app.

  rewrite -!/(typed_pointsto_def _ _ _) -!typed_pointsto_unseal.
  simpl_one_flatten_struct (# (ClerkPool.mu' v)) vkv.ClerkPool "mu"%go.
  simpl_one_flatten_struct (# (ClerkPool.cls' v)) vkv.ClerkPool "cls"%go.

  solve_field_ref_f.
Qed.

End instances.

(* type vkv.KVState *)
Module KVState.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  kvs' : loc;
  vnums' : loc;
  minVnum' : w64;
}.
End def.
End KVState.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_KVState : Settable KVState.t :=
  settable! KVState.mk < KVState.kvs'; KVState.vnums'; KVState.minVnum' >.
Global Instance into_val_KVState : IntoVal KVState.t :=
  {| to_val_def v :=
    struct.val_aux vkv.KVState [
    "kvs" ::= #(KVState.kvs' v);
    "vnums" ::= #(KVState.vnums' v);
    "minVnum" ::= #(KVState.minVnum' v)
    ]%struct
  |}.

Global Program Instance into_val_typed_KVState : IntoValTyped KVState.t vkv.KVState :=
{|
  default_val := KVState.mk (default_val _) (default_val _) (default_val _);
|}.
Next Obligation. solve_to_val_type. Qed.
Next Obligation. solve_zero_val. Qed.
Next Obligation. solve_to_val_inj. Qed.
Final Obligation. solve_decision. Qed.

Global Instance into_val_struct_field_KVState_kvs : IntoValStructField "kvs" vkv.KVState KVState.kvs'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_KVState_vnums : IntoValStructField "vnums" vkv.KVState KVState.vnums'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_KVState_minVnum : IntoValStructField "minVnum" vkv.KVState KVState.minVnum'.
Proof. solve_into_val_struct_field. Qed.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_KVState kvs' vnums' minVnum':
  PureWp True
    (struct.make #vkv.KVState (alist_val [
      "kvs" ::= #kvs';
      "vnums" ::= #vnums';
      "minVnum" ::= #minVnum'
    ]))%struct
    #(KVState.mk kvs' vnums' minVnum').
Proof. solve_struct_make_pure_wp. Qed.


Global Instance KVState_struct_fields_split dq l (v : KVState.t) :
  StructFieldsSplit dq l v (
    "Hkvs" ∷ l ↦s[vkv.KVState :: "kvs"]{dq} v.(KVState.kvs') ∗
    "Hvnums" ∷ l ↦s[vkv.KVState :: "vnums"]{dq} v.(KVState.vnums') ∗
    "HminVnum" ∷ l ↦s[vkv.KVState :: "minVnum"]{dq} v.(KVState.minVnum')
  ).
Proof.
  rewrite /named.
  apply struct_fields_split_intro.
  unfold_typed_pointsto; split_pointsto_app.

  rewrite -!/(typed_pointsto_def _ _ _) -!typed_pointsto_unseal.
  simpl_one_flatten_struct (# (KVState.kvs' v)) vkv.KVState "kvs"%go.
  simpl_one_flatten_struct (# (KVState.vnums' v)) vkv.KVState "vnums"%go.

  solve_field_ref_f.
Qed.

End instances.

(* type vkv.PutArgs *)
Module PutArgs.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Key' : go_string;
  Val' : go_string;
}.
End def.
End PutArgs.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_PutArgs : Settable PutArgs.t :=
  settable! PutArgs.mk < PutArgs.Key'; PutArgs.Val' >.
Global Instance into_val_PutArgs : IntoVal PutArgs.t :=
  {| to_val_def v :=
    struct.val_aux vkv.PutArgs [
    "Key" ::= #(PutArgs.Key' v);
    "Val" ::= #(PutArgs.Val' v)
    ]%struct
  |}.

Global Program Instance into_val_typed_PutArgs : IntoValTyped PutArgs.t vkv.PutArgs :=
{|
  default_val := PutArgs.mk (default_val _) (default_val _);
|}.
Next Obligation. solve_to_val_type. Qed.
Next Obligation. solve_zero_val. Qed.
Next Obligation. solve_to_val_inj. Qed.
Final Obligation. solve_decision. Qed.

Global Instance into_val_struct_field_PutArgs_Key : IntoValStructField "Key" vkv.PutArgs PutArgs.Key'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_PutArgs_Val : IntoValStructField "Val" vkv.PutArgs PutArgs.Val'.
Proof. solve_into_val_struct_field. Qed.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_PutArgs Key' Val':
  PureWp True
    (struct.make #vkv.PutArgs (alist_val [
      "Key" ::= #Key';
      "Val" ::= #Val'
    ]))%struct
    #(PutArgs.mk Key' Val').
Proof. solve_struct_make_pure_wp. Qed.


Global Instance PutArgs_struct_fields_split dq l (v : PutArgs.t) :
  StructFieldsSplit dq l v (
    "HKey" ∷ l ↦s[vkv.PutArgs :: "Key"]{dq} v.(PutArgs.Key') ∗
    "HVal" ∷ l ↦s[vkv.PutArgs :: "Val"]{dq} v.(PutArgs.Val')
  ).
Proof.
  rewrite /named.
  apply struct_fields_split_intro.
  unfold_typed_pointsto; split_pointsto_app.

  rewrite -!/(typed_pointsto_def _ _ _) -!typed_pointsto_unseal.
  simpl_one_flatten_struct (# (PutArgs.Key' v)) vkv.PutArgs "Key"%go.

  solve_field_ref_f.
Qed.

End instances.

(* type vkv.getArgs *)
Module getArgs.
Section def.
Context `{ffi_syntax}.
Definition t := go_string.
End def.
End getArgs.

(* type vkv.CondPutArgs *)
Module CondPutArgs.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Key' : go_string;
  Expect' : go_string;
  Val' : go_string;
}.
End def.
End CondPutArgs.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_CondPutArgs : Settable CondPutArgs.t :=
  settable! CondPutArgs.mk < CondPutArgs.Key'; CondPutArgs.Expect'; CondPutArgs.Val' >.
Global Instance into_val_CondPutArgs : IntoVal CondPutArgs.t :=
  {| to_val_def v :=
    struct.val_aux vkv.CondPutArgs [
    "Key" ::= #(CondPutArgs.Key' v);
    "Expect" ::= #(CondPutArgs.Expect' v);
    "Val" ::= #(CondPutArgs.Val' v)
    ]%struct
  |}.

Global Program Instance into_val_typed_CondPutArgs : IntoValTyped CondPutArgs.t vkv.CondPutArgs :=
{|
  default_val := CondPutArgs.mk (default_val _) (default_val _) (default_val _);
|}.
Next Obligation. solve_to_val_type. Qed.
Next Obligation. solve_zero_val. Qed.
Next Obligation. solve_to_val_inj. Qed.
Final Obligation. solve_decision. Qed.

Global Instance into_val_struct_field_CondPutArgs_Key : IntoValStructField "Key" vkv.CondPutArgs CondPutArgs.Key'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_CondPutArgs_Expect : IntoValStructField "Expect" vkv.CondPutArgs CondPutArgs.Expect'.
Proof. solve_into_val_struct_field. Qed.

Global Instance into_val_struct_field_CondPutArgs_Val : IntoValStructField "Val" vkv.CondPutArgs CondPutArgs.Val'.
Proof. solve_into_val_struct_field. Qed.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_CondPutArgs Key' Expect' Val':
  PureWp True
    (struct.make #vkv.CondPutArgs (alist_val [
      "Key" ::= #Key';
      "Expect" ::= #Expect';
      "Val" ::= #Val'
    ]))%struct
    #(CondPutArgs.mk Key' Expect' Val').
Proof. solve_struct_make_pure_wp. Qed.


Global Instance CondPutArgs_struct_fields_split dq l (v : CondPutArgs.t) :
  StructFieldsSplit dq l v (
    "HKey" ∷ l ↦s[vkv.CondPutArgs :: "Key"]{dq} v.(CondPutArgs.Key') ∗
    "HExpect" ∷ l ↦s[vkv.CondPutArgs :: "Expect"]{dq} v.(CondPutArgs.Expect') ∗
    "HVal" ∷ l ↦s[vkv.CondPutArgs :: "Val"]{dq} v.(CondPutArgs.Val')
  ).
Proof.
  rewrite /named.
  apply struct_fields_split_intro.
  unfold_typed_pointsto; split_pointsto_app.

  rewrite -!/(typed_pointsto_def _ _ _) -!typed_pointsto_unseal.
  simpl_one_flatten_struct (# (CondPutArgs.Key' v)) vkv.CondPutArgs "Key"%go.
  simpl_one_flatten_struct (# (CondPutArgs.Expect' v)) vkv.CondPutArgs "Expect"%go.

  solve_field_ref_f.
Qed.

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

Global Instance is_pkg_defined_instance : IsPkgDefined vkv :=
{|
  is_pkg_defined := is_global_definitions vkv var_addrs;
|}.

Definition own_allocated : iProp Σ :=
True.

Global Instance wp_func_call_MakeClerk :
  WpFuncCall vkv "MakeClerk" _ (is_pkg_defined vkv) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_MakeClerkPool :
  WpFuncCall vkv "MakeClerkPool" _ (is_pkg_defined vkv) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_MakeKv :
  WpFuncCall vkv "MakeKv" _ (is_pkg_defined vkv) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_encodePutArgs :
  WpFuncCall vkv "encodePutArgs" _ (is_pkg_defined vkv) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_decodePutArgs :
  WpFuncCall vkv "decodePutArgs" _ (is_pkg_defined vkv) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_encodeGetArgs :
  WpFuncCall vkv "encodeGetArgs" _ (is_pkg_defined vkv) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_decodeGetArgs :
  WpFuncCall vkv "decodeGetArgs" _ (is_pkg_defined vkv) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_encodeCondPutArgs :
  WpFuncCall vkv "encodeCondPutArgs" _ (is_pkg_defined vkv) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_decodeCondPutArgs :
  WpFuncCall vkv "decodeCondPutArgs" _ (is_pkg_defined vkv) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_makeVersionedStateMachine :
  WpFuncCall vkv "makeVersionedStateMachine" _ (is_pkg_defined vkv) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Start :
  WpFuncCall vkv "Start" _ (is_pkg_defined vkv) :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_method_call_Clerk'ptr_CondPut :
  WpMethodCall vkv "Clerk'ptr" "CondPut" _ (is_pkg_defined vkv) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Clerk'ptr_Get :
  WpMethodCall vkv "Clerk'ptr" "Get" _ (is_pkg_defined vkv) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Clerk'ptr_Put :
  WpMethodCall vkv "Clerk'ptr" "Put" _ (is_pkg_defined vkv) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ClerkPool'ptr_ConditionalPut :
  WpMethodCall vkv "ClerkPool'ptr" "ConditionalPut" _ (is_pkg_defined vkv) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ClerkPool'ptr_Get :
  WpMethodCall vkv "ClerkPool'ptr" "Get" _ (is_pkg_defined vkv) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ClerkPool'ptr_Put :
  WpMethodCall vkv "ClerkPool'ptr" "Put" _ (is_pkg_defined vkv) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ClerkPool'ptr_doWithClerk :
  WpMethodCall vkv "ClerkPool'ptr" "doWithClerk" _ (is_pkg_defined vkv) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_KVState'ptr_apply :
  WpMethodCall vkv "KVState'ptr" "apply" _ (is_pkg_defined vkv) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_KVState'ptr_applyReadonly :
  WpMethodCall vkv "KVState'ptr" "applyReadonly" _ (is_pkg_defined vkv) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_KVState'ptr_get :
  WpMethodCall vkv "KVState'ptr" "get" _ (is_pkg_defined vkv) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_KVState'ptr_getState :
  WpMethodCall vkv "KVState'ptr" "getState" _ (is_pkg_defined vkv) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_KVState'ptr_put :
  WpMethodCall vkv "KVState'ptr" "put" _ (is_pkg_defined vkv) :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_KVState'ptr_setState :
  WpMethodCall vkv "KVState'ptr" "setState" _ (is_pkg_defined vkv) :=
  ltac:(apply wp_method_call'; reflexivity).

End names.
End vkv.
