(* autogenerated by goose proofgen (types); do not modify *)
Require Export New.proof.proof_prelude.
Require Export New.generatedproof.fmt.
Require Export New.generatedproof.math.
Require Export New.generatedproof.go_etcd_io.raft.v3.quorum.slices64.
Require Export New.generatedproof.sort.
Require Export New.generatedproof.strings.
Require Export New.generatedproof.strconv.
Require Export New.code.go_etcd_io.raft.v3.quorum.
Require Export New.golang.theory.

Module quorum.
Axiom falso : False.

Module MajorityConfig.
Section def.
Context `{ffi_syntax}.
Definition t := loc.
End def.
End MajorityConfig.

Module JointConfig.
Section def.
Context `{ffi_syntax}.
Definition t := (vec MajorityConfig.t 2).
End def.
End JointConfig.
Module unit.
Section def.
Context `{ffi_syntax}.
Record t := mk {
}.
End def.
End unit.

Section instances.
Context `{ffi_syntax}.
Global Instance into_val_unit `{ffi_syntax} : IntoVal unit.t.
Admitted.

Global Instance into_val_typed_unit `{ffi_syntax} : IntoValTyped unit.t quorum.unit :=
{|
  default_val := unit.mk;
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.

Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_unit `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}:
  PureWp True
    (struct.make quorum.unit (alist_val [
    ]))%V
    #(unit.mk).
Admitted.


End instances.

Module Index.
Section def.
Context `{ffi_syntax}.
Definition t := w64.
End def.
End Index.
Module tup.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  id' : w64;
  idx' : Index.t;
  ok' : bool;
  bar' : w64;
}.
End def.
End tup.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_tup `{ffi_syntax}: Settable _ :=
  settable! tup.mk < tup.id'; tup.idx'; tup.ok'; tup.bar' >.
Global Instance into_val_tup `{ffi_syntax} : IntoVal tup.t.
Admitted.

Global Instance into_val_typed_tup `{ffi_syntax} : IntoValTyped tup.t quorum.tup :=
{|
  default_val := tup.mk (default_val _) (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_tup_id `{ffi_syntax} : IntoValStructField "id" quorum.tup tup.id'.
Admitted.

Global Instance into_val_struct_field_tup_idx `{ffi_syntax} : IntoValStructField "idx" quorum.tup tup.idx'.
Admitted.

Global Instance into_val_struct_field_tup_ok `{ffi_syntax} : IntoValStructField "ok" quorum.tup tup.ok'.
Admitted.

Global Instance into_val_struct_field_tup_bar `{ffi_syntax} : IntoValStructField "bar" quorum.tup tup.bar'.
Admitted.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_tup `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} id' idx' ok' bar':
  PureWp True
    (struct.make quorum.tup (alist_val [
      "id" ::= #id';
      "idx" ::= #idx';
      "ok" ::= #ok';
      "bar" ::= #bar'
    ]))%V
    #(tup.mk id' idx' ok' bar').
Admitted.


Global Instance tup_struct_fields_split dq l (v : tup.t) :
  StructFieldsSplit dq l v (
    "Hid" ∷ l ↦s[quorum.tup :: "id"]{dq} v.(tup.id') ∗
    "Hidx" ∷ l ↦s[quorum.tup :: "idx"]{dq} v.(tup.idx') ∗
    "Hok" ∷ l ↦s[quorum.tup :: "ok"]{dq} v.(tup.ok') ∗
    "Hbar" ∷ l ↦s[quorum.tup :: "bar"]{dq} v.(tup.bar')
  ).
Admitted.

End instances.

Module AckedIndexer.
Section def.
Context `{ffi_syntax}.
Definition t := interface.t.
End def.
End AckedIndexer.

Module mapAckIndexer.
Section def.
Context `{ffi_syntax}.
Definition t := loc.
End def.
End mapAckIndexer.

Module VoteResult.
Section def.
Context `{ffi_syntax}.
Definition t := w8.
End def.
End VoteResult.

Section names.

Class GlobalAddrs :=
{
  _VoteResult_index : loc;
}.

Context `{!GlobalAddrs}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
    ("_VoteResult_index"%go, _VoteResult_index)
  ].

Definition is_defined := is_global_definitions quorum.pkg_name' var_addrs quorum.functions' quorum.msets'.

Global Instance is_pkg_defined : PkgIsDefined quorum.pkg_name' is_defined :=
  ltac:(prove_pkg_is_defined).

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
  "H_VoteResult_index" ∷ _VoteResult_index ↦ (default_val (vec w8 4)).

Global Instance wp_globals_get__VoteResult_index : 
  WpGlobalsGet quorum.pkg_name' "_VoteResult_index" _VoteResult_index is_defined.
Proof. apply wp_globals_get'. reflexivity. Qed.

Global Instance wp_func_call__unused :
  WpFuncCall quorum.pkg_name' "_unused" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_method_call_JointConfig_CommittedIndex :
  WpMethodCall quorum.pkg_name' "JointConfig" "CommittedIndex" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_JointConfig_Describe :
  WpMethodCall quorum.pkg_name' "JointConfig" "Describe" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_JointConfig_IDs :
  WpMethodCall quorum.pkg_name' "JointConfig" "IDs" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_JointConfig_String :
  WpMethodCall quorum.pkg_name' "JointConfig" "String" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_JointConfig_VoteResult :
  WpMethodCall quorum.pkg_name' "JointConfig" "VoteResult" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_JointConfig'ptr_CommittedIndex :
  WpMethodCall quorum.pkg_name' "JointConfig'ptr" "CommittedIndex" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_JointConfig'ptr_Describe :
  WpMethodCall quorum.pkg_name' "JointConfig'ptr" "Describe" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_JointConfig'ptr_IDs :
  WpMethodCall quorum.pkg_name' "JointConfig'ptr" "IDs" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_JointConfig'ptr_String :
  WpMethodCall quorum.pkg_name' "JointConfig'ptr" "String" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_JointConfig'ptr_VoteResult :
  WpMethodCall quorum.pkg_name' "JointConfig'ptr" "VoteResult" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MajorityConfig_CommittedIndex :
  WpMethodCall quorum.pkg_name' "MajorityConfig" "CommittedIndex" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MajorityConfig_Describe :
  WpMethodCall quorum.pkg_name' "MajorityConfig" "Describe" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MajorityConfig_Slice :
  WpMethodCall quorum.pkg_name' "MajorityConfig" "Slice" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MajorityConfig_String :
  WpMethodCall quorum.pkg_name' "MajorityConfig" "String" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MajorityConfig_VoteResult :
  WpMethodCall quorum.pkg_name' "MajorityConfig" "VoteResult" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MajorityConfig'ptr_CommittedIndex :
  WpMethodCall quorum.pkg_name' "MajorityConfig'ptr" "CommittedIndex" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MajorityConfig'ptr_Describe :
  WpMethodCall quorum.pkg_name' "MajorityConfig'ptr" "Describe" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MajorityConfig'ptr_Slice :
  WpMethodCall quorum.pkg_name' "MajorityConfig'ptr" "Slice" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MajorityConfig'ptr_String :
  WpMethodCall quorum.pkg_name' "MajorityConfig'ptr" "String" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MajorityConfig'ptr_VoteResult :
  WpMethodCall quorum.pkg_name' "MajorityConfig'ptr" "VoteResult" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Index_String :
  WpMethodCall quorum.pkg_name' "Index" "String" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Index'ptr_String :
  WpMethodCall quorum.pkg_name' "Index'ptr" "String" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_mapAckIndexer_AckedIndex :
  WpMethodCall quorum.pkg_name' "mapAckIndexer" "AckedIndex" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_mapAckIndexer'ptr_AckedIndex :
  WpMethodCall quorum.pkg_name' "mapAckIndexer'ptr" "AckedIndex" _ (pkg_defined quorum.pkg_name') :=
  ltac:(apply wp_method_call'; reflexivity).

End names.
End quorum.
