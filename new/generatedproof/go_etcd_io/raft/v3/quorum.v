(* autogenerated by goose proofgen (types); do not modify *)
From New.code Require Import go_etcd_io.raft.v3.quorum.
From New.golang Require Import theory.

Require New.generatedproof.fmt.
Require New.generatedproof.math.
Require New.generatedproof.sort.
Require New.generatedproof.strings.
Require New.generatedproof.go_etcd_io.raft.v3.quorum.slices64.
Require New.generatedproof.strconv.
Axiom falso : False.

Module JointConfig.
Section def.
Context `{ffi_syntax}.
Definition t := (vec loc 2).
End def.
End JointConfig.
Module MajorityConfig.
Section def.
Context `{ffi_syntax}.
Definition t := loc.
End def.
End MajorityConfig.
Module tup.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  id' : w64;
  idx' : w64;
  ok' : bool;
  bar' : w64;
}.
End def.
End tup.


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

Instance wp_struct_make_tup `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} id' idx' ok' bar':
  PureWp True
    (struct.make quorum.tup (alist_val [
      "id" ::= #id';
      "idx" ::= #idx';
      "ok" ::= #ok';
      "bar" ::= #bar'
    ]))%V
    #(tup.mk id' idx' ok' bar').
Admitted.

Module Index.
Section def.
Context `{ffi_syntax}.
Definition t := w64.
End def.
End Index.
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
(* autogenerated by proofgen (names); do not modify *)
Require Import New.code.go_etcd_io.raft.v3.quorum.
Require Export New.proof.proof_prelude.
Module quorum.
Section defs.
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

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
  "H_VoteResult_index" ∷ _VoteResult_index ↦ (default_val (vec w8 4)).

Global Instance wp_globals_get__VoteResult_index : 
  WpGlobalsGet quorum.pkg_name' "_VoteResult_index" _VoteResult_index is_defined.
Proof. apply wp_globals_get'. reflexivity. Qed.

Global Instance wp_method_call_JointConfig_CommittedIndex : 
  WpMethodCall quorum.pkg_name' "JointConfig" "CommittedIndex" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_JointConfig_Describe : 
  WpMethodCall quorum.pkg_name' "JointConfig" "Describe" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_JointConfig_IDs : 
  WpMethodCall quorum.pkg_name' "JointConfig" "IDs" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_JointConfig_String : 
  WpMethodCall quorum.pkg_name' "JointConfig" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_JointConfig_VoteResult : 
  WpMethodCall quorum.pkg_name' "JointConfig" "VoteResult" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_JointConfig'ptr_CommittedIndex : 
  WpMethodCall quorum.pkg_name' "JointConfig'ptr" "CommittedIndex" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_JointConfig'ptr_Describe : 
  WpMethodCall quorum.pkg_name' "JointConfig'ptr" "Describe" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_JointConfig'ptr_IDs : 
  WpMethodCall quorum.pkg_name' "JointConfig'ptr" "IDs" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_JointConfig'ptr_String : 
  WpMethodCall quorum.pkg_name' "JointConfig'ptr" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_JointConfig'ptr_VoteResult : 
  WpMethodCall quorum.pkg_name' "JointConfig'ptr" "VoteResult" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MajorityConfig_CommittedIndex : 
  WpMethodCall quorum.pkg_name' "MajorityConfig" "CommittedIndex" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MajorityConfig_Describe : 
  WpMethodCall quorum.pkg_name' "MajorityConfig" "Describe" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MajorityConfig_Slice : 
  WpMethodCall quorum.pkg_name' "MajorityConfig" "Slice" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MajorityConfig_String : 
  WpMethodCall quorum.pkg_name' "MajorityConfig" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MajorityConfig_VoteResult : 
  WpMethodCall quorum.pkg_name' "MajorityConfig" "VoteResult" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MajorityConfig'ptr_CommittedIndex : 
  WpMethodCall quorum.pkg_name' "MajorityConfig'ptr" "CommittedIndex" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MajorityConfig'ptr_Describe : 
  WpMethodCall quorum.pkg_name' "MajorityConfig'ptr" "Describe" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MajorityConfig'ptr_Slice : 
  WpMethodCall quorum.pkg_name' "MajorityConfig'ptr" "Slice" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MajorityConfig'ptr_String : 
  WpMethodCall quorum.pkg_name' "MajorityConfig'ptr" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MajorityConfig'ptr_VoteResult : 
  WpMethodCall quorum.pkg_name' "MajorityConfig'ptr" "VoteResult" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Index_String : 
  WpMethodCall quorum.pkg_name' "Index" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Index'ptr_String : 
  WpMethodCall quorum.pkg_name' "Index'ptr" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_mapAckIndexer_AckedIndex : 
  WpMethodCall quorum.pkg_name' "mapAckIndexer" "AckedIndex" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_mapAckIndexer'ptr_AckedIndex : 
  WpMethodCall quorum.pkg_name' "mapAckIndexer'ptr" "AckedIndex" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_VoteResult_String : 
  WpMethodCall quorum.pkg_name' "VoteResult" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_VoteResult'ptr_String : 
  WpMethodCall quorum.pkg_name' "VoteResult'ptr" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

End defs.
End quorum.
