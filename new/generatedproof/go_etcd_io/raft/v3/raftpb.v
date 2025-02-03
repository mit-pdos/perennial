(* autogenerated by goose proofgen (types); do not modify *)
From New.code Require Import go_etcd_io.raft.v3.raftpb.
From New.golang Require Import theory.

Axiom falso : False.

Module Entry.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Term' : w64;
  Index' : w64;
  Type' : w32;
  Data' : slice.t;
}.
End def.
End Entry.


Global Instance settable_Entry `{ffi_syntax}: Settable _ :=
  settable! Entry.mk < Entry.Term'; Entry.Index'; Entry.Type'; Entry.Data' >.
Global Instance into_val_Entry `{ffi_syntax} : IntoVal Entry.t.
Admitted.

Global Instance into_val_typed_Entry `{ffi_syntax} : IntoValTyped Entry.t raftpb.Entry :=
{|
  default_val := Entry.mk (default_val _) (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_Entry_Term `{ffi_syntax} : IntoValStructField "Term" raftpb.Entry Entry.Term'.
Admitted.

Global Instance into_val_struct_field_Entry_Index `{ffi_syntax} : IntoValStructField "Index" raftpb.Entry Entry.Index'.
Admitted.

Global Instance into_val_struct_field_Entry_Type `{ffi_syntax} : IntoValStructField "Type" raftpb.Entry Entry.Type'.
Admitted.

Global Instance into_val_struct_field_Entry_Data `{ffi_syntax} : IntoValStructField "Data" raftpb.Entry Entry.Data'.
Admitted.

Instance wp_struct_make_Entry `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} Term' Index' Type' Data':
  PureWp True
    (struct.make raftpb.Entry (alist_val [
      "Term" ::= #Term';
      "Index" ::= #Index';
      "Type" ::= #Type';
      "Data" ::= #Data'
    ]))%V
    #(Entry.mk Term' Index' Type' Data').
Admitted.

Module ConfState.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Voters' : slice.t;
  Learners' : slice.t;
  VotersOutgoing' : slice.t;
  LearnersNext' : slice.t;
  AutoLeave' : bool;
}.
End def.
End ConfState.


Global Instance settable_ConfState `{ffi_syntax}: Settable _ :=
  settable! ConfState.mk < ConfState.Voters'; ConfState.Learners'; ConfState.VotersOutgoing'; ConfState.LearnersNext'; ConfState.AutoLeave' >.
Global Instance into_val_ConfState `{ffi_syntax} : IntoVal ConfState.t.
Admitted.

Global Instance into_val_typed_ConfState `{ffi_syntax} : IntoValTyped ConfState.t raftpb.ConfState :=
{|
  default_val := ConfState.mk (default_val _) (default_val _) (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_ConfState_Voters `{ffi_syntax} : IntoValStructField "Voters" raftpb.ConfState ConfState.Voters'.
Admitted.

Global Instance into_val_struct_field_ConfState_Learners `{ffi_syntax} : IntoValStructField "Learners" raftpb.ConfState ConfState.Learners'.
Admitted.

Global Instance into_val_struct_field_ConfState_VotersOutgoing `{ffi_syntax} : IntoValStructField "VotersOutgoing" raftpb.ConfState ConfState.VotersOutgoing'.
Admitted.

Global Instance into_val_struct_field_ConfState_LearnersNext `{ffi_syntax} : IntoValStructField "LearnersNext" raftpb.ConfState ConfState.LearnersNext'.
Admitted.

Global Instance into_val_struct_field_ConfState_AutoLeave `{ffi_syntax} : IntoValStructField "AutoLeave" raftpb.ConfState ConfState.AutoLeave'.
Admitted.

Instance wp_struct_make_ConfState `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} Voters' Learners' VotersOutgoing' LearnersNext' AutoLeave':
  PureWp True
    (struct.make raftpb.ConfState (alist_val [
      "Voters" ::= #Voters';
      "Learners" ::= #Learners';
      "VotersOutgoing" ::= #VotersOutgoing';
      "LearnersNext" ::= #LearnersNext';
      "AutoLeave" ::= #AutoLeave'
    ]))%V
    #(ConfState.mk Voters' Learners' VotersOutgoing' LearnersNext' AutoLeave').
Admitted.

Module SnapshotMetadata.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  ConfState' : ConfState.t;
  Index' : w64;
  Term' : w64;
}.
End def.
End SnapshotMetadata.


Global Instance settable_SnapshotMetadata `{ffi_syntax}: Settable _ :=
  settable! SnapshotMetadata.mk < SnapshotMetadata.ConfState'; SnapshotMetadata.Index'; SnapshotMetadata.Term' >.
Global Instance into_val_SnapshotMetadata `{ffi_syntax} : IntoVal SnapshotMetadata.t.
Admitted.

Global Instance into_val_typed_SnapshotMetadata `{ffi_syntax} : IntoValTyped SnapshotMetadata.t raftpb.SnapshotMetadata :=
{|
  default_val := SnapshotMetadata.mk (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_SnapshotMetadata_ConfState `{ffi_syntax} : IntoValStructField "ConfState" raftpb.SnapshotMetadata SnapshotMetadata.ConfState'.
Admitted.

Global Instance into_val_struct_field_SnapshotMetadata_Index `{ffi_syntax} : IntoValStructField "Index" raftpb.SnapshotMetadata SnapshotMetadata.Index'.
Admitted.

Global Instance into_val_struct_field_SnapshotMetadata_Term `{ffi_syntax} : IntoValStructField "Term" raftpb.SnapshotMetadata SnapshotMetadata.Term'.
Admitted.

Instance wp_struct_make_SnapshotMetadata `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} ConfState' Index' Term':
  PureWp True
    (struct.make raftpb.SnapshotMetadata (alist_val [
      "ConfState" ::= #ConfState';
      "Index" ::= #Index';
      "Term" ::= #Term'
    ]))%V
    #(SnapshotMetadata.mk ConfState' Index' Term').
Admitted.

Module Snapshot.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Data' : slice.t;
  Metadata' : SnapshotMetadata.t;
}.
End def.
End Snapshot.


Global Instance settable_Snapshot `{ffi_syntax}: Settable _ :=
  settable! Snapshot.mk < Snapshot.Data'; Snapshot.Metadata' >.
Global Instance into_val_Snapshot `{ffi_syntax} : IntoVal Snapshot.t.
Admitted.

Global Instance into_val_typed_Snapshot `{ffi_syntax} : IntoValTyped Snapshot.t raftpb.Snapshot :=
{|
  default_val := Snapshot.mk (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_Snapshot_Data `{ffi_syntax} : IntoValStructField "Data" raftpb.Snapshot Snapshot.Data'.
Admitted.

Global Instance into_val_struct_field_Snapshot_Metadata `{ffi_syntax} : IntoValStructField "Metadata" raftpb.Snapshot Snapshot.Metadata'.
Admitted.

Instance wp_struct_make_Snapshot `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} Data' Metadata':
  PureWp True
    (struct.make raftpb.Snapshot (alist_val [
      "Data" ::= #Data';
      "Metadata" ::= #Metadata'
    ]))%V
    #(Snapshot.mk Data' Metadata').
Admitted.

Module Message.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Type' : w32;
  To' : w64;
  From' : w64;
  Term' : w64;
  LogTerm' : w64;
  Index' : w64;
  Entries' : slice.t;
  Commit' : w64;
  Vote' : w64;
  Snapshot' : loc;
  Reject' : bool;
  RejectHint' : w64;
  Context' : slice.t;
  Responses' : slice.t;
}.
End def.
End Message.


Global Instance settable_Message `{ffi_syntax}: Settable _ :=
  settable! Message.mk < Message.Type'; Message.To'; Message.From'; Message.Term'; Message.LogTerm'; Message.Index'; Message.Entries'; Message.Commit'; Message.Vote'; Message.Snapshot'; Message.Reject'; Message.RejectHint'; Message.Context'; Message.Responses' >.
Global Instance into_val_Message `{ffi_syntax} : IntoVal Message.t.
Admitted.

Global Instance into_val_typed_Message `{ffi_syntax} : IntoValTyped Message.t raftpb.Message :=
{|
  default_val := Message.mk (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_Message_Type `{ffi_syntax} : IntoValStructField "Type" raftpb.Message Message.Type'.
Admitted.

Global Instance into_val_struct_field_Message_To `{ffi_syntax} : IntoValStructField "To" raftpb.Message Message.To'.
Admitted.

Global Instance into_val_struct_field_Message_From `{ffi_syntax} : IntoValStructField "From" raftpb.Message Message.From'.
Admitted.

Global Instance into_val_struct_field_Message_Term `{ffi_syntax} : IntoValStructField "Term" raftpb.Message Message.Term'.
Admitted.

Global Instance into_val_struct_field_Message_LogTerm `{ffi_syntax} : IntoValStructField "LogTerm" raftpb.Message Message.LogTerm'.
Admitted.

Global Instance into_val_struct_field_Message_Index `{ffi_syntax} : IntoValStructField "Index" raftpb.Message Message.Index'.
Admitted.

Global Instance into_val_struct_field_Message_Entries `{ffi_syntax} : IntoValStructField "Entries" raftpb.Message Message.Entries'.
Admitted.

Global Instance into_val_struct_field_Message_Commit `{ffi_syntax} : IntoValStructField "Commit" raftpb.Message Message.Commit'.
Admitted.

Global Instance into_val_struct_field_Message_Vote `{ffi_syntax} : IntoValStructField "Vote" raftpb.Message Message.Vote'.
Admitted.

Global Instance into_val_struct_field_Message_Snapshot `{ffi_syntax} : IntoValStructField "Snapshot" raftpb.Message Message.Snapshot'.
Admitted.

Global Instance into_val_struct_field_Message_Reject `{ffi_syntax} : IntoValStructField "Reject" raftpb.Message Message.Reject'.
Admitted.

Global Instance into_val_struct_field_Message_RejectHint `{ffi_syntax} : IntoValStructField "RejectHint" raftpb.Message Message.RejectHint'.
Admitted.

Global Instance into_val_struct_field_Message_Context `{ffi_syntax} : IntoValStructField "Context" raftpb.Message Message.Context'.
Admitted.

Global Instance into_val_struct_field_Message_Responses `{ffi_syntax} : IntoValStructField "Responses" raftpb.Message Message.Responses'.
Admitted.

Instance wp_struct_make_Message `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} Type' To' From' Term' LogTerm' Index' Entries' Commit' Vote' Snapshot' Reject' RejectHint' Context' Responses':
  PureWp True
    (struct.make raftpb.Message (alist_val [
      "Type" ::= #Type';
      "To" ::= #To';
      "From" ::= #From';
      "Term" ::= #Term';
      "LogTerm" ::= #LogTerm';
      "Index" ::= #Index';
      "Entries" ::= #Entries';
      "Commit" ::= #Commit';
      "Vote" ::= #Vote';
      "Snapshot" ::= #Snapshot';
      "Reject" ::= #Reject';
      "RejectHint" ::= #RejectHint';
      "Context" ::= #Context';
      "Responses" ::= #Responses'
    ]))%V
    #(Message.mk Type' To' From' Term' LogTerm' Index' Entries' Commit' Vote' Snapshot' Reject' RejectHint' Context' Responses').
Admitted.

Module HardState.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Term' : w64;
  Vote' : w64;
  Commit' : w64;
}.
End def.
End HardState.


Global Instance settable_HardState `{ffi_syntax}: Settable _ :=
  settable! HardState.mk < HardState.Term'; HardState.Vote'; HardState.Commit' >.
Global Instance into_val_HardState `{ffi_syntax} : IntoVal HardState.t.
Admitted.

Global Instance into_val_typed_HardState `{ffi_syntax} : IntoValTyped HardState.t raftpb.HardState :=
{|
  default_val := HardState.mk (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_HardState_Term `{ffi_syntax} : IntoValStructField "Term" raftpb.HardState HardState.Term'.
Admitted.

Global Instance into_val_struct_field_HardState_Vote `{ffi_syntax} : IntoValStructField "Vote" raftpb.HardState HardState.Vote'.
Admitted.

Global Instance into_val_struct_field_HardState_Commit `{ffi_syntax} : IntoValStructField "Commit" raftpb.HardState HardState.Commit'.
Admitted.

Instance wp_struct_make_HardState `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} Term' Vote' Commit':
  PureWp True
    (struct.make raftpb.HardState (alist_val [
      "Term" ::= #Term';
      "Vote" ::= #Vote';
      "Commit" ::= #Commit'
    ]))%V
    #(HardState.mk Term' Vote' Commit').
Admitted.

Module ConfChange.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Type' : w32;
  NodeID' : w64;
  Context' : slice.t;
  ID' : w64;
}.
End def.
End ConfChange.


Global Instance settable_ConfChange `{ffi_syntax}: Settable _ :=
  settable! ConfChange.mk < ConfChange.Type'; ConfChange.NodeID'; ConfChange.Context'; ConfChange.ID' >.
Global Instance into_val_ConfChange `{ffi_syntax} : IntoVal ConfChange.t.
Admitted.

Global Instance into_val_typed_ConfChange `{ffi_syntax} : IntoValTyped ConfChange.t raftpb.ConfChange :=
{|
  default_val := ConfChange.mk (default_val _) (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_ConfChange_Type `{ffi_syntax} : IntoValStructField "Type" raftpb.ConfChange ConfChange.Type'.
Admitted.

Global Instance into_val_struct_field_ConfChange_NodeID `{ffi_syntax} : IntoValStructField "NodeID" raftpb.ConfChange ConfChange.NodeID'.
Admitted.

Global Instance into_val_struct_field_ConfChange_Context `{ffi_syntax} : IntoValStructField "Context" raftpb.ConfChange ConfChange.Context'.
Admitted.

Global Instance into_val_struct_field_ConfChange_ID `{ffi_syntax} : IntoValStructField "ID" raftpb.ConfChange ConfChange.ID'.
Admitted.

Instance wp_struct_make_ConfChange `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} Type' NodeID' Context' ID':
  PureWp True
    (struct.make raftpb.ConfChange (alist_val [
      "Type" ::= #Type';
      "NodeID" ::= #NodeID';
      "Context" ::= #Context';
      "ID" ::= #ID'
    ]))%V
    #(ConfChange.mk Type' NodeID' Context' ID').
Admitted.

Module ConfChangeV2.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Transition' : w32;
  Changes' : slice.t;
  Context' : slice.t;
}.
End def.
End ConfChangeV2.


Global Instance settable_ConfChangeV2 `{ffi_syntax}: Settable _ :=
  settable! ConfChangeV2.mk < ConfChangeV2.Transition'; ConfChangeV2.Changes'; ConfChangeV2.Context' >.
Global Instance into_val_ConfChangeV2 `{ffi_syntax} : IntoVal ConfChangeV2.t.
Admitted.

Global Instance into_val_typed_ConfChangeV2 `{ffi_syntax} : IntoValTyped ConfChangeV2.t raftpb.ConfChangeV2 :=
{|
  default_val := ConfChangeV2.mk (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_ConfChangeV2_Transition `{ffi_syntax} : IntoValStructField "Transition" raftpb.ConfChangeV2 ConfChangeV2.Transition'.
Admitted.

Global Instance into_val_struct_field_ConfChangeV2_Changes `{ffi_syntax} : IntoValStructField "Changes" raftpb.ConfChangeV2 ConfChangeV2.Changes'.
Admitted.

Global Instance into_val_struct_field_ConfChangeV2_Context `{ffi_syntax} : IntoValStructField "Context" raftpb.ConfChangeV2 ConfChangeV2.Context'.
Admitted.

Instance wp_struct_make_ConfChangeV2 `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} Transition' Changes' Context':
  PureWp True
    (struct.make raftpb.ConfChangeV2 (alist_val [
      "Transition" ::= #Transition';
      "Changes" ::= #Changes';
      "Context" ::= #Context'
    ]))%V
    #(ConfChangeV2.mk Transition' Changes' Context').
Admitted.

(* autogenerated by proofgen (names); do not modify *)
Require Import New.code.go_etcd_io.raft.v3.raftpb.
Require Export New.proof.proof_prelude.
Module raftpb.
Section defs.
Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Definition is_defined := is_global_definitions raftpb.pkg_name' var_addrs raftpb.functions' raftpb.msets'.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

End defs.
End raftpb.
