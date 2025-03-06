(* autogenerated by goose proofgen (types); do not modify *)
Require Export New.proof.proof_prelude.
Require Export New.code.go_etcd_io.raft.v3.raftpb.
Require Export New.golang.theory.

Module raftpb.
Axiom falso : False.

Module ConfChangeI.
Section def.
Context `{ffi_syntax}.
Definition t := interface.t.
End def.
End ConfChangeI.

Module EntryType.
Section def.
Context `{ffi_syntax}.
Definition t := w32.
End def.
End EntryType.

Module MessageType.
Section def.
Context `{ffi_syntax}.
Definition t := w32.
End def.
End MessageType.

Module ConfChangeTransition.
Section def.
Context `{ffi_syntax}.
Definition t := w32.
End def.
End ConfChangeTransition.

Module ConfChangeType.
Section def.
Context `{ffi_syntax}.
Definition t := w32.
End def.
End ConfChangeType.
Module Entry.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Term' : w64;
  Index' : w64;
  Type' : EntryType.t;
  Data' : slice.t;
}.
End def.
End Entry.

Section instances.
Context `{ffi_syntax}.

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


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_Entry `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} Term' Index' Type' Data':
  PureWp True
    (struct.make raftpb.Entry (alist_val [
      "Term" ::= #Term';
      "Index" ::= #Index';
      "Type" ::= #Type';
      "Data" ::= #Data'
    ]))%V
    #(Entry.mk Term' Index' Type' Data').
Admitted.


Global Instance Entry_struct_fields_split dq l (v : Entry.t) :
  StructFieldsSplit dq l v (
    "HTerm" ∷ l ↦s[raftpb.Entry :: "Term"]{dq} v.(Entry.Term') ∗
    "HIndex" ∷ l ↦s[raftpb.Entry :: "Index"]{dq} v.(Entry.Index') ∗
    "HType" ∷ l ↦s[raftpb.Entry :: "Type"]{dq} v.(Entry.Type') ∗
    "HData" ∷ l ↦s[raftpb.Entry :: "Data"]{dq} v.(Entry.Data')
  ).
Admitted.

End instances.
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

Section instances.
Context `{ffi_syntax}.

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


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_ConfState `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} Voters' Learners' VotersOutgoing' LearnersNext' AutoLeave':
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


Global Instance ConfState_struct_fields_split dq l (v : ConfState.t) :
  StructFieldsSplit dq l v (
    "HVoters" ∷ l ↦s[raftpb.ConfState :: "Voters"]{dq} v.(ConfState.Voters') ∗
    "HLearners" ∷ l ↦s[raftpb.ConfState :: "Learners"]{dq} v.(ConfState.Learners') ∗
    "HVotersOutgoing" ∷ l ↦s[raftpb.ConfState :: "VotersOutgoing"]{dq} v.(ConfState.VotersOutgoing') ∗
    "HLearnersNext" ∷ l ↦s[raftpb.ConfState :: "LearnersNext"]{dq} v.(ConfState.LearnersNext') ∗
    "HAutoLeave" ∷ l ↦s[raftpb.ConfState :: "AutoLeave"]{dq} v.(ConfState.AutoLeave')
  ).
Admitted.

End instances.
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

Section instances.
Context `{ffi_syntax}.

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


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_SnapshotMetadata `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} ConfState' Index' Term':
  PureWp True
    (struct.make raftpb.SnapshotMetadata (alist_val [
      "ConfState" ::= #ConfState';
      "Index" ::= #Index';
      "Term" ::= #Term'
    ]))%V
    #(SnapshotMetadata.mk ConfState' Index' Term').
Admitted.


Global Instance SnapshotMetadata_struct_fields_split dq l (v : SnapshotMetadata.t) :
  StructFieldsSplit dq l v (
    "HConfState" ∷ l ↦s[raftpb.SnapshotMetadata :: "ConfState"]{dq} v.(SnapshotMetadata.ConfState') ∗
    "HIndex" ∷ l ↦s[raftpb.SnapshotMetadata :: "Index"]{dq} v.(SnapshotMetadata.Index') ∗
    "HTerm" ∷ l ↦s[raftpb.SnapshotMetadata :: "Term"]{dq} v.(SnapshotMetadata.Term')
  ).
Admitted.

End instances.
Module Snapshot.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Data' : slice.t;
  Metadata' : SnapshotMetadata.t;
}.
End def.
End Snapshot.

Section instances.
Context `{ffi_syntax}.

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


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_Snapshot `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} Data' Metadata':
  PureWp True
    (struct.make raftpb.Snapshot (alist_val [
      "Data" ::= #Data';
      "Metadata" ::= #Metadata'
    ]))%V
    #(Snapshot.mk Data' Metadata').
Admitted.


Global Instance Snapshot_struct_fields_split dq l (v : Snapshot.t) :
  StructFieldsSplit dq l v (
    "HData" ∷ l ↦s[raftpb.Snapshot :: "Data"]{dq} v.(Snapshot.Data') ∗
    "HMetadata" ∷ l ↦s[raftpb.Snapshot :: "Metadata"]{dq} v.(Snapshot.Metadata')
  ).
Admitted.

End instances.
Module Message.
Section def.
Context `{ffi_syntax}.
Axiom t : Type.
End def.
End Message.

Global Instance into_val_Message `{ffi_syntax} : IntoVal Message.t.
Admitted.

Global Instance into_val_typed_Message `{ffi_syntax} : IntoValTyped Message.t raftpb.Message.
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

Section instances.
Context `{ffi_syntax}.

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


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_HardState `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} Term' Vote' Commit':
  PureWp True
    (struct.make raftpb.HardState (alist_val [
      "Term" ::= #Term';
      "Vote" ::= #Vote';
      "Commit" ::= #Commit'
    ]))%V
    #(HardState.mk Term' Vote' Commit').
Admitted.


Global Instance HardState_struct_fields_split dq l (v : HardState.t) :
  StructFieldsSplit dq l v (
    "HTerm" ∷ l ↦s[raftpb.HardState :: "Term"]{dq} v.(HardState.Term') ∗
    "HVote" ∷ l ↦s[raftpb.HardState :: "Vote"]{dq} v.(HardState.Vote') ∗
    "HCommit" ∷ l ↦s[raftpb.HardState :: "Commit"]{dq} v.(HardState.Commit')
  ).
Admitted.

End instances.
Module ConfChange.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Type' : ConfChangeType.t;
  NodeID' : w64;
  Context' : slice.t;
  ID' : w64;
}.
End def.
End ConfChange.

Section instances.
Context `{ffi_syntax}.

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


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_ConfChange `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} Type' NodeID' Context' ID':
  PureWp True
    (struct.make raftpb.ConfChange (alist_val [
      "Type" ::= #Type';
      "NodeID" ::= #NodeID';
      "Context" ::= #Context';
      "ID" ::= #ID'
    ]))%V
    #(ConfChange.mk Type' NodeID' Context' ID').
Admitted.


Global Instance ConfChange_struct_fields_split dq l (v : ConfChange.t) :
  StructFieldsSplit dq l v (
    "HType" ∷ l ↦s[raftpb.ConfChange :: "Type"]{dq} v.(ConfChange.Type') ∗
    "HNodeID" ∷ l ↦s[raftpb.ConfChange :: "NodeID"]{dq} v.(ConfChange.NodeID') ∗
    "HContext" ∷ l ↦s[raftpb.ConfChange :: "Context"]{dq} v.(ConfChange.Context') ∗
    "HID" ∷ l ↦s[raftpb.ConfChange :: "ID"]{dq} v.(ConfChange.ID')
  ).
Admitted.

End instances.
Module ConfChangeV2.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Transition' : ConfChangeTransition.t;
  Changes' : slice.t;
  Context' : slice.t;
}.
End def.
End ConfChangeV2.

Section instances.
Context `{ffi_syntax}.

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


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_ConfChangeV2 `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} Transition' Changes' Context':
  PureWp True
    (struct.make raftpb.ConfChangeV2 (alist_val [
      "Transition" ::= #Transition';
      "Changes" ::= #Changes';
      "Context" ::= #Context'
    ]))%V
    #(ConfChangeV2.mk Transition' Changes' Context').
Admitted.


Global Instance ConfChangeV2_struct_fields_split dq l (v : ConfChangeV2.t) :
  StructFieldsSplit dq l v (
    "HTransition" ∷ l ↦s[raftpb.ConfChangeV2 :: "Transition"]{dq} v.(ConfChangeV2.Transition') ∗
    "HChanges" ∷ l ↦s[raftpb.ConfChangeV2 :: "Changes"]{dq} v.(ConfChangeV2.Changes') ∗
    "HContext" ∷ l ↦s[raftpb.ConfChangeV2 :: "Context"]{dq} v.(ConfChangeV2.Context')
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

Definition is_defined := is_global_definitions raftpb.pkg_name' var_addrs raftpb.functions' raftpb.msets'.

Global Instance is_pkg_defined : PkgIsDefined raftpb.pkg_name' is_defined :=
  ltac:(prove_pkg_is_defined).

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

End names.
End raftpb.
