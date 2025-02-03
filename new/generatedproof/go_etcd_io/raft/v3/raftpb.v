(* autogenerated by goose proofgen (types); do not modify *)
From New.code Require Import go_etcd_io.raft.v3.raftpb.
From New.golang Require Import theory.

Axiom falso : False.

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

Global Instance wp_func_call_MarshalConfChange : 
  WpFuncCall raftpb.pkg_name' "MarshalConfChange" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_ConfChangesFromString : 
  WpFuncCall raftpb.pkg_name' "ConfChangesFromString" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_ConfChangesToString : 
  WpFuncCall raftpb.pkg_name' "ConfChangesToString" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_encodeVarintRaft : 
  WpFuncCall raftpb.pkg_name' "encodeVarintRaft" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_sovRaft : 
  WpFuncCall raftpb.pkg_name' "sovRaft" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_sozRaft : 
  WpFuncCall raftpb.pkg_name' "sozRaft" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_skipRaft : 
  WpFuncCall raftpb.pkg_name' "skipRaft" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_method_call_EntryType_Enum : 
  WpMethodCall raftpb.pkg_name' "EntryType" "Enum" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_EntryType_EnumDescriptor : 
  WpMethodCall raftpb.pkg_name' "EntryType" "EnumDescriptor" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_EntryType_String : 
  WpMethodCall raftpb.pkg_name' "EntryType" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_EntryType'ptr_Enum : 
  WpMethodCall raftpb.pkg_name' "EntryType'ptr" "Enum" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_EntryType'ptr_EnumDescriptor : 
  WpMethodCall raftpb.pkg_name' "EntryType'ptr" "EnumDescriptor" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_EntryType'ptr_String : 
  WpMethodCall raftpb.pkg_name' "EntryType'ptr" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_EntryType'ptr_UnmarshalJSON : 
  WpMethodCall raftpb.pkg_name' "EntryType'ptr" "UnmarshalJSON" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MessageType_Enum : 
  WpMethodCall raftpb.pkg_name' "MessageType" "Enum" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MessageType_EnumDescriptor : 
  WpMethodCall raftpb.pkg_name' "MessageType" "EnumDescriptor" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MessageType_String : 
  WpMethodCall raftpb.pkg_name' "MessageType" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MessageType'ptr_Enum : 
  WpMethodCall raftpb.pkg_name' "MessageType'ptr" "Enum" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MessageType'ptr_EnumDescriptor : 
  WpMethodCall raftpb.pkg_name' "MessageType'ptr" "EnumDescriptor" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MessageType'ptr_String : 
  WpMethodCall raftpb.pkg_name' "MessageType'ptr" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_MessageType'ptr_UnmarshalJSON : 
  WpMethodCall raftpb.pkg_name' "MessageType'ptr" "UnmarshalJSON" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeTransition_Enum : 
  WpMethodCall raftpb.pkg_name' "ConfChangeTransition" "Enum" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeTransition_EnumDescriptor : 
  WpMethodCall raftpb.pkg_name' "ConfChangeTransition" "EnumDescriptor" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeTransition_String : 
  WpMethodCall raftpb.pkg_name' "ConfChangeTransition" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeTransition'ptr_Enum : 
  WpMethodCall raftpb.pkg_name' "ConfChangeTransition'ptr" "Enum" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeTransition'ptr_EnumDescriptor : 
  WpMethodCall raftpb.pkg_name' "ConfChangeTransition'ptr" "EnumDescriptor" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeTransition'ptr_String : 
  WpMethodCall raftpb.pkg_name' "ConfChangeTransition'ptr" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeTransition'ptr_UnmarshalJSON : 
  WpMethodCall raftpb.pkg_name' "ConfChangeTransition'ptr" "UnmarshalJSON" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeType_Enum : 
  WpMethodCall raftpb.pkg_name' "ConfChangeType" "Enum" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeType_EnumDescriptor : 
  WpMethodCall raftpb.pkg_name' "ConfChangeType" "EnumDescriptor" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeType_String : 
  WpMethodCall raftpb.pkg_name' "ConfChangeType" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeType'ptr_Enum : 
  WpMethodCall raftpb.pkg_name' "ConfChangeType'ptr" "Enum" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeType'ptr_EnumDescriptor : 
  WpMethodCall raftpb.pkg_name' "ConfChangeType'ptr" "EnumDescriptor" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeType'ptr_String : 
  WpMethodCall raftpb.pkg_name' "ConfChangeType'ptr" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeType'ptr_UnmarshalJSON : 
  WpMethodCall raftpb.pkg_name' "ConfChangeType'ptr" "UnmarshalJSON" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Entry'ptr_Descriptor : 
  WpMethodCall raftpb.pkg_name' "Entry'ptr" "Descriptor" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Entry'ptr_Marshal : 
  WpMethodCall raftpb.pkg_name' "Entry'ptr" "Marshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Entry'ptr_MarshalTo : 
  WpMethodCall raftpb.pkg_name' "Entry'ptr" "MarshalTo" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Entry'ptr_MarshalToSizedBuffer : 
  WpMethodCall raftpb.pkg_name' "Entry'ptr" "MarshalToSizedBuffer" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Entry'ptr_ProtoMessage : 
  WpMethodCall raftpb.pkg_name' "Entry'ptr" "ProtoMessage" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Entry'ptr_Reset : 
  WpMethodCall raftpb.pkg_name' "Entry'ptr" "Reset" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Entry'ptr_Size : 
  WpMethodCall raftpb.pkg_name' "Entry'ptr" "Size" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Entry'ptr_String : 
  WpMethodCall raftpb.pkg_name' "Entry'ptr" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Entry'ptr_Unmarshal : 
  WpMethodCall raftpb.pkg_name' "Entry'ptr" "Unmarshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Entry'ptr_XXX_DiscardUnknown : 
  WpMethodCall raftpb.pkg_name' "Entry'ptr" "XXX_DiscardUnknown" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Entry'ptr_XXX_Marshal : 
  WpMethodCall raftpb.pkg_name' "Entry'ptr" "XXX_Marshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Entry'ptr_XXX_Merge : 
  WpMethodCall raftpb.pkg_name' "Entry'ptr" "XXX_Merge" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Entry'ptr_XXX_Size : 
  WpMethodCall raftpb.pkg_name' "Entry'ptr" "XXX_Size" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Entry'ptr_XXX_Unmarshal : 
  WpMethodCall raftpb.pkg_name' "Entry'ptr" "XXX_Unmarshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_SnapshotMetadata'ptr_Descriptor : 
  WpMethodCall raftpb.pkg_name' "SnapshotMetadata'ptr" "Descriptor" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_SnapshotMetadata'ptr_Marshal : 
  WpMethodCall raftpb.pkg_name' "SnapshotMetadata'ptr" "Marshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_SnapshotMetadata'ptr_MarshalTo : 
  WpMethodCall raftpb.pkg_name' "SnapshotMetadata'ptr" "MarshalTo" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_SnapshotMetadata'ptr_MarshalToSizedBuffer : 
  WpMethodCall raftpb.pkg_name' "SnapshotMetadata'ptr" "MarshalToSizedBuffer" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_SnapshotMetadata'ptr_ProtoMessage : 
  WpMethodCall raftpb.pkg_name' "SnapshotMetadata'ptr" "ProtoMessage" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_SnapshotMetadata'ptr_Reset : 
  WpMethodCall raftpb.pkg_name' "SnapshotMetadata'ptr" "Reset" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_SnapshotMetadata'ptr_Size : 
  WpMethodCall raftpb.pkg_name' "SnapshotMetadata'ptr" "Size" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_SnapshotMetadata'ptr_String : 
  WpMethodCall raftpb.pkg_name' "SnapshotMetadata'ptr" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_SnapshotMetadata'ptr_Unmarshal : 
  WpMethodCall raftpb.pkg_name' "SnapshotMetadata'ptr" "Unmarshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_SnapshotMetadata'ptr_XXX_DiscardUnknown : 
  WpMethodCall raftpb.pkg_name' "SnapshotMetadata'ptr" "XXX_DiscardUnknown" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_SnapshotMetadata'ptr_XXX_Marshal : 
  WpMethodCall raftpb.pkg_name' "SnapshotMetadata'ptr" "XXX_Marshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_SnapshotMetadata'ptr_XXX_Merge : 
  WpMethodCall raftpb.pkg_name' "SnapshotMetadata'ptr" "XXX_Merge" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_SnapshotMetadata'ptr_XXX_Size : 
  WpMethodCall raftpb.pkg_name' "SnapshotMetadata'ptr" "XXX_Size" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_SnapshotMetadata'ptr_XXX_Unmarshal : 
  WpMethodCall raftpb.pkg_name' "SnapshotMetadata'ptr" "XXX_Unmarshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Snapshot'ptr_Descriptor : 
  WpMethodCall raftpb.pkg_name' "Snapshot'ptr" "Descriptor" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Snapshot'ptr_Marshal : 
  WpMethodCall raftpb.pkg_name' "Snapshot'ptr" "Marshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Snapshot'ptr_MarshalTo : 
  WpMethodCall raftpb.pkg_name' "Snapshot'ptr" "MarshalTo" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Snapshot'ptr_MarshalToSizedBuffer : 
  WpMethodCall raftpb.pkg_name' "Snapshot'ptr" "MarshalToSizedBuffer" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Snapshot'ptr_ProtoMessage : 
  WpMethodCall raftpb.pkg_name' "Snapshot'ptr" "ProtoMessage" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Snapshot'ptr_Reset : 
  WpMethodCall raftpb.pkg_name' "Snapshot'ptr" "Reset" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Snapshot'ptr_Size : 
  WpMethodCall raftpb.pkg_name' "Snapshot'ptr" "Size" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Snapshot'ptr_String : 
  WpMethodCall raftpb.pkg_name' "Snapshot'ptr" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Snapshot'ptr_Unmarshal : 
  WpMethodCall raftpb.pkg_name' "Snapshot'ptr" "Unmarshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Snapshot'ptr_XXX_DiscardUnknown : 
  WpMethodCall raftpb.pkg_name' "Snapshot'ptr" "XXX_DiscardUnknown" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Snapshot'ptr_XXX_Marshal : 
  WpMethodCall raftpb.pkg_name' "Snapshot'ptr" "XXX_Marshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Snapshot'ptr_XXX_Merge : 
  WpMethodCall raftpb.pkg_name' "Snapshot'ptr" "XXX_Merge" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Snapshot'ptr_XXX_Size : 
  WpMethodCall raftpb.pkg_name' "Snapshot'ptr" "XXX_Size" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Snapshot'ptr_XXX_Unmarshal : 
  WpMethodCall raftpb.pkg_name' "Snapshot'ptr" "XXX_Unmarshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Message'ptr_Descriptor : 
  WpMethodCall raftpb.pkg_name' "Message'ptr" "Descriptor" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Message'ptr_Marshal : 
  WpMethodCall raftpb.pkg_name' "Message'ptr" "Marshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Message'ptr_MarshalTo : 
  WpMethodCall raftpb.pkg_name' "Message'ptr" "MarshalTo" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Message'ptr_MarshalToSizedBuffer : 
  WpMethodCall raftpb.pkg_name' "Message'ptr" "MarshalToSizedBuffer" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Message'ptr_ProtoMessage : 
  WpMethodCall raftpb.pkg_name' "Message'ptr" "ProtoMessage" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Message'ptr_Reset : 
  WpMethodCall raftpb.pkg_name' "Message'ptr" "Reset" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Message'ptr_Size : 
  WpMethodCall raftpb.pkg_name' "Message'ptr" "Size" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Message'ptr_String : 
  WpMethodCall raftpb.pkg_name' "Message'ptr" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Message'ptr_Unmarshal : 
  WpMethodCall raftpb.pkg_name' "Message'ptr" "Unmarshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Message'ptr_XXX_DiscardUnknown : 
  WpMethodCall raftpb.pkg_name' "Message'ptr" "XXX_DiscardUnknown" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Message'ptr_XXX_Marshal : 
  WpMethodCall raftpb.pkg_name' "Message'ptr" "XXX_Marshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Message'ptr_XXX_Merge : 
  WpMethodCall raftpb.pkg_name' "Message'ptr" "XXX_Merge" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Message'ptr_XXX_Size : 
  WpMethodCall raftpb.pkg_name' "Message'ptr" "XXX_Size" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Message'ptr_XXX_Unmarshal : 
  WpMethodCall raftpb.pkg_name' "Message'ptr" "XXX_Unmarshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_HardState'ptr_Descriptor : 
  WpMethodCall raftpb.pkg_name' "HardState'ptr" "Descriptor" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_HardState'ptr_Marshal : 
  WpMethodCall raftpb.pkg_name' "HardState'ptr" "Marshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_HardState'ptr_MarshalTo : 
  WpMethodCall raftpb.pkg_name' "HardState'ptr" "MarshalTo" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_HardState'ptr_MarshalToSizedBuffer : 
  WpMethodCall raftpb.pkg_name' "HardState'ptr" "MarshalToSizedBuffer" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_HardState'ptr_ProtoMessage : 
  WpMethodCall raftpb.pkg_name' "HardState'ptr" "ProtoMessage" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_HardState'ptr_Reset : 
  WpMethodCall raftpb.pkg_name' "HardState'ptr" "Reset" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_HardState'ptr_Size : 
  WpMethodCall raftpb.pkg_name' "HardState'ptr" "Size" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_HardState'ptr_String : 
  WpMethodCall raftpb.pkg_name' "HardState'ptr" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_HardState'ptr_Unmarshal : 
  WpMethodCall raftpb.pkg_name' "HardState'ptr" "Unmarshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_HardState'ptr_XXX_DiscardUnknown : 
  WpMethodCall raftpb.pkg_name' "HardState'ptr" "XXX_DiscardUnknown" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_HardState'ptr_XXX_Marshal : 
  WpMethodCall raftpb.pkg_name' "HardState'ptr" "XXX_Marshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_HardState'ptr_XXX_Merge : 
  WpMethodCall raftpb.pkg_name' "HardState'ptr" "XXX_Merge" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_HardState'ptr_XXX_Size : 
  WpMethodCall raftpb.pkg_name' "HardState'ptr" "XXX_Size" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_HardState'ptr_XXX_Unmarshal : 
  WpMethodCall raftpb.pkg_name' "HardState'ptr" "XXX_Unmarshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfState_Equivalent : 
  WpMethodCall raftpb.pkg_name' "ConfState" "Equivalent" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfState'ptr_Descriptor : 
  WpMethodCall raftpb.pkg_name' "ConfState'ptr" "Descriptor" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfState'ptr_Equivalent : 
  WpMethodCall raftpb.pkg_name' "ConfState'ptr" "Equivalent" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfState'ptr_Marshal : 
  WpMethodCall raftpb.pkg_name' "ConfState'ptr" "Marshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfState'ptr_MarshalTo : 
  WpMethodCall raftpb.pkg_name' "ConfState'ptr" "MarshalTo" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfState'ptr_MarshalToSizedBuffer : 
  WpMethodCall raftpb.pkg_name' "ConfState'ptr" "MarshalToSizedBuffer" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfState'ptr_ProtoMessage : 
  WpMethodCall raftpb.pkg_name' "ConfState'ptr" "ProtoMessage" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfState'ptr_Reset : 
  WpMethodCall raftpb.pkg_name' "ConfState'ptr" "Reset" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfState'ptr_Size : 
  WpMethodCall raftpb.pkg_name' "ConfState'ptr" "Size" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfState'ptr_String : 
  WpMethodCall raftpb.pkg_name' "ConfState'ptr" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfState'ptr_Unmarshal : 
  WpMethodCall raftpb.pkg_name' "ConfState'ptr" "Unmarshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfState'ptr_XXX_DiscardUnknown : 
  WpMethodCall raftpb.pkg_name' "ConfState'ptr" "XXX_DiscardUnknown" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfState'ptr_XXX_Marshal : 
  WpMethodCall raftpb.pkg_name' "ConfState'ptr" "XXX_Marshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfState'ptr_XXX_Merge : 
  WpMethodCall raftpb.pkg_name' "ConfState'ptr" "XXX_Merge" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfState'ptr_XXX_Size : 
  WpMethodCall raftpb.pkg_name' "ConfState'ptr" "XXX_Size" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfState'ptr_XXX_Unmarshal : 
  WpMethodCall raftpb.pkg_name' "ConfState'ptr" "XXX_Unmarshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChange_AsV1 : 
  WpMethodCall raftpb.pkg_name' "ConfChange" "AsV1" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChange_AsV2 : 
  WpMethodCall raftpb.pkg_name' "ConfChange" "AsV2" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChange'ptr_AsV1 : 
  WpMethodCall raftpb.pkg_name' "ConfChange'ptr" "AsV1" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChange'ptr_AsV2 : 
  WpMethodCall raftpb.pkg_name' "ConfChange'ptr" "AsV2" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChange'ptr_Descriptor : 
  WpMethodCall raftpb.pkg_name' "ConfChange'ptr" "Descriptor" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChange'ptr_Marshal : 
  WpMethodCall raftpb.pkg_name' "ConfChange'ptr" "Marshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChange'ptr_MarshalTo : 
  WpMethodCall raftpb.pkg_name' "ConfChange'ptr" "MarshalTo" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChange'ptr_MarshalToSizedBuffer : 
  WpMethodCall raftpb.pkg_name' "ConfChange'ptr" "MarshalToSizedBuffer" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChange'ptr_ProtoMessage : 
  WpMethodCall raftpb.pkg_name' "ConfChange'ptr" "ProtoMessage" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChange'ptr_Reset : 
  WpMethodCall raftpb.pkg_name' "ConfChange'ptr" "Reset" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChange'ptr_Size : 
  WpMethodCall raftpb.pkg_name' "ConfChange'ptr" "Size" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChange'ptr_String : 
  WpMethodCall raftpb.pkg_name' "ConfChange'ptr" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChange'ptr_Unmarshal : 
  WpMethodCall raftpb.pkg_name' "ConfChange'ptr" "Unmarshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChange'ptr_XXX_DiscardUnknown : 
  WpMethodCall raftpb.pkg_name' "ConfChange'ptr" "XXX_DiscardUnknown" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChange'ptr_XXX_Marshal : 
  WpMethodCall raftpb.pkg_name' "ConfChange'ptr" "XXX_Marshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChange'ptr_XXX_Merge : 
  WpMethodCall raftpb.pkg_name' "ConfChange'ptr" "XXX_Merge" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChange'ptr_XXX_Size : 
  WpMethodCall raftpb.pkg_name' "ConfChange'ptr" "XXX_Size" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChange'ptr_XXX_Unmarshal : 
  WpMethodCall raftpb.pkg_name' "ConfChange'ptr" "XXX_Unmarshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeSingle'ptr_Descriptor : 
  WpMethodCall raftpb.pkg_name' "ConfChangeSingle'ptr" "Descriptor" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeSingle'ptr_Marshal : 
  WpMethodCall raftpb.pkg_name' "ConfChangeSingle'ptr" "Marshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeSingle'ptr_MarshalTo : 
  WpMethodCall raftpb.pkg_name' "ConfChangeSingle'ptr" "MarshalTo" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeSingle'ptr_MarshalToSizedBuffer : 
  WpMethodCall raftpb.pkg_name' "ConfChangeSingle'ptr" "MarshalToSizedBuffer" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeSingle'ptr_ProtoMessage : 
  WpMethodCall raftpb.pkg_name' "ConfChangeSingle'ptr" "ProtoMessage" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeSingle'ptr_Reset : 
  WpMethodCall raftpb.pkg_name' "ConfChangeSingle'ptr" "Reset" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeSingle'ptr_Size : 
  WpMethodCall raftpb.pkg_name' "ConfChangeSingle'ptr" "Size" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeSingle'ptr_String : 
  WpMethodCall raftpb.pkg_name' "ConfChangeSingle'ptr" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeSingle'ptr_Unmarshal : 
  WpMethodCall raftpb.pkg_name' "ConfChangeSingle'ptr" "Unmarshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeSingle'ptr_XXX_DiscardUnknown : 
  WpMethodCall raftpb.pkg_name' "ConfChangeSingle'ptr" "XXX_DiscardUnknown" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeSingle'ptr_XXX_Marshal : 
  WpMethodCall raftpb.pkg_name' "ConfChangeSingle'ptr" "XXX_Marshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeSingle'ptr_XXX_Merge : 
  WpMethodCall raftpb.pkg_name' "ConfChangeSingle'ptr" "XXX_Merge" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeSingle'ptr_XXX_Size : 
  WpMethodCall raftpb.pkg_name' "ConfChangeSingle'ptr" "XXX_Size" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeSingle'ptr_XXX_Unmarshal : 
  WpMethodCall raftpb.pkg_name' "ConfChangeSingle'ptr" "XXX_Unmarshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeV2_AsV1 : 
  WpMethodCall raftpb.pkg_name' "ConfChangeV2" "AsV1" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeV2_AsV2 : 
  WpMethodCall raftpb.pkg_name' "ConfChangeV2" "AsV2" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeV2_EnterJoint : 
  WpMethodCall raftpb.pkg_name' "ConfChangeV2" "EnterJoint" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeV2_LeaveJoint : 
  WpMethodCall raftpb.pkg_name' "ConfChangeV2" "LeaveJoint" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeV2'ptr_AsV1 : 
  WpMethodCall raftpb.pkg_name' "ConfChangeV2'ptr" "AsV1" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeV2'ptr_AsV2 : 
  WpMethodCall raftpb.pkg_name' "ConfChangeV2'ptr" "AsV2" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeV2'ptr_Descriptor : 
  WpMethodCall raftpb.pkg_name' "ConfChangeV2'ptr" "Descriptor" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeV2'ptr_EnterJoint : 
  WpMethodCall raftpb.pkg_name' "ConfChangeV2'ptr" "EnterJoint" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeV2'ptr_LeaveJoint : 
  WpMethodCall raftpb.pkg_name' "ConfChangeV2'ptr" "LeaveJoint" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeV2'ptr_Marshal : 
  WpMethodCall raftpb.pkg_name' "ConfChangeV2'ptr" "Marshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeV2'ptr_MarshalTo : 
  WpMethodCall raftpb.pkg_name' "ConfChangeV2'ptr" "MarshalTo" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeV2'ptr_MarshalToSizedBuffer : 
  WpMethodCall raftpb.pkg_name' "ConfChangeV2'ptr" "MarshalToSizedBuffer" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeV2'ptr_ProtoMessage : 
  WpMethodCall raftpb.pkg_name' "ConfChangeV2'ptr" "ProtoMessage" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeV2'ptr_Reset : 
  WpMethodCall raftpb.pkg_name' "ConfChangeV2'ptr" "Reset" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeV2'ptr_Size : 
  WpMethodCall raftpb.pkg_name' "ConfChangeV2'ptr" "Size" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeV2'ptr_String : 
  WpMethodCall raftpb.pkg_name' "ConfChangeV2'ptr" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeV2'ptr_Unmarshal : 
  WpMethodCall raftpb.pkg_name' "ConfChangeV2'ptr" "Unmarshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeV2'ptr_XXX_DiscardUnknown : 
  WpMethodCall raftpb.pkg_name' "ConfChangeV2'ptr" "XXX_DiscardUnknown" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeV2'ptr_XXX_Marshal : 
  WpMethodCall raftpb.pkg_name' "ConfChangeV2'ptr" "XXX_Marshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeV2'ptr_XXX_Merge : 
  WpMethodCall raftpb.pkg_name' "ConfChangeV2'ptr" "XXX_Merge" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeV2'ptr_XXX_Size : 
  WpMethodCall raftpb.pkg_name' "ConfChangeV2'ptr" "XXX_Size" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ConfChangeV2'ptr_XXX_Unmarshal : 
  WpMethodCall raftpb.pkg_name' "ConfChangeV2'ptr" "XXX_Unmarshal" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

End defs.
End raftpb.
