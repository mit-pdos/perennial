(* autogenerated from go.etcd.io/raft/v3/raftpb *)
From New.golang Require Import defn.

Definition raftpb : go_string := "go.etcd.io/raft/v3/raftpb".

Module raftpb.
Section code.
Context `{ffi_syntax}.


Definition ConfChangeI : go_type := interfaceT.

Definition EntryType : go_type := int32T.

Definition EntryNormal : expr := #(W32 0).

Definition EntryConfChange : expr := #(W32 1).

Definition EntryConfChangeV2 : expr := #(W32 2).

Axiom EntryType_name'init : val.

Axiom EntryType_value'init : val.

Definition MessageType : go_type := int32T.

Definition MsgHup : expr := #(W32 0).

Definition MsgBeat : expr := #(W32 1).

Definition MsgProp : expr := #(W32 2).

Definition MsgApp : expr := #(W32 3).

Definition MsgAppResp : expr := #(W32 4).

Definition MsgVote : expr := #(W32 5).

Definition MsgVoteResp : expr := #(W32 6).

Definition MsgSnap : expr := #(W32 7).

Definition MsgHeartbeat : expr := #(W32 8).

Definition MsgHeartbeatResp : expr := #(W32 9).

Definition MsgUnreachable : expr := #(W32 10).

Definition MsgSnapStatus : expr := #(W32 11).

Definition MsgCheckQuorum : expr := #(W32 12).

Definition MsgTransferLeader : expr := #(W32 13).

Definition MsgTimeoutNow : expr := #(W32 14).

Definition MsgReadIndex : expr := #(W32 15).

Definition MsgReadIndexResp : expr := #(W32 16).

Definition MsgPreVote : expr := #(W32 17).

Definition MsgPreVoteResp : expr := #(W32 18).

Definition MsgStorageAppend : expr := #(W32 19).

Definition MsgStorageAppendResp : expr := #(W32 20).

Definition MsgStorageApply : expr := #(W32 21).

Definition MsgStorageApplyResp : expr := #(W32 22).

Definition MsgForgetLeader : expr := #(W32 23).

Axiom MessageType_name'init : val.

Axiom MessageType_value'init : val.

Definition ConfChangeTransition : go_type := int32T.

Axiom ConfChangeTransition_name'init : val.

Axiom ConfChangeTransition_value'init : val.

Definition ConfChangeType : go_type := int32T.

Definition ConfChangeAddNode : expr := #(W32 0).

Definition ConfChangeRemoveNode : expr := #(W32 1).

Definition ConfChangeUpdateNode : expr := #(W32 2).

Definition ConfChangeAddLearnerNode : expr := #(W32 3).

Axiom ConfChangeType_name'init : val.

Axiom ConfChangeType_value'init : val.

Definition Entry : go_type := structT [
  "Term" :: uint64T;
  "Index" :: uint64T;
  "Type" :: EntryType;
  "Data" :: sliceT
].

Definition ConfState : go_type := structT [
  "Voters" :: sliceT;
  "Learners" :: sliceT;
  "VotersOutgoing" :: sliceT;
  "LearnersNext" :: sliceT;
  "AutoLeave" :: boolT
].

Definition SnapshotMetadata : go_type := structT [
  "ConfState" :: ConfState;
  "Index" :: uint64T;
  "Term" :: uint64T
].

Definition Snapshot : go_type := structT [
  "Data" :: sliceT;
  "Metadata" :: SnapshotMetadata
].

Axiom Message : go_type.

Definition HardState : go_type := structT [
  "Term" :: uint64T;
  "Vote" :: uint64T;
  "Commit" :: uint64T
].

Definition ConfChange : go_type := structT [
  "Type" :: ConfChangeType;
  "NodeID" :: uint64T;
  "Context" :: sliceT;
  "ID" :: uint64T
].

Definition ConfChangeV2 : go_type := structT [
  "Transition" :: ConfChangeTransition;
  "Changes" :: sliceT;
  "Context" :: sliceT
].

Axiom fileDescriptor_b042552c306ae59b'init : val.

Axiom ErrInvalidLengthRaft'init : val.

Axiom ErrIntOverflowRaft'init : val.

Axiom ErrUnexpectedEndOfGroupRaft'init : val.

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [].

Definition msets' : list (go_string * (list (go_string * val))) := [("EntryType"%go, []); ("EntryType'ptr"%go, []); ("MessageType"%go, []); ("MessageType'ptr"%go, []); ("ConfChangeTransition"%go, []); ("ConfChangeTransition'ptr"%go, []); ("ConfChangeType"%go, []); ("ConfChangeType'ptr"%go, []); ("Entry"%go, []); ("Entry'ptr"%go, []); ("SnapshotMetadata"%go, []); ("SnapshotMetadata'ptr"%go, []); ("Snapshot"%go, []); ("Snapshot'ptr"%go, []); ("HardState"%go, []); ("HardState'ptr"%go, []); ("ConfState"%go, []); ("ConfState'ptr"%go, []); ("ConfChange"%go, []); ("ConfChange'ptr"%go, []); ("ConfChangeV2"%go, []); ("ConfChangeV2'ptr"%go, [])].

#[global] Instance info' : PkgInfo raftpb.raftpb :=
  {|
    pkg_vars := vars';
    pkg_functions := functions';
    pkg_msets := msets';
    pkg_imported_pkgs := [];
  |}.

Axiom _'init : val.

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init raftpb.raftpb (λ: <>,
      exception_do (do:  (_'init #());;;
      do:  (_'init #());;;
      do:  (_'init #());;;
      do:  (EntryType_name'init #());;;
      do:  (EntryType_value'init #());;;
      do:  (MessageType_name'init #());;;
      do:  (MessageType_value'init #());;;
      do:  (ConfChangeTransition_name'init #());;;
      do:  (ConfChangeTransition_value'init #());;;
      do:  (ConfChangeType_name'init #());;;
      do:  (ConfChangeType_value'init #());;;
      do:  (fileDescriptor_b042552c306ae59b'init #());;;
      do:  (ErrInvalidLengthRaft'init #());;;
      do:  (ErrIntOverflowRaft'init #());;;
      do:  (ErrUnexpectedEndOfGroupRaft'init #()))
      ).

End code.
End raftpb.
