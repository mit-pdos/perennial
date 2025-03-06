(* autogenerated from go.etcd.io/etcd/api/v3/mvccpb *)
From New.golang Require Import defn.

Module mvccpb.
Section code.
Context `{ffi_syntax}.


Definition Event_EventType : go_type := int32T.

Definition PUT : expr := #(W32 0).

Definition DELETE : expr := #(W32 1).

Axiom Event_EventType_name'init : val.

Axiom Event_EventType_value'init : val.

Definition KeyValue : go_type := structT [
  "Key" :: sliceT;
  "CreateRevision" :: int64T;
  "ModRevision" :: int64T;
  "Version" :: int64T;
  "Value" :: sliceT;
  "Lease" :: int64T;
  "XXX_NoUnkeyedLiteral" :: structT [
  ];
  "XXX_unrecognized" :: sliceT;
  "XXX_sizecache" :: int32T
].

Definition Event : go_type := structT [
  "Type" :: Event_EventType;
  "Kv" :: ptrT;
  "PrevKv" :: ptrT;
  "XXX_NoUnkeyedLiteral" :: structT [
  ];
  "XXX_unrecognized" :: sliceT;
  "XXX_sizecache" :: int32T
].

Axiom fileDescriptor_2216fe83c9c12408'init : val.

Axiom ErrInvalidLengthKv'init : val.

Axiom ErrIntOverflowKv'init : val.

Axiom ErrUnexpectedEndOfGroupKv'init : val.

Definition pkg_name' : go_string := "go.etcd.io/etcd/api/v3/mvccpb".

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [].

Definition msets' : list (go_string * (list (go_string * val))) := [("Event_EventType"%go, []); ("Event_EventType'ptr"%go, []); ("KeyValue"%go, []); ("KeyValue'ptr"%go, []); ("Event"%go, []); ("Event'ptr"%go, [])].

Definition info' : pkg_info.t := {|
             pkg_info.vars := vars';
             pkg_info.functions := functions';
             pkg_info.msets := msets';
             pkg_info.imported_pkgs := [];
           |}.

#[global] Instance  : PkgInfo pkg_name' info' :=
  {}.

Axiom _'init : val.

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init pkg_name' (λ: <>,
      exception_do (do:  (_'init #());;;
      do:  (_'init #());;;
      do:  (_'init #());;;
      do:  (Event_EventType_name'init #());;;
      do:  (Event_EventType_value'init #());;;
      do:  (fileDescriptor_2216fe83c9c12408'init #());;;
      do:  (ErrInvalidLengthKv'init #());;;
      do:  (ErrIntOverflowKv'init #());;;
      do:  (ErrUnexpectedEndOfGroupKv'init #()))
      ).

End code.
End mvccpb.
