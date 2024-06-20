From Perennial.goose_lang Require Import lang notation.
From Perennial.goose_lang.ffi.grove_ffi Require Export impl.
From Perennial.goose_lang Require Import prelude typing.

Inductive GroveTys : Set := GroveListenTy | GroveConnectionTy.
#[global]
(* TODO: Why is this an instance but the ones above are not? *)
Instance grove_val_ty: val_types :=
  {| ext_tys := GroveTys; |}.
Instance grove_ty: ext_types grove_op :=
  {| val_tys := grove_val_ty;
     get_ext_tys _ _ := False |}. (* currently we just don't give types for the GroveOps *)

(** * Grove user-facing operations. *)
Section grove.
  (* these are local instances on purpose, so that importing this files doesn't
  suddenly cause all FFI parameters to be inferred as the grove model *)
  (* FIXME: figure out which of these clients need to set *)
  Existing Instances grove_op grove_model grove_ty grove_semantics.
  Local Coercion Var' (s:string) : expr := Var s.

  (** [extT] have size 1 so this fits with them being pointers in Go. *)
  Definition Listener : ty := extT GroveListenTy.
  Definition Connection : ty := extT GroveConnectionTy.
  Definition Address : ty := uint64T.

  Definition ConnectRet := (struct.decl [
                              "Err" :: boolT;
                              "Connection" :: Connection
                            ])%struct.

  Definition ReceiveRet := (struct.decl [
                              "Err" :: boolT;
                              "Data" :: slice.T byteT
                            ])%struct.

  (** Type: func(uint64) Listener *)
  Definition Listen : val :=
    λ: "e", ExternalOp ListenOp "e".

  (** Type: func(uint64) (bool, Connection) *)
  Definition Connect : val :=
    λ: "e",
      let: "c" := ExternalOp ConnectOp "e" in
      let: "err" := Fst "c" in
      let: "socket" := Snd "c" in
      struct.mk ConnectRet [
        "Err" ::= "err";
        "Connection" ::= "socket"
      ].

  (** Type: func(Listener) Connection *)
  Definition Accept : val :=
    λ: "e", ExternalOp AcceptOp "e".

  (** Type: func(Connection, []byte) *)
  Definition Send : val :=
    λ: "e" "m", ExternalOp SendOp ("e", (slice.ptr "m", slice.len "m")).

  (** Type: func(Connection) (bool, []byte) *)
  Definition Receive : val :=
    λ: "e",
      let: "r" := ExternalOp RecvOp "e" in
      let: "err" := Fst "r" in
      let: "slice" := Snd "r" in
      let: "ptr" := Fst "slice" in
      let: "len" := Snd "slice" in
      struct.mk ReceiveRet [
        "Err" ::= "err";
        "Data" ::= ("ptr", "len", "len")
      ].


  (** FileRead pretends that the operation can never fail.
      The Go implementation will accordingly abort the program if an I/O error occurs. *)
  Definition FileRead : val :=
    λ: "f",
      let: "ret" := ExternalOp FileReadOp "f" in
      let: "err" := Fst "ret" in
      let: "slice" := Snd "ret" in
      if: "err" then control.impl.Exit #() else
      let: "ptr" := Fst "slice" in
      let: "len" := Snd "slice" in
      ("ptr", "len", "len").

  (** FileWrite pretends that the operation can never fail.
      The Go implementation will accordingly abort the program if an I/O error occurs. *)
  Definition FileWrite : val :=
    λ: "f" "c",
      let: "err" := ExternalOp FileWriteOp ("f", (slice.ptr "c", slice.len "c")) in
      if: "err" then control.impl.Exit #() else
      #().

  (** FileAppend pretends that the operation can never fail.
      The Go implementation will accordingly abort the program if an I/O error occurs. *)
  Definition FileAppend : val :=
    λ: "f" "c",
      let: "err" := ExternalOp FileAppendOp ("f", (slice.ptr "c", slice.len "c")) in
      if: "err" then control.impl.Exit #() else
      #().

  (** Type: func() uint64 *)
  Definition GetTSC : val :=
    λ: <>, ExternalOp GetTscOp #().

  (** Type: func() (uint64, uint64) *)
  Definition GetTimeRange : val :=
    λ: <>, ExternalOp GetTimeRangeOp #().

End grove.
