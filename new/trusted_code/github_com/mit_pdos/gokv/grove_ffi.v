From New.golang Require Import defn.
From Perennial.goose_lang.ffi.grove_ffi Require Export impl.

#[global]
Existing Instances grove_op grove_model.
(** * Grove user-facing operations. *)
Section grove.
  Context {go_gctx : GoGlobalContext}.

  (** These are pointers in Go. *)
  Definition Listener : go.type := unsafe.Pointer.
  Definition Connection : go.type := unsafe.Pointer.
  Definition Address : go.type := go.uint64.

  Definition ConnectRet := go.StructType [
                               go.FieldDecl "Err" go.bool;
                               go.FieldDecl "Connection" Connection
                             ].

  Definition ReceiveRet := go.StructType [
                               go.FieldDecl "Err" go.bool;
                               go.FieldDecl "Data" (go.SliceType go.byte)
                             ].

  (** Type: func(uint64) Listener *)
  Definition Listenⁱᵐᵖˡ : val :=
    λ: "e", ref (ExternalOp ListenOp "e").

  (** Type: func(uint64) (bool, Connection) *)
  Definition Connectⁱᵐᵖˡ : val :=
    λ: "e",
      let: "c" := ExternalOp ConnectOp "e" in
      let: "err" := Fst "c" in
      let: "socket" := ref (Snd "c") in
      CompositeLiteral ConnectRet (
          LiteralValue [
              KeyedElement None (ElementExpression go.bool "err");
              KeyedElement None (ElementExpression Connection "socket")
            ]
      ).

  (** Type: func(Listener) Connection *)
  Definition Acceptⁱᵐᵖˡ : val :=
    λ: "e", ref (ExternalOp AcceptOp (!"e")).

  (** Type: func(Connection, []byte) *)
  Definition Sendⁱᵐᵖˡ : val :=
    λ: "e" "m", ExternalOp SendOp (!"e", (IndexRef (go.SliceType go.byte) ("m", #(W64 0)),
                                            FuncResolve go.len [go.SliceType go.byte] "m")).

  (** Type: func(Connection) (bool, []byte) *)
  Definition Receiveⁱᵐᵖˡ : val :=
    λ: "e",
      let: "r" := ExternalOp RecvOp (!"e") in
      let: "err" := Fst "r" in
      let: "slice" := Snd "r" in
      let: "ptr" := Fst "slice" in
      let: "len" := Snd "slice" in

      CompositeLiteral ConnectRet (
          LiteralValue [
              KeyedElement None (ElementExpression go.bool "err");
              KeyedElement None
                (ElementExpression (go.SliceType go.byte) (InternalMakeSlice ("ptr", "len", "len")))
            ]
        ).


  (** FileRead pretends that the operation can never fail.
      The Go implementation will accordingly abort the program if an I/O error occurs. *)
  Definition FileReadⁱᵐᵖˡ : val :=
    λ: "f",
      let: "ret" := ExternalOp FileReadOp "f" in
      let: "err" := Fst "ret" in
      let: "slice" := Snd "ret" in
      if: "err" then AngelicExit #() else
      let: "ptr" := Fst "slice" in
      let: "len" := Snd "slice" in
      InjL ("ptr", "len", "len").

  (** FileWrite pretends that the operation can never fail.
      The Go implementation will accordingly abort the program if an I/O error occurs. *)
  Definition FileWriteⁱᵐᵖˡ : val :=
    λ: "f" "c",
      let: "err" := ExternalOp FileWriteOp ("f", (IndexRef (go.SliceType go.byte) ("c", #(W64 0)),
                                                 FuncResolve go.len [go.SliceType go.byte] "c")) in
      if: "err" then AngelicExit #() else
      #().

  (** FileAppend pretends that the operation can never fail.
      The Go implementation will accordingly abort the program if an I/O error occurs. *)
  Definition FileAppendⁱᵐᵖˡ : val :=
    λ: "f" "c",
      let: "err" := ExternalOp FileAppendOp ("f", (IndexRef (go.SliceType go.byte) ("c", #(W64 0)),
                                                 FuncResolve go.len [go.SliceType go.byte] "c")) in
      if: "err" then AngelicExit #() else
      #().

  (** Type: func() uint64 *)
  Definition GetTSCⁱᵐᵖˡ : val :=
    λ: <>, ExternalOp GetTscOp #().

  (** Type: func() (uint64, uint64) *)
  Definition GetTimeRangeⁱᵐᵖˡ : val :=
    λ: <>, ExternalOp GetTimeRangeOp #().

End grove.
