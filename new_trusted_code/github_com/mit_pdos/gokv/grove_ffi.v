From New.golang Require Import defn.
From Perennial.goose_lang.ffi.grove_ffi Require Export impl.

#[global]
Existing Instances grove_op grove_model.
Coercion Var' (s: string) := Var s.
(** * Grove user-facing operations. *)
Section grove.

  (** These are pointers in Go. *)
  Definition Listener : go_type := ptrT.
  Definition Connection : go_type := ptrT.
  Definition Address : go_type := uint64T.

  Definition ConnectRet := structT [
                               "Err" :: boolT;
                               "Connection" :: Connection
                             ].

  Definition ReceiveRet := structT [
                               "Err" :: boolT;
                               "Data" :: sliceT byteT
                             ].

  (** Type: func(uint64) Listener *)
  Definition Listen : val :=
    λ: "e", ExternalOp ListenOp "e".

  (** Type: func(uint64) (bool, Connection) *)
  Definition Connect : val :=
    λ: "e",
      let: "c" := ExternalOp ConnectOp "e" in
      let: "err" := Fst "c" in
      let: "socket" := Snd "c" in
      struct.make ConnectRet {[
        #(str "Err") := "err";
        #(str "Connection") := "socket"
      ]}.

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
      struct.make ReceiveRet {[
        #(str "Err") := "err";
        #(str "Data") := ("ptr", "len", "len")
      ]}.


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
      let: "err" := ExternalOp FileWriteOp ("f", (Fst $ Fst "c", Snd $ Fst "c")) in
      if: "err" then control.impl.Exit #() else
      #().

  (** FileAppend pretends that the operation can never fail.
      The Go implementation will accordingly abort the program if an I/O error occurs. *)
  Definition FileAppend : val :=
    λ: "f" "c",
      let: "err" := ExternalOp FileAppendOp ("f", (Fst $ Fst "c", Snd $ Fst "c")) in
      if: "err" then control.impl.Exit #() else
      #().

  (** Type: func() uint64 *)
  Definition GetTSC : val :=
    λ: <>, ExternalOp GetTscOp #().

  (** Type: func() (uint64, uint64) *)
  Definition GetTimeRange : val :=
    λ: <>, ExternalOp GetTimeRangeOp #().

End grove.
