From Perennial.goose_lang Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.

Definition Conn: ty. Admitted.

Definition Dial: val :=
  rec: "Dial" "addr" :=
    Panic "ffi";;
    #().

Definition Conn__Send: val :=
  rec: "Conn__Send" "data" :=
    Panic "ffi";;
    #().

Definition Conn__Receive: val :=
  rec: "Conn__Receive" <> :=
    Panic "ffi";;
    #().

Definition Listener: ty. Admitted.

Definition Listen: val :=
  rec: "Listen" "addr" :=
    Panic "ffi";;
    #().

Definition Listener__Accept: val :=
  rec: "Listener__Accept" <> :=
    Panic "ffi";;
    #().

End code.
