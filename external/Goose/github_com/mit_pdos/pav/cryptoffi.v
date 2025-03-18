From Perennial.goose_lang Require Import prelude.

Notation SigPublicKey := (slice.T byteT) (only parsing).

Section code.
Context `{ext_ty: ext_types}.

(* Hash. *)

Definition HashLen : expr := #32.

Definition NewHasher: val :=
  rec: "NewHasher" <> :=
    Panic "ffi".

Definition Hasher__Write: val :=
  rec: "Hasher__Write" "ptr_hr" "sl_b" :=
    Panic "ffi".

Definition Hasher__Sum: val :=
  rec: "Hasher__Sum" "ptr_hr" "sl_b" :=
    Panic "ffi".

(* Signature. *)

Definition SigGenerateKey: val :=
  rec: "SigGenerateKey" <> :=
    Panic "ffi".

Definition SigPrivateKey__Sign: val :=
  rec: "SigPrivateKey__Sign" "sk" "message" :=
    Panic "ffi".

Definition SigPublicKey__Verify: val :=
  rec: "SigPublicKey__Verify" "pk" "message" "sig" :=
    Panic "ffi".

(* Verifiable Random Function (VRF). *)

Definition VrfGenerateKey: val :=
  rec: "VrfGenerateKey" <> :=
    Panic "ffi".

Definition VrfPrivateKey__Prove: val :=
  rec: "VrfPrivateKey__Prove" "sk" "data" :=
    Panic "ffi".

Definition VrfPublicKey__Verify: val :=
  rec: "VrfPublicKey__Verify" "pk" "data" "proof" :=
    Panic "ffi".

Definition VrfPublicKeyEncode: val :=
  rec: "VrfPublicKeyEncode" "pk" :=
    Panic "ffi".

Definition VrfPublicKeyDecode: val :=
  rec: "VrfPublicKeyDecode" "b" :=
    Panic "ffi".

(* Random. *)

Definition RandBytes: val :=
  rec: "RandBytes" "n" :=
    Panic "ffi".

End code.
