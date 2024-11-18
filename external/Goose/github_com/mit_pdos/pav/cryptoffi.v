From Perennial.goose_lang Require Import prelude.

Notation SigPublicKey := (slice.T byteT) (only parsing).

Section code.
Context `{ext_ty: ext_types}.

Definition HashLen : expr := #32.

Definition Hash: val :=
  rec: "Hash" "data" :=
    Panic "ffi";;
    #().

Definition SigGenerateKey: val :=
  rec: "SigGenerateKey" <> :=
    Panic "ffi";;
    #().

Definition SigPrivateKey__Sign: val :=
  rec: "SigPrivateKey__Sign" "sk" "message" :=
    Panic "ffi";;
    #().

Definition SigPublicKey__Verify: val :=
  rec: "SigPublicKey__Verify" "pk" "message" "sig" :=
    Panic "ffi";;
    #().

Definition VrfGenerateKey: val :=
  rec: "VrfGenerateKey" <> :=
    Panic "ffi";;
    #().

Definition VrfPrivateKey__Hash: val :=
  rec: "VrfPrivateKey__Hash" "sk" "data" :=
    Panic "ffi";;
    #().

Definition VrfPublicKey__Verify: val :=
  rec: "VrfPublicKey__Verify" "pk" "data" "proof" :=
    Panic "ffi";;
    #().

Definition VrfPublicKeyEncode: val :=
  rec: "VrfPublicKeyEncode" "pk" :=
    Panic "ffi";;
    #().

Definition VrfPublicKeyDecode: val :=
  rec: "VrfPublicKeyDecode" "b" :=
    Panic "ffi";;
    #().

Definition RandBytes: val :=
  rec: "RandBytes" "n" :=
    Panic "ffi";;
    #().

End code.
