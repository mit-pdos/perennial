From Perennial.goose_lang Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.

Definition HashLen : expr := #32.

Definition SigLen : expr := #64.

Definition Hash: val :=
  rec: "Hash" "data" :=
    Panic "ffi";;
    #().

Definition PrivateKey: ty := slice.T byteT.

Definition PublicKey: ty := slice.T byteT.

Definition GenerateKey: val :=
  rec: "GenerateKey" <> :=
    Panic "ffi";;
    #().

Definition PrivateKey__Sign: val :=
  rec: "PrivateKey__Sign" "priv" "message" :=
    Panic "ffi";;
    #().

Definition PublicKey__Verify: val :=
  rec: "PublicKey__Verify" "pub" "message" "sig" :=
    Panic "ffi";;
    #().

Definition VrfPrivateKey: ty. Admitted.

Definition VrfPublicKey: ty. Admitted.

Definition VrfGenerateKey: val :=
  rec: "VrfGenerateKey" <> :=
    Panic "ffi";;
    #().

Definition VrfPrivateKey__Hash: val :=
  rec: "VrfPrivateKey__Hash" "data" :=
    Panic "ffi";;
    #().

Definition VrfPublicKey__Verify: val :=
  rec: "VrfPublicKey__Verify" "data" "hash" "proof" :=
    Panic "ffi";;
    #().

Definition RandBytes: val :=
  rec: "RandBytes" "n" :=
    Panic "ffi";;
    #().

End code.
