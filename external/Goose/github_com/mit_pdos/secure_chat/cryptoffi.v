From Perennial.goose_lang Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

Definition Sig: ty := slice.T byteT.

Definition HashLen : expr := #32.

Definition SigLen : expr := #64.

Definition Hash: val :=
  rec: "Hash" "data" :=
    Panic "shim";;
    #().

Definition SignerT := struct.decl [
].

Definition VerifierT := struct.decl [
].

Definition MakeKeys: val :=
  rec: "MakeKeys" <> :=
    Panic "shim";;
    #().

Definition Sign: val :=
  rec: "Sign" "sk" "data" :=
    Panic "shim";;
    #().

Definition Verify: val :=
  rec: "Verify" "vk" "data" "sig" :=
    Panic "shim";;
    #().

End code.
