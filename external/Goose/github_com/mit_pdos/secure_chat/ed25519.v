From Perennial.goose_lang Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

Definition PrivateKey: ty := slice.T byteT.
Definition PublicKey: ty := slice.T byteT.
End code.
