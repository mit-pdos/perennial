From Perennial.goose_lang Require Import lang notation typing.

Definition ProphIdT {ext} {ext_ty: ext_types ext} := prophT.

Section goose_lang.
Context {ext: ffi_syntax}.

Definition NewProph : val :=
  λ: <>, NewProph.

Definition ResolveProph : val :=
  λ: "p" "val", ResolveProph (Var "p") (Var "val").

End goose_lang.

