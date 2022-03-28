From Perennial.goose_lang Require Import lang notation typing.

(** We could use a dedicated opaque type but it's not really worth it...
and this one does have the right size. *)
Definition ProphIdT {ext} {ext_ty: ext_types ext} := ptrT.

Section goose_lang.
Context {ext: ffi_syntax}.

Definition NewProph : val :=
  λ: <>, NewProph.

Definition ResolveProph : val :=
  λ: "p" "val", ResolveProph (Var "p") (Var "val").

End goose_lang.

