From Perennial.goose_lang Require Import lang notation.

Section goose_lang.
Context {ext:ffi_syntax}.

Definition variadic_noop : val :=
  rec: "variadic_noop" "x" :=
     (λ: "y", "variadic_noop" "y")%E.

End goose_lang.
