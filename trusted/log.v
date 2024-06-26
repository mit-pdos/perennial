From Perennial.new_goose_lang Require Import prelude.

Section code.
Context `{ffi_syntax}.
Local Coercion Var' s: expr := Var s.

Definition Printf : val := variadic_noop.
Definition Println : val := variadic_noop.

End code.
