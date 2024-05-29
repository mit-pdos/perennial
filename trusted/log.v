From Perennial.goose_lang Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

Definition Printf : val := variadic_noop.
Definition Println : val := variadic_noop.

End code.
