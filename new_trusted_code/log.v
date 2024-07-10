From New.golang Require Import defn.

Section code.
Context `{ffi_syntax}.
Local Coercion Var' s: expr := Var s.

Definition Printf : val := variadic_noop.
Definition Println : val := variadic_noop.

End code.
