From New.golang Require Import defn.

Section code.
Context `{ffi_syntax}.

Definition Printf : val := variadic_noop.
Definition Println : val := variadic_noop.

End code.
