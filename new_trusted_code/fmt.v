From New.golang Require Export defn.

Section code.
Context `{ffi_syntax}.

Definition Print : val := variadic_noop.
Definition Printf : val := variadic_noop.

End code.
