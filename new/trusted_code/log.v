From New.golang Require Import defn.

Section code.
Context `{ffi_syntax}.

Definition Printf : val :=
  λ: "format" "vs", #().
Definition Println : val :=
  λ: "vs", #().

End code.
