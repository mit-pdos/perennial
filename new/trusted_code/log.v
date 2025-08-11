From New.golang Require Import defn.

Section code.
Context `{ffi_syntax}.

Definition Printfⁱᵐᵖˡ : val :=
  λ: "format" "vs", #().

Definition Printlnⁱᵐᵖˡ : val :=
  λ: "vs", #().

End code.
