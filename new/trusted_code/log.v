From New.golang Require Import defn.

Section code.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

Definition Printfⁱᵐᵖˡ : val :=
  λ: "format" "vs", #().

Definition Printlnⁱᵐᵖˡ : val :=
  λ: "vs", #().

End code.
