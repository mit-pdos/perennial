From New.golang Require Import defn.

Module synctest.
Section code.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

Definition Runⁱᵐᵖˡ : val := λ: "f", Panic "not supported".

Definition IsInBubbleⁱᵐᵖˡ : val := λ: <>, #false.

End code.
End synctest.
