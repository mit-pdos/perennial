From New.golang Require Import defn.

Module synctest.
Section code.
Context `{ffi_syntax}.

Definition Runⁱᵐᵖˡ : val := λ: "f", Panic "not supported".

Definition IsInBubbleⁱᵐᵖˡ : val := λ: <>, #false.

End code.
End synctest.
