From New.golang Require Import defn.

Module time.
Section code.
Context `{ffi_syntax}.

Definition newTimerⁱᵐᵖˡ : val :=
  λ: "when" "period" "f" "arg" "cp", #().

Definition runtimeNanoⁱᵐᵖˡ : val :=
  λ: <>, ArbitraryInt.

(* TODO: could avoid making this trusted by verifying the real implementation,
   which requires verifying `internal/godebug`. *)
Definition syncTimerⁱᵐᵖˡ : val :=
  λ: "c",
     if: ArbitraryInt = #(W64 0) then "c"
     else #chan.nil.

Axiom Afterⁱᵐᵖˡ : val.

End code.
End time.
