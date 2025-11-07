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

(* TODO: awkward to construct a time.Time from trusted_code *)
Axiom arbitraryTime : val.
#[local] Definition __Time : go_type := structT [
  "wall" :: uint64T;
  "ext" :: int64T;
  "loc" :: ptrT
].

Definition Afterⁱᵐᵖˡ : val :=
  λ: "d",
    let: "ch" := chan.make #__Time #(W64 0) in
    (* delay is modeled as a no-op *)
    Fork (chan.send #__Time "ch" (arbitraryTime #()));;
    "ch".

Definition Sleepⁱᵐᵖˡ : val :=
  λ: "d", #().

End code.
End time.
