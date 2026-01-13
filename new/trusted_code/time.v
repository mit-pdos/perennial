From New.golang Require Import defn.

Module time.
Section code.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

Definition newTimerⁱᵐᵖˡ : val :=
  λ: "when" "period" "f" "arg" "cp", #().

Definition runtimeNanoⁱᵐᵖˡ : val :=
  λ: <>, ArbitraryInt.

(* TODO: could avoid making this trusted by verifying the real implementation,
   which requires verifying `internal/godebug`. *)
Definition syncTimerⁱᵐᵖˡ : val :=
  λ: "c",
     if: ArbitraryInt =⟨go.int64⟩ #(W64 0) then "c"
     else #chan.nil.

Definition arbitraryTime: val :=
  λ: <>,
     (* generate a simple non-monotonic time without any nanoseconds and
     location of UTC *)
     let: "wall_seconds" := ArbitraryInt in
     CompositeLiteral (go.Named "time.Time"%go []) (LiteralValue [
        KeyedElement (Some $ KeyField "wall") (ElementExpression #(W64 0));
        KeyedElement (Some $ KeyField "ext") (ElementExpression "wall_seconds");
        KeyedElement (Some $ KeyField "loc") (ElementExpression #null)
     ]).

Definition Afterⁱᵐᵖˡ : val :=
  λ: "d",
    let: "ch" := FuncResolve go.make2 [(go.Named "time.Time"%go [])] #() #(W64 0) in
    (* delay is modeled as a no-op *)
    Fork (chan.send (go.Named "time.Time"%go []) "ch" (arbitraryTime #()));;
    "ch".

Definition Sleepⁱᵐᵖˡ : val :=
  λ: "d", #().

End code.
End time.
