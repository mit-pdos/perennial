From New.golang.defn Require Import pre lock.

Module primitive.
Section code.
  Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

  (** [Assume c] goes into an endless loop if [c] does not hold. So proofs can
assume that it holds. *)
  Definition Assumeⁱᵐᵖˡ : val :=
    λ: "cond", if: Var "cond" then #()
               else (rec: "loop" <> := Var "loop" #()) #().

  (** [Assert c] raises UB (program gets stuck via [Panic]) if [c] does not
hold. So proofs have to show it always holds. *)
  Definition Assertⁱᵐᵖˡ : val :=
    λ: "cond", if: Var "cond" then #()
               else Panic "assert failed".

  (** [Exit n] is supposed to exit the process. We cannot directly model
this in GooseLang, so we just loop. *)
  Definition Exitⁱᵐᵖˡ : val :=
    λ: <>, (rec: "loop" <> := Var "loop" #()) #().

  Definition Millisecond: val := #(W64 1000000).
  Definition Second: val := #(W64 1000000000).

  Definition Sleepⁱᵐᵖˡ : val := λ: "duration", #().

  Definition TimeNowⁱᵐᵖˡ : val := λ: <>, ArbitraryInt.

  Definition AfterFuncⁱᵐᵖˡ : val := λ: "duration" "f", Fork "f" ;; Alloc "f".

  Definition RandomUint64ⁱᵐᵖˡ : val := λ: <>, ArbitraryInt.

  Definition NewProphⁱᵐᵖˡ : val := λ: <>, goose_lang.NewProph.

  Definition ResolveProphⁱᵐᵖˡ : val := λ: "p" "val", goose_lang.ResolveProph (Var "p") (Var "val").

  Definition Linearizeⁱᵐᵖˡ : val := λ: <>, #().

  Definition Mutexⁱᵐᵖˡ := go.bool.

  Definition Mutex := go.Named "github.com/goose-lang/primitive.Mutex"%go [].

  Definition Mutex__Lockⁱᵐᵖˡ : val :=
    λ: "m" <>, lock.lock "m".

  Definition Mutex__Unlockⁱᵐᵖˡ : val :=
    λ: "m" <>, lock.unlock "m".

  Definition ProphIdⁱᵐᵖˡ := go.proph_id.

End code.

Module Mutex. Definition t := bool. End Mutex.
Module ProphId. Definition t := proph_id. End ProphId.

End primitive.
