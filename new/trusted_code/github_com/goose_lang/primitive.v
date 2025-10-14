From New.code Require Import sync.
From New.golang.defn Require Import core slice lock.

Module primitive.
Module prophId. Definition id : go_string := "github.com/goose-lang/goose.prophId". End prophId.
Section code.
  Context `{ffi_syntax}.

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

  Definition UInt64Putⁱᵐᵖˡ : val :=
    λ: "p" "n",
      exception_do (
      do: (slice.elem_ref #uint8T "p" #(W64 0)) <-[#uint8T] to_u8 ("n" ≫ #(W64 (0*8)));;;
      do: (slice.elem_ref #uint8T "p" #(W64 1)) <-[#uint8T] to_u8 ("n" ≫ #(W64 (1*8)));;;
      do: (slice.elem_ref #uint8T "p" #(W64 2)) <-[#uint8T] to_u8 ("n" ≫ #(W64 (2*8)));;;
      do: (slice.elem_ref #uint8T "p" #(W64 3)) <-[#uint8T] to_u8 ("n" ≫ #(W64 (3*8)));;;
      do: (slice.elem_ref #uint8T "p" #(W64 4)) <-[#uint8T] to_u8 ("n" ≫ #(W64 (4*8)));;;
      do: (slice.elem_ref #uint8T "p" #(W64 5)) <-[#uint8T] to_u8 ("n" ≫ #(W64 (5*8)));;;
      do: (slice.elem_ref #uint8T "p" #(W64 6)) <-[#uint8T] to_u8 ("n" ≫ #(W64 (6*8)));;;
      do: (slice.elem_ref #uint8T "p" #(W64 7)) <-[#uint8T] to_u8 ("n" ≫ #(W64 (7*8)))).

  Definition UInt64Getⁱᵐᵖˡ : val := λ: "p",
      let: "v0" := to_u64 ![#uint8T](slice.elem_ref #uint8T "p" #(W64 0)) in
      let: "v1" := to_u64 ![#uint8T](slice.elem_ref #uint8T "p" #(W64 1)) in
      let: "v2" := to_u64 ![#uint8T](slice.elem_ref #uint8T "p" #(W64 2)) in
      let: "v3" := to_u64 ![#uint8T](slice.elem_ref #uint8T "p" #(W64 3)) in
      let: "v4" := to_u64 ![#uint8T](slice.elem_ref #uint8T "p" #(W64 4)) in
      let: "v5" := to_u64 ![#uint8T](slice.elem_ref #uint8T "p" #(W64 5)) in
      let: "v6" := to_u64 ![#uint8T](slice.elem_ref #uint8T "p" #(W64 6)) in
      let: "v7" := to_u64 ![#uint8T](slice.elem_ref #uint8T "p" #(W64 7)) in
      "v0" `or` ("v1" `or` ("v2" `or` ("v3" `or` ("v4" `or` ("v5" `or` ("v6" `or` "v7"
          ≪ #(W64 8)) ≪ #(W64 8)) ≪ #(W64 8)) ≪ #(W64 8)) ≪ #(W64 8)) ≪ #(W64 8)) ≪ #(W64 8).

  Definition UInt32Putⁱᵐᵖˡ : val :=
    λ: "p" "n",
      exception_do (
      do: (slice.elem_ref #uint8T "p" #(W64 0)) <-[#uint8T] to_u8 ("n" ≫ #(W32 (0*8)));;;
      do: (slice.elem_ref #uint8T "p" #(W64 1)) <-[#uint8T] to_u8 ("n" ≫ #(W32 (1*8)));;;
      do: (slice.elem_ref #uint8T "p" #(W64 2)) <-[#uint8T] to_u8 ("n" ≫ #(W32 (2*8)));;;
      do: (slice.elem_ref #uint8T "p" #(W64 3)) <-[#uint8T] to_u8 ("n" ≫ #(W32 (3*8)))).

  Definition UInt32Getⁱᵐᵖˡ : val := λ: "p",
      let: "v0" := to_u32 ![#uint8T](slice.elem_ref #uint8T "p" #(W64 0)) in
      let: "v1" := to_u32 ![#uint8T](slice.elem_ref #uint8T "p" #(W64 1)) in
      let: "v2" := to_u32 ![#uint8T](slice.elem_ref #uint8T "p" #(W64 2)) in
      let: "v3" := to_u32 ![#uint8T](slice.elem_ref #uint8T "p" #(W64 3)) in
      "v0" `or` ("v1" `or` ("v2" `or` ("v3" ≪ #(W32 8)) ≪ #(W32 8)) ≪ #(W32 8)) ≪ #(W32 8).

  Definition Millisecond: val := #(W64 1000000).
  Definition Second: val := #(W64 1000000000).

  Definition Sleepⁱᵐᵖˡ : val := λ: "duration", #().

  Definition TimeNowⁱᵐᵖˡ : val := λ: <>, ArbitraryInt.

  Definition AfterFuncⁱᵐᵖˡ : val := λ: "duration" "f", Fork "f" ;; ref "f".

  Definition WaitTimeoutⁱᵐᵖˡ : val := λ: "l" "timeout",
      method_call #sync #"Cond" "Wait" "l".

  Definition RandomUint64ⁱᵐᵖˡ : val := λ: <>, ArbitraryInt.

  Definition NewProphⁱᵐᵖˡ : val := λ: <>, goose_lang.NewProph.

  Definition ResolveProphⁱᵐᵖˡ : val := λ: "p" "val", goose_lang.ResolveProph (Var "p") (Var "val").

  Definition Linearizeⁱᵐᵖˡ : val := λ: <>, #().

  Definition AssumeNoStringOverflowⁱᵐᵖˡ : val :=
    λ: "s", assume.assume (IsNoStringOverflow "s").

  Definition Mutex := boolT.

  Definition Mutex__Lockⁱᵐᵖˡ : val :=
    λ: "m" <>, lock.lock "m".

  Definition Mutex__Unlockⁱᵐᵖˡ : val :=
    λ: "m" <>, lock.unlock "m".

End code.
End primitive.
