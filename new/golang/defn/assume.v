From New.golang.defn Require Export exception.

Section defn.

Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

(** [assume e] goes into an infinite loop if e does not hold *)
Definition assume : val :=
  λ: "cond", if: "cond" then #() else
               (rec: "infloop" <> := "infloop" #()) #().

(** Assume "a" + "b" doesn't overflow. *)
Definition assume_sum_no_overflow : val :=
  λ: "a" "b", assume ("a" ≤⟨go.uint64⟩ #(W64 (2^64-1)) - "b");; #().

(** Assume "a" + "b" doesn't overflow and return the sum. *)
Definition sum_assume_no_overflow : val :=
  λ: "a" "b", assume_sum_no_overflow "a" "b";;
              "a" + "b".

(** Assume "x" + "y" doesn't overflow. *)
Definition assume_sum_no_overflow_signed : val :=
  λ: "x" "y",
  let: "max_int" := #(W64 (2^63-1)) in
  let: "min_int" := #(W64 (-2^63)) in
  assume (((#(W64 0) <⟨go.int⟩ "y") && ("x" <⟨go.int⟩ ("max_int"-"y"))) ||
    (("y" <⟨go.int⟩ #(W64 0)) && (("min_int"-"y") <⟨go.int⟩ "x"))).

(** Assume "x" + "y" doesn't overflow and return the sum. *)
Definition sum_assume_no_overflow_signed : val :=
  λ: "a" "b", assume_sum_no_overflow_signed "a" "b";;
              "a" + "b".

Definition mul_overflows : val :=
  λ: "a" "b", if: ("a" =⟨go.uint64⟩ #(W64 0)) || ("b" =⟨go.uint64⟩ #(W64 0)) then #false
              else "a" >⟨go.uint64⟩ #(W64 (2^64-1)) `quot` "b".

(** Assume "a" * "b" doesn't overflow (as unsigned 64-bit integers) *)
Definition assume_mul_no_overflow : val :=
  λ: "a" "b", assume (~ mul_overflows "a" "b").

End defn.
