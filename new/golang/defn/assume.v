From New Require Export notation.
From New.golang.defn Require Import exception.
From Perennial Require Import base.

Section defn.

Context `{!ffi_syntax}.

(** [assume e] goes into an infinite loop if e does not hold *)
Definition assume : val :=
  λ: "cond", if: "cond" then #() else
               (rec: "infloop" <> := "infloop" #()) #().

(** Assume "a" + "b" doesn't overflow. *)
Definition assume_sum_no_overflow : val :=
  λ: "a" "b", assume ("a" ≤ #(W64 (2^64-1)) - "b");; #().

(** Assume "a" + "b" doesn't overflow and return the sum. *)
Definition sum_assume_no_overflow : val :=
  λ: "a" "b", assume_sum_no_overflow "a" "b";;
              "a" + "b".

End defn.
