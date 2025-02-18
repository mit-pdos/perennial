From New.golang Require Import defn.
(* From New.code_axioms Require Import log. *)

Section code.
Context `{ffi_syntax}.

Definition Printf : val := variadic_noop.
Definition Println : val := variadic_noop.

Definition initialize' : val := λ: <>, #().

End code.
