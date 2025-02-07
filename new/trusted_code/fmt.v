From New.golang Require Export defn.
(* From New.code_axioms Require Import fmt. *)

Section code.
Context `{ffi_syntax}.

Definition Print : val := variadic_noop.
Definition Printf : val := variadic_noop.

Definition initialize' : val := λ: <>, #().

End code.
