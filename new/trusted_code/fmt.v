From New.golang Require Export defn.
(* From New.code_axioms Require Import fmt. *)

Section code.
Context `{ffi_syntax}.

(* FIXME: Returns some stuff *)
Definition Printⁱᵐᵖˡ : val :=
  λ: "format" "a",
    Panic "unimplemented".

(* FIXME: Returns some stuff *)
Definition Printfⁱᵐᵖˡ : val :=
  λ: "a",
    Panic "unimplemented".

End code.
