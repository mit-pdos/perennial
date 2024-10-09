From Perennial.goose_lang Require Import lang notation.

Section goose_lang.
Context {ext: ffi_syntax}.

(** [Assume c] goes into an endless loop if [c] does not hold. So proofs can
assume that it holds. *)
Definition Assume: val :=
  λ: "cond", if: "cond" then #()
             else (rec: "loop" <> := "loop" #()) #().

(** [Assert c] raises UB (program gets stuck via [Panic]) if [c] does not
hold. So proofs have to show it always holds. *)
Definition Assert: val :=
  λ: "cond", if: "cond" then #()
             else Panic "assert failed".

(** [Exit n] is supposed to exit the process. We cannot directly model
this in GooseLang, so we just loop. *)
Definition Exit: val :=
  λ: <>, (rec: "loop" <> := "loop" #()) #().

End goose_lang.
