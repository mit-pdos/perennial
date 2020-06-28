From iris.proofmode Require Import tactics.

(* TODO: move iLeft and iRight here *)

Tactic Notation "iApply" open_constr(lem) "in" constr(i) :=
  iDestruct (lem with i) as i.
