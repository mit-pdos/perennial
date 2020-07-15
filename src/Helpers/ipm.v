From iris.proofmode Require Export tactics.
From iris.proofmode Require Import intro_patterns.

From iris_string_ident Require Export ltac2_string_ident.

Tactic Notation "iApply" open_constr(lem) "in" constr(i) :=
  iDestruct (lem with i) as i.

(* TODO: this works, but maybe we can do better *)
Tactic Notation "iLeft" "in" constr(H) :=
  let pat := constr:(IList [[IIdent H; IDrop]]) in
  iDestruct H as pat.
Tactic Notation "iRight" "in" constr(H) :=
  let pat := constr:(IList [[IDrop; IIdent H]]) in
  iDestruct H as pat.
