(* Common setup for all of Perennial. Similar to stdpp and iris's options.v
files. *)

From Coq Require Import ZArith.
From stdpp Require Export base tactics.

Notation "'sealed' x" := (unseal (_ : seal x)) (at level 200, only parsing).

(** Override stdpp's setting of Program's Obligation Tactic to [id]. *)
(* this Ltac is here to support rebinding, if needed *)
Ltac obligation_tac :=
  try
    match goal with
    | |- seal _ => eexists; reflexivity
    | _ => solve [ apply _ ]
    end.

#[global]
Obligation Tactic := obligation_tac.

Module test_obligation_tactic.
  Definition foo_def := 3.
  Program Definition foo := sealed foo_def.
  (* should not create any obligations *)
  Definition foo_unseal : foo = _ := seal_eq _.
End test_obligation_tactic.

#[export] Set Default Goal Selector "!".
(* cannot be export *)
#[global] Open Scope Z_scope.
