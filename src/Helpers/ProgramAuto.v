From Coq.Program Require Import Tactics.
From stdpp Require Import base.

(* this Ltac is here to support rebinding, if needed *)
Ltac obligation_tac :=
  try
    match goal with
    | |- seal _ => eexists; reflexivity
    | _ => solve [ apply _ ]
    end.

#[global,export]
Obligation Tactic := obligation_tac.

#[global]
Unset Transparent Obligations.

Module test.
  Definition foo_def := 3.
  Program Definition foo := unseal (_:seal (@foo_def)).
  (* should not create any obligations *)
  Definition foo_unseal : foo = _ := seal_eq _.
End test.
