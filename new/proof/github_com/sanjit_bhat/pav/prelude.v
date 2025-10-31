(* usage: before importing this, import anything you want.
after importing this, don't import anything except "new/proof" files,
which shouldn't have side-effects (including Exports)
or unintended name shadows. *)

(* add extra dependencies. *)
From RecordUpdate Require Export RecordSet.
From iris_named_props Require Export custom_syntax.
From Perennial.Helpers Require Export bytes condition Map.
From iris.base_logic.lib Require Export mono_nat ghost_map.
From Perennial.base_logic Require Export mono_list.

(* set the right shadowed dependencies. *)
(* note: stdpp overrides some Stdlib names. *)
From stdpp Require Export prelude.
From Perennial.algebra Require Export ghost_var.

(* restore perennial's side-effects. *)
Ltac obligation_tac :=
  try
    match goal with
    | |- seal _ => eexists; reflexivity
    | _ => solve [ apply _ ]
    end.
#[global] Obligation Tactic := obligation_tac.
#[export] Set Default Goal Selector "!".
#[global] Open Scope Z_scope.
