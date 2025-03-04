From Perennial.goose_lang Require Import notation.
From New.golang.theory Require Import proofmode globals init.

(* TODO: iFrame # is only for backwards compatibility *)
Tactic Notation "wp_globals_get" :=
  wp_globals_get_core; try iPkgInit; try iFrame "#".
Tactic Notation "wp_func_call" :=
  wp_func_call_core; try iPkgInit; try iFrame "#".
Tactic Notation "wp_method_call" :=
  wp_method_call_core; try iPkgInit; try iFrame "#".

Tactic Notation "wp_apply" open_constr(lem) :=
  wp_apply_core lem; try iPkgInit.
