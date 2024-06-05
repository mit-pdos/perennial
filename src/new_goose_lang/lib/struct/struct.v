From iris.proofmode Require Import coq_tactics reduction.
From Perennial.base_logic.lib Require Import invariants.
From Perennial.goose_lang Require Import proofmode.
From Perennial.new_goose_lang.lib Require Export typed_mem struct.impl.
From Perennial.Helpers Require Import NamedProps.

Local Close Scope struct_scope.

Reserved Notation "l ↦[ d :: f ] dq v"
    (at level 20, dq custom dfrac at level 1, d at level 50, f at level 50,
       format "l  ↦[ d :: f ] dq  v").
