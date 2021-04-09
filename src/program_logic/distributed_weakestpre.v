From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From Perennial.base_logic.lib Require Import wsat.
From Perennial.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export crash_lang dist_lang crash_weakestpre recovery_weakestpre.
Import uPred.

Set Default Proof Using "Type".

(*** Distributed WP ***)

Class groveG (Λ : language) (CS: crash_semantics Λ) (Σ : gFunctors) := GroveG {
  grove_global_state_interp : global_state Λ → nat → list (observation Λ) → iProp Σ;
  grove_num_laters_per_step : nat → nat;
  grove_invG :> invG Σ;
}.

Section wpd.
Context `{gG: !groveG Λ CS Σ}.
Context `{pG: !perennialG Λ CS T Σ}.

(*
Definition equal_global_interp ct1 ct2 :=
  @global_state_interp _ _(perennial_irisG (fst ct1) (snd ct1)) =
  @global_state_interp _ _(perennial_irisG (fst ct2) (snd ct2)).
*)

Definition equal_global_inG ct :=
  @global_state_interp _ _(perennial_irisG (fst ct) (snd ct)) = grove_global_state_interp ∧
  @num_laters_per_step _ _(perennial_irisG (fst ct) (snd ct)) = grove_num_laters_per_step ∧
  @iris_invG _ _ (perennial_irisG (fst ct) (snd ct)) = grove_invG.

Definition wpd (k : nat) (E: coPset) (cts: list (crashG Σ * pbundleG T Σ)) (es: list (expr Λ)) :=
 (⌜ ∀ ct, ct ∈ cts → equal_global_inG ct ⌝ ∧
 [∗ list] i↦ct;e ∈ cts;es, ∃ Φ Φrx Φinv, wpr NotStuck k (fst ct) (snd ct) E e e Φ Φinv Φrx)%I.

End wpd.
