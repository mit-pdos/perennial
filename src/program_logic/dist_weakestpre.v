From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From Perennial.base_logic.lib Require Import wsat.
From Perennial.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export crash_lang dist_lang crash_weakestpre recovery_weakestpre.
Import uPred.

Set Default Proof Using "Type".

(*** Distributed WP ***)

Class groveG (Λ : language) (CS: crash_semantics Λ) (Σ : gFunctors) := GroveG {
  grove_global_state_interp : global_state Λ → nat → fracR → coPset → list (observation Λ) → iProp Σ;
  grove_num_laters_per_step : nat → nat;
  grove_step_count_next : nat → nat;
  grove_invG :> invGS Σ;
}.

Section wpd.
Context `{gG: !groveG Λ CS Σ}.
Context `{pG: !perennialG Λ CS T Σ}.

(*
Definition equal_global_interp ct1 ct2 :=
  @global_state_interp _ _(perennial_irisG (fst ct1) (snd ct1)) =
  @global_state_interp _ _(perennial_irisG (fst ct2) (snd ct2)).
*)

Definition equal_global_inG ct : iProp Σ :=
  ⌜ @num_laters_per_step _ _(perennial_irisG (fst ct) (snd ct)) = grove_num_laters_per_step ∧
    @step_count_next _ _(perennial_irisG (fst ct) (snd ct)) = grove_step_count_next ∧
    @iris_invG _ _ (perennial_irisG (fst ct) (snd ct)) = grove_invG ⌝ ∗
  (∀ g ns mj D κs, @global_state_interp _ _(perennial_irisG (fst ct) (snd ct)) g ns mj D κs ∗-∗
               grove_global_state_interp g ns mj D κs).

Definition wpd (k : nat) (E: coPset) (cts: list (crashG Σ * pbundleG T Σ)) (ers: list (expr Λ * expr Λ)) :=
 (□ (∀ ct, ⌜ ct ∈ cts ⌝ → equal_global_inG ct) ∧
 [∗ list] i↦ct;er ∈ cts;ers, ∃ Φ Φrx Φinv, wpr NotStuck k (fst ct) (snd ct) E (fst er) (snd er) Φ Φinv Φrx)%I.

End wpd.
