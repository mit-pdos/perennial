From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From Perennial.base_logic.lib Require Import wsat.
From Perennial.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export crash_lang dist_lang crash_weakestpre recovery_weakestpre.
Import uPred.

Set Default Proof Using "Type".

(*** Distributed WP ***)
(* TODO(RJ) let us hope we do not need this any more
Class distGS (Λ : language) (CS: crash_semantics Λ) (Σ : gFunctors) := DistGS {
  grove_global_state_interp : global_state Λ → nat → fracR → coPset → list (observation Λ) → iProp Σ;
  grove_num_laters_per_step : nat → nat;
  grove_step_count_next : nat → nat;
  grove_invG :> invGS Σ;
}.
*)

Section wpd.
Context `{HI: !irisGS Λ Σ}.

(*
Definition equal_global_interp ct1 ct2 :=
  @global_state_interp _ _(perennial_irisG (fst ct1) (snd ct1)) =
  @global_state_interp _ _(perennial_irisG (fst ct2) (snd ct2)).
*)
(*
Definition equal_global_inG ct : iProp Σ :=
  ⌜ @num_laters_per_step _ _(perennial_irisG (fst ct) (snd ct)) = grove_num_laters_per_step ∧
    @step_count_next _ _(perennial_irisG (fst ct) (snd ct)) = grove_step_count_next ∧
    @iris_invGS _ _ (perennial_irisG (fst ct) (snd ct)) = grove_invG ⌝ ∗
  (∀ g ns mj D κs, @global_state_interp _ _(perennial_irisG (fst ct) (snd ct)) g ns mj D κs ∗-∗
               grove_global_state_interp g ns mj D κs).
*)

Definition wpd CS (k : nat) (E: coPset) (ers: list node_init_cfg) :=
 ([∗ list] i↦σ ∈ ers, ∀ `(Hc: !crashGS Σ),
   |={⊤}=> ∃ (stateI : state Λ → nat → iProp Σ) (* for the initial generation *) Φ Φrx Φinv,
   let HG := GenerationGS Λ Σ Hc stateI in
   stateI σ.(init_local_state) 0 ∗
   wpr CS NotStuck k HG E σ.(init_thread) σ.(init_restart) Φ Φinv Φrx)%I.

Lemma wpd_compose CS k E ers1 ers2 :
  wpd CS k E ers1 -∗
  wpd CS k E ers2 -∗
  wpd CS k E (ers1 ++ ers2).
Proof. rewrite /wpd big_sepL_app. iIntros "$ $". Qed.

End wpd.
