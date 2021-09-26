From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From Perennial.base_logic.lib Require Import wsat.
From Perennial.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export crash_lang dist_lang crash_weakestpre recovery_weakestpre.
Import uPred.

Set Default Proof Using "Type".

(*** Distributed WP ***)

Section wpd.
Context `{HI: !irisGS Λ Σ}.

Definition wpd CS (E: coPset) (ers: list node_init_cfg) :=
 ([∗ list] i↦σ ∈ ers, ∀ `(Hc: !crashGS Σ),
   |={⊤}=> ∃ (stateI : state Λ → nat → iProp Σ) (* for the initial generation *) Φ Φrx Φinv,
   let HG := GenerationGS Λ Σ Hc stateI in
   stateI σ.(init_local_state) 0 ∗
   wpr CS NotStuck HG E σ.(init_thread) σ.(init_restart) Φ Φinv Φrx)%I.

Lemma wpd_compose CS E ers1 ers2 :
  wpd CS E ers1 -∗
  wpd CS E ers2 -∗
  wpd CS E (ers1 ++ ers2).
Proof. rewrite /wpd big_sepL_app. iIntros "$ $". Qed.

End wpd.
