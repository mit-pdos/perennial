From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic.lib Require Import wsat.
From iris.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export crash_lang.

(* Weakest pre-condition with a crash invariant. *)
Definition wp_crash `{!irisG Λ Σ} s E e Φ Φinv :=
  (WP e @ s ; E {{ Φ }} ∗
  (∀ σ κs n, state_interp σ κs n ={⊤,∅}=∗ Φinv σ))%I.

Definition recv_idemp Σ {Λ CS} `{!invPreG Σ} s (rec: expr Λ) φinv φrec :=
  (□ (∀ `{Hinv : invG Σ} σ1 σ1' κs (Hcrash: crash_prim_step CS σ1 σ1'),
        (φinv σ1 ={⊤}=∗
           ∃ (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
             (fork_post : val Λ → iProp Σ),
             let _ : irisG Λ Σ := IrisG _ _ Hinv stateI fork_post in
             stateI σ1' κs 0 ∗
             wp_crash s ⊤ rec (λ _, ∀ σ n, stateI σ [] n ={⊤, ∅}=∗ φrec σ ) φinv)))%I.
