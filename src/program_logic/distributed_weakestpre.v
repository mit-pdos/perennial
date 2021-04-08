From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From Perennial.base_logic.lib Require Import wsat.
From Perennial.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export crash_lang crash_weakestpre recovery_weakestpre.
Import uPred.

Set Default Proof Using "Type".

(*** Distributed WP ***)

Section wpd.
Context `{pG: !perennialG Λ CS T Σ}.

Definition equal_global_interp ct1 ct2 :=
  @global_state_interp _ _(perennial_irisG (fst ct1) (snd ct1)) =
  @global_state_interp _ _(perennial_irisG (fst ct2) (snd ct2)).

(* maybe the global interp should be a parameter that they are all equal to,
   rather than saying they're all equal? *)
Definition wpd (k : nat) (E: coPset) (cts: list (crashG Σ * pbundleG T Σ)) (es: list (expr Λ)) :=
 (⌜ ∀ ct1 ct2, ct1 ∈ cts → ct2 ∈ cts → equal_global_interp ct1 ct2 ⌝ ∧
 [∗ list] i↦ct;e ∈ cts;es, ∃ Φ Φrx Φinv, wpr NotStuck k (fst ct) (snd ct) E e e Φ Φinv Φrx)%I.

End wpd.
