From stdpp Require Import countable.
From Perennial Require Import Helpers.CountableTactics.

Inductive Three :=
  one | two | three.

Instance Three_eq_dec : EqDecision Three.
Proof.
  solve_decision.
Qed.

Instance Three_countable : Countable Three.
Proof.
  solve_countable Three_rec 3.
Qed.

Definition Three_countable' : Countable Three.
Proof.
  solve_countable Three_rec 5.
Qed.
