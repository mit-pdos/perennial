(**
 * Common definitions used by every part of this project. Minimize this file.
 *)
From Perennial.program_proof Require Export grove_prelude.

Inductive proposal : Set :=
| Any
| Proposed (v : string).
Definition proposals := gmap nat proposal.

Inductive vote : Set :=
| Reject
| CAccept
| FAccept (v : string).
Definition ballot := list vote.

#[global]
Instance vote_eq_decision :
  EqDecision vote.
Proof. solve_decision. Qed.

Inductive consensus : Set :=
| Chosen (v : string)
| Free.

Definition prefixes `{Countable A} {B : Type} (lbs ls : gmap A (list B)) :=
  ∀ x lb l, lbs !! x = Some lb -> ls !! x = Some l -> prefix lb l.
