(**
 * Common definitions used by every part of this project. Minimize this file.
 *)
From Perennial.program_proof Require Export grove_prelude.

Inductive proposal : Type :=
| Any
| Proposed (v : byte_string).
Definition proposals := gmap nat proposal.

Inductive vote : Type :=
| Reject
| CAccept
| FAccept (v : byte_string).
Definition ballot := list vote.

#[global]
Instance vote_eq_decision :
  EqDecision vote.
Proof. solve_decision. Qed.

Inductive consensus : Type :=
| Chosen (v : byte_string)
| Free.

Definition prefixes `{Countable A} {B : Type} (lbs ls : gmap A (list B)) :=
  ∀ x lb l, lbs !! x = Some lb -> ls !! x = Some l -> prefix lb l.
