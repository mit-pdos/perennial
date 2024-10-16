From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.pure Require Import quorum list.
From Perennial.program_proof.tulip Require Import base.

Inductive vote :=
| Accept (p : bool)
| Reject.

Definition ballot := list vote.
