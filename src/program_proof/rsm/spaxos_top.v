(**
 * Common definitions used by every part of this project. Minimize this file.
 *)
From Perennial.program_proof Require Export grove_prelude.
From Perennial.program_logic Require Export atomic. (* prefer the ncfupd atomics *)

Definition proposals := gmap nat byte_string.
Definition ballot := list bool.
Inductive consensus : Type :=
| Chosen (v : byte_string)
| Free.

Definition prefixes `{Countable A} {B : Type} (lbs ls : gmap A (list B)) :=
  ∀ x lb l, lbs !! x = Some lb -> ls !! x = Some l -> prefix lb l.
