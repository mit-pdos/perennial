(**
 * Common definitions used by every part of this project. Minimize this file.
 *)
From Perennial.program_proof Require Export grove_prelude.

Definition proposals := gmap nat string.
Definition ballot := list bool.
Inductive consensus : Set :=
| Chosen (v : string)
| Free.
