(*
There's a universe inconsistency between diaframe and something in the memkv
closed proof. This file is a minimal way to reproduce that error, without
building other unneeded proofs in Perennial.
 *)

Set Printing Universes.

From iris.bi Require Import interface.
From diaframe Require proofmode_base.

(* this is the constraint diaframe introduces which causes the problems *)
Fail Constraint universes.Quant < universes.Logic.

From Perennial.program_proof.memkv Require Import memkv_shard_ghost_init.
(* surprisingly the Require succeeds but merely type checking this definition in the new universes fails  *)
Check shard_server_ghost_init.
(*
Error: Universe inconsistency. Cannot enforce cmra.ucmra.u0 <=
Perennial.diaframe_test.8 because Perennial.diaframe_test.8
< Perennial.diaframe_test.7 <= cmra.ucmra.u0.
*)
