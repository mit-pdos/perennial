From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.memkv Require Import closed memkv_clerk_proof.

(* Closed proof for shard + coord server *)
Print Assumptions shard_coord_boot.

(* Client proofs -- not yet closed *)
Definition client_theorems := (@KVClerk__Get, @KVClerk__Put, @KVClerk__ConditionalPut).
Print Assumptions client_theorems.
