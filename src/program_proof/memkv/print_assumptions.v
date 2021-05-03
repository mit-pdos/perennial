From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.memkv Require Import closed memkv_clerk_proof.

(* Closed proof for shard server *)
Print Assumptions shard_boot1.

(* Client proofs -- not yet closed *)
Definition client_theorems := (@KVClerk__Get, @KVClerk__Put, @KVClerk__ConditionalPut).
Print Assumptions client_theorems.
