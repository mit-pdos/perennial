From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.memkv Require Import closed memkv_clerk_proof.

(* Client function wps *)
Definition client_theorems := (@wp_KVClerk__Get, @wp_KVClerk__MGet, @wp_KVClerk__Put, @wp_KVClerk__ConditionalPut).
Print Assumptions client_theorems.

(* Closed proof for shard + coord server *)
Print Assumptions closed1.shard_coord_boot.

(* Closed proof for bank boot *)
Print Assumptions closed2.bank_boot.

