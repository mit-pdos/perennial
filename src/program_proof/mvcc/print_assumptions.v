From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.mvcc Require Import mvcc_proof examples_hello.

(* Core Txn machinery *)
Definition mvcc_theorems := (
	@wp_txn__Run, @wp_txn__Read, @wp_txn__Write, @wp_txn__Delete,
	@wp_MkDB, @wp_DB__NewTxn, @wp_DB__ActivateGC
).
Print Assumptions mvcc_theorems.

(* Closed proofs *)
Print Assumptions closed_proof.hello_adequate.
