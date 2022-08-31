From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.mvcc Require Import mvcc_proof.

(* Core Txn machinery *)
Definition mvcc_theorems := (
	@wp_txn__DoTxn, @wp_txn__Get, @wp_txn__Put, @wp_txn__Delete,
	@wp_MkTxnMgr, @wp_txnMgr__New, @wp_txnMgr__ActivateGC
).
Print Assumptions mvcc_theorems.

