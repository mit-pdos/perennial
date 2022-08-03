From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.mvcc Require Import mvcc_proof txn_do_txn txn_get txn_put.

(* Core Txn machinery *)
Definition mvcc_theorems := (@wp_txn__DoTxn, @wp_txn__Get, @wp_txn__Put).
Print Assumptions mvcc_theorems.

