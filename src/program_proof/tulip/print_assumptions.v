From Perennial.program_proof.tulip Require Import tulip_proof.

(* Interface of tulip *)
Definition tulip_theorems := (
	@wp_mkTxn, @wp_Txn__Run, @wp_Txn__Read, @wp_Txn__Write, @wp_Txn__Delete,
	@wp_start
).
Print Assumptions tulip_theorems.

(* Closed proofs *)
(* Print Assumptions closed_proof.hello_adequate. *)
