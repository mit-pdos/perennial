From New.proof Require Export proof_prelude.
From Perennial.program_logic Require Export atomic_fupd.
From New Require Import disk_prelude.
From Perennial.goose_lang.ffi Require Import disk_prelude.

#[global]
Existing Instances disk_semantics disk_interp.
#[global]
Existing Instances goose_diskGS.

(* Make sure Z_scope is open. *)
Local Lemma Z_scope_test : (0%Z) + (0%Z) = 0%Z.
Proof. done. Qed.
