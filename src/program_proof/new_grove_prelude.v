From Perennial.program_logic Require Export atomic_fupd.
From Perennial.program_proof Require Export new_proof_prelude.
From Perennial.new_goose_lang Require Export ffi.grove_prelude.
From Perennial.program_proof Require Export grove_ffi.proof.
From Perennial.goose_lang.ffi.grove_ffi Require Import grove_ffi.

#[global]
Existing Instances grove_semantics grove_interp.
#[global]
Existing Instances goose_groveGS goose_groveNodeGS.

(* Make sure Z_scope is open. *)
Local Lemma Z_scope_test : (0%Z) + (0%Z) = 0%Z.
Proof. done. Qed.
