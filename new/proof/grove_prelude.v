From New.proof Require Export proof_prelude.
From Perennial.program_logic Require Export atomic_fupd.
From New Require Export grove_prelude.
From Perennial.goose_lang.ffi.grove_ffi Require Import grove_ffi.

#[global]
Existing Instances grove_semantics grove_interp.
#[global]
Existing Instances goose_groveGS goose_groveNodeGS.

(* Make sure Z_scope is open. *)
Local Lemma Z_scope_test : (0%Z) + (0%Z) = 0%Z.
Proof. done. Qed.
