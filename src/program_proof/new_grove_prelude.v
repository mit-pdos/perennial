From Perennial.program_logic Require Export atomic_fupd.
From Perennial.program_proof Require Export new_proof_prelude.
From Perennial.goose_lang Require Export ffi.grove_prelude.
From Perennial.program_proof Require Export grove_ffi.proof.

(* Make sure Z_scope is open. *)
Local Lemma Z_scope_test : (0%Z) + (0%Z) = 0%Z.
Proof. done. Qed.
