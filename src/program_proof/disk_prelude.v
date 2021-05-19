From Perennial.program_proof Require Export proof_prelude.
From Perennial.goose_lang Require Export ffi.disk_prelude.

(* Make sure Z_scope is open. *)
Local Lemma Z_scope_test : (0%Z) + (0%Z) = 0%Z.
Proof. done. Qed.
