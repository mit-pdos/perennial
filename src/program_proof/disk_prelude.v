From Perennial.program_logic Require Export atomic.
From Perennial.program_proof Require Export proof_prelude.
(* For backwards compat, make untyped slice lib take precedence. *)
From Perennial.goose_lang Require Export typing lib.slice.slice.

From Perennial.goose_lang Require Export ffi.disk_prelude.

(* Make sure Z_scope is open. *)
Local Lemma Z_scope_test : (0%Z) + (0%Z) = 0%Z.
Proof. done. Qed.
