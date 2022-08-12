From Perennial.program_proof Require Export proof_prelude.
(* For backwards compat, make untyped slice lib take precedence. *)
From Perennial.goose_lang.lib Require Export slice.

From Perennial.goose_lang Require Export ffi.async_disk_prelude.

(* Make sure Z_scope is open. *)
Local Lemma Z_scope_test : (0%Z) + (0%Z) = 0%Z.
Proof. done. Qed.


