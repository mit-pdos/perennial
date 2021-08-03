(** LiteBuild depends on a subset of Perennial that is relatively fast to check,
    for use in Coq's CI. *)

(* Some key theorems *)
From Perennial.goose_lang Require
     recovery_adequacy dist_adequacy.
(* Some core libraries *)
From Perennial.base_logic Require
     gmap_own.
(* Prelude and shared files *)
From Perennial.program_proof Require
     proof_prelude disk_prelude grove_prelude
     marshal_proof std_proof.

From Perennial.goose_lang Require
     adequacy recovery_adequacy dist_adequacy
     crash_lock
     rwlock.

(* a couple program proofs that are pretty interesting on their own and include
the wpc infrastructure *)
From Perennial.program_proof Require
     wal.circ_proof_crash.

(* Goose tests: goose_unittest has the syntactic tests while generated_test
includes running all the semantics tests *)
From Goose.github_com.tchajed.goose.internal.examples Require
     unittest.
From Perennial.goose_lang.interpreter Require
     generated_test.
