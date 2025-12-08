(** ShouldBuild depends on everything that should be regularly compiled (by
default using make as well as in CI). *)

From Perennial.algebra Require ghost_async_map abs_laterable partition.

From Perennial.goose_lang Require
     adequacy recovery_adequacy dist_adequacy
     crash_lock
     rwlock
     rwlock_derived
     barrier
     refinement refinement_adequacy
     ffi.atomic_refinement
     logical_reln_adeq
     popl_submission_proofs
.

From Perennial.goose_lang.ffi Require async_disk async_disk_equiv.


From Perennial.program_proof.examples Require
     replicated_block_proof
     all_examples
.
From Perennial.program_proof.examples Require print_assumptions.

From Perennial.program_proof.grove_shared Require
     urpc_proof erpc_proof.

(* rsm *)
From Perennial.program_proof.rsm Require rsm_proof.

(* tulip *)
From Perennial.program_proof.tulip Require tulip_proof.
From Perennial.program_proof.tulip Require print_assumptions.

(*
From Perennial.goose_lang Require
     ffi.append_log_ffi.
*)
From Perennial.tutorial Require
     ipm_extensions.

(* WIP slice library *)
From Perennial.goose_lang.lib Require
     slice.pred_slice.
(* sync/atomic library (not yet used) *)
From Perennial.goose_lang.lib Require
     atomic.atomic.

(* WIP Z-based list library *)
From Perennial.Helpers Require ListZ.
(* WIP list helper library *)
From Perennial.Helpers Require ListSplice.

(* goose output *)
From Goose.github_com.goose_lang.goose.internal.examples Require
     comments simpledb logging2 rfc1813 trust_import.

(* examples goose output *)
From Goose.github_com.mit_pdos Require
     dynamic_dir.

(* interpreter semantics tests *)
From Perennial.goose_lang.interpreter Require
     generated_test.

(* ensures this file itself works for Coq's CI and catches any oversight where
something in the lite build isn't listed here *)
From Perennial Require LiteBuild.

(* Verus-related proofs *)
From Perennial.program_proof.verus Require
    wrs wrsmulti inv ucmra_cmra_adjunction.
(*
From Perennial.program_proof.verus Require
    typecast_nontermination.
*)

(** everything below is unmaintained but does build.
i.e., if it breaks in the future, we might remove it. *)

From Perennial.program_proof Require
  optional_precond spellchecker.proof bad_nil_slice bad_zero_func single.election.
From Perennial.program_logic Require simulation.
From Perennial.goose_lang.trusted.github_com.mit_pdos.gokv Require trusted_hash.
From Perennial.program_proof.tulip.paxos.invariance Require extend.
From Perennial.program_proof.tulip.program.backup Require bgpreparer_process_query_result.

From New Require should_build.
