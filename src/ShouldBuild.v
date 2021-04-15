(** ShouldBuild depends on everything that should be regularly compiled (by
default using make as well as in CI on Travis). *)

From Perennial.program_logic Require
     dist_lang
     distributed_weakestpre
     distributed_adequacy.
From Perennial.goose_lang Require
     adequacy recovery_adequacy distributed_adequacy
     spec_assert
     metatheory
     refinement refinement_adequacy
     crash_lock
     logical_reln_adeq.
From Perennial.program_proof Require
     wal.circ_proof_crash
     append_log_proof
     (* append_log_refinement *)
     lockmap_proof
     crash_lockmap_proof
     wal.proof
     wal.specs
     txn.txn_proof
     buftxn.buftxn_proof
     buftxn.sep_buftxn_proof buftxn.sep_buftxn_recovery_proof
     buftxn_replication.buftxn_replication_proof
     alloc.alloc_proof
     twophase.twophase_proof
     twophase.twophase_refinement_thm
     simple.proofs simple.example
     wp_to_wpc.
From Perennial.program_proof.examples Require
     all_examples.

(* TODO: refactoring in progress
From Perennial.program_proof.lockservice Require
     bank_proof incr_proof incr_proxy_proof two_pc_example. *)

From Perennial.goose_lang Require
     ffi.append_log_ffi.
From Perennial.tutorial Require
     ipm_extensions.

(* WIP slice library *)
From Perennial.goose_lang.lib Require
     slice.pred_slice.

(* WIP list algebra *)
From Perennial.algebra Require
     append_list.

(* goose output *)
From Perennial.goose_lang.examples Require
     goose_unittest simpledb logging2 rfc1813.

(* goose-nfsd *)
From Goose.github_com.mit_pdos Require
     goose_nfsd.kvs
     goose_nfsd.twophase
     goose_nfsd.simple.

(* examples goose output *)
From Goose.github_com.mit_pdos Require
     dynamic_dir.

(* interpreter semantics tests *)
From Perennial.goose_lang.interpreter Require
     interpreter
     disk_interpreter
     generated_test.

(* ensures this file itself works for Coq's CI and catches any oversight where
something in the lite build isn't listed here *)
From Perennial Require LiteBuild.
