(** ShouldBuild depends on everything that should be regularly compiled (by
default using make as well as in CI). *)

(*
From Perennial.program_logic Require
     dist_weakestpre
     dist_adequacy.  *)
From Perennial.goose_lang Require
     adequacy recovery_adequacy (* dist_adequacy *)
     crash_lock
     rwlock
     barrier
     refinement refinement_adequacy
     logical_reln_adeq.
From Perennial.program_proof Require
     wal.circ_proof_crash
(*
     append_log_proof
     (* append_log_refinement *)
*)
     lockmap_proof
     crash_lockmap_proof
     wal.proof
     obj.obj_proof
     jrnl.jrnl_proof
     jrnl.sep_jrnl_recovery_proof
     jrnl_replication.jrnl_replication_proof
     txn.twophase_refinement_thm
     simple.proofs simple.example
     wp_to_wpc
.

(*
From Perennial.program_proof.examples Require
     all_examples.
*)

(* TODO: refactoring in progress
From Perennial.program_proof.lockservice Require
     bank_proof incr_proof incr_proxy_proof two_pc_example. *)

(* In-memory sharded KV system *)
From Perennial.program_proof.memkv Require
     rpc_proof
     memkv_clerk_proof memkv_shard_start_proof memkv_shard_make_proof memkv_coord_make_proof
     closed.

(*
From Perennial.goose_lang Require
     ffi.append_log_ffi.
*)
From Perennial.tutorial Require
     ipm_extensions.

(* WIP slice library *)
From Perennial.goose_lang.lib Require
     slice.pred_slice.

(* goose output *)
From Goose.github_com.tchajed.goose.internal.examples Require
     semantics unittest comments simpledb logging2 rfc1813.

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
(*
From Perennial Require LiteBuild.
*)
