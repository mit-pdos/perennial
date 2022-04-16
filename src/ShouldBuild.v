(** ShouldBuild depends on everything that should be regularly compiled (by
default using make as well as in CI). *)

From Perennial.algebra Require ghost_async_map.

From Perennial.goose_lang Require
     adequacy recovery_adequacy dist_adequacy
     crash_lock
     rwlock
     rwlock_derived
     barrier
     refinement refinement_adequacy
     ffi.atomic_refinement
     logical_reln_adeq
     paper_proof
.
From Perennial.goose_lang.ffi Require async_disk async_disk_equiv.
From Perennial.program_proof Require
     lockmap_proof
     jrnl_replication.jrnl_replication_proof
     txn.twophase_refinement_thm
     simple.proofs simple.example
.

From Perennial.program_proof.examples Require
     replicated_block_proof
     all_examples
.

From Perennial.program_proof.grove_shared Require
     urpc_proof erpc_proof.

(* In-memory sharded KV system *)
From Perennial.program_proof.memkv Require
     connman_proof
     memkv_clerk_proof memkv_shard_start_proof memkv_shard_make_proof memkv_coord_make_proof
     memkv_clerk_proof
     lockservice_proof bank_proof
     closed.

(* Primary-backup replication system *)
From Perennial.program_proof.pb Require
     replica_proof.

From Goose.github_com.mit_pdos.gokv.pb Require
     controller.

From Goose.github_com.mit_pdos.gokv.fencing Require
     config ctr frontend.
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
     comments simpledb logging2 rfc1813.

(* examples goose output *)
From Goose.github_com.mit_pdos Require
     dynamic_dir.

(* interpreter semantics tests *)
From Perennial.goose_lang.interpreter Require
     generated_test.

(* ensures this file itself works for Coq's CI and catches any oversight where
something in the lite build isn't listed here *)
From Perennial Require LiteBuild.
