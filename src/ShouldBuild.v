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
     popl_submission_proofs
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

(* Epoch-fencing examples *)
From Perennial.program_proof.fencing Require
     config_proof ctr_proof frontend_proof.
From Perennial.program_proof.ctrexample Require
     client server closed.

(* Append-only file library *)
From Perennial.program_proof.aof Require proof.

(* vrsm *)
From Perennial.program_proof.vrsm Require
     reconfig.proof vkv.kv_proof closed_proof.

(* MVCC *)
From Perennial.program_proof.mvcc Require mvcc_proof.

(* rsm *)
From Perennial.program_proof.rsm Require rsm_proof.

(* tulip *)
From Perennial.program_proof.tulip Require tulip_proof.

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

(* lease examples *)
From Perennial.program_proof.minlease Require proof.

(* Grove tutorial *)
From Perennial.program_proof.tutorial Require
     basics.proof
     queue.proof
     kvservice.proof
     kvservice.full_proof.

From Perennial.program_proof.cachekv Require proof.

From New.code.go_etcd_io.raft Require v3.
From New.proof Require asyncfile etcdraft.

From New.code.github_com.goose_lang.goose.testdata.examples Require unittest semantics.

(* FIXME: add back in. *)
(* From Perennial.program_proof.pav Require should_build. *)
