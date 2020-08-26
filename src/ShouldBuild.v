(** ShouldBuild depends on everything that should be regularly compiled (by
default using make as well as in CI on Travis). *)

From Perennial.goose_lang Require
     adequacy recovery_adequacy
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
     wal.proof
     wal.specs
     txn.txn_proof
     buftxn.buftxn_proof
     buftxn.idealized_buftxn_spec.
From Perennial.program_proof.examples Require
     dir_proof
     single_inode_proof
     alloc_crash_proof
     indirect_inode_proof
     indirect_inode_append_proof
     replicated_block_proof
     toy_proof.
From Perennial.goose_lang Require
     ffi.append_log_ffi
     ffi.kvs_ffi.
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
     goose_nfsd.lockmap
     goose_nfsd.buf
     goose_nfsd.txn
     goose_nfsd.alloc
     goose_nfsd.buftxn
     goose_nfsd.kvs.

(* examples goose output *)
From Goose.github_com.mit_pdos Require
     async_inode
     dynamic_dir.

(* interpreter semantics tests *)
From Perennial.goose_lang.interpreter Require
     interpreter
     disk_interpreter
     generated_test.

(* NFS spec *)
From Perennial.goose_lang.examples.nfs_spec Require
     NFS3API.
