(** ShouldBuild depends on everything that should be regularly compiled (by
default using make as well as in CI on Travis). *)

From Perennial.goose_lang Require
     adequacy recovery_adequacy
     spec_assert
     metatheory
     refinement refinement_adequacy
     crash_lock
     logical_reln.
From Perennial.program_proof Require
     marshal_proof
     append_log_proof
     append_log_hocap
     append_log_refinement
     util_proof
     lockmap_proof
     (* temporarily disabled while wal abstraction is in flux *)
     (* wal.proof *)
     wal.specs
     wal.circular_proof
     txn.specs
     buftxn.specs.
From Perennial.goose_lang Require
     ffi.append_log_ffi.

(* goose output *)
From Perennial.goose_lang.examples Require
     goose_unittest append_log wal simpledb logging2 rfc1813.

(* goose-nfsd *)
From Goose.github_com.mit_pdos Require
     goose_nfsd.lockmap
     goose_nfsd.buf
     goose_nfsd.txn
     goose_nfsd.alloc
     goose_nfsd.buftxn
     goose_nfsd.kvs.

(* interpreter semantics tests *)
From Perennial.goose_lang.interpreter Require interpreter disk_interpreter.
(* From Perennial.goose_lang.interpreter Require
     generated_test
     disk_interpreter. *)

(* NFS spec *)
From Perennial.goose_lang.examples.nfs_spec Require
     NFS3API.
