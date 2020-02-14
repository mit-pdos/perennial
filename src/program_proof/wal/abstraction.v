From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.program_proof Require Import proof_prelude.

Module update.
  Record t :=
    { addr: u64;
      b: Block; }.
End update.

Definition disk := gmap Z Block.

Module log_state.
  Record t :=
    mk { (* tracks the disk corresponding to each LogPosition (the identifiers
    handed out by MemAppend) *)
        txn_disk: gmap u64 disk;
        (* installed_to promises what will be read after a cache miss *)
        installed_to: u64;
        (* durable_to promises what will be on-disk after a crash *)
        durable_to: u64;
      }.
  Global Instance _eta: Settable _ := settable! mk <txn_disk; installed_to; durable_to>.
End log_state.
