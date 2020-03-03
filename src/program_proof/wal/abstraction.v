From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.

From Perennial.program_proof Require Import proof_prelude.

Module update.
  Record t :=
    mk { addr: u64;
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

  (* TODO: it would be awkward to express directly with dependent types but all
     of the operations should preserve this well-formedness invariant.

    Additionally, the state should grow monotonically: txn_disk should
    accumulate new disks (possibly overwriting the latest disk due to complete
    absorption) and installed_to and durable_to should increase.
   *)
  Definition wf (σ:t) :=
    (exists install_d,
      σ.(txn_disk) !! σ.(installed_to) = Some install_d) ∧
    (exists durable_d,
      σ.(txn_disk) !! σ.(durable_to) = Some durable_d) ∧
    (int.val σ.(installed_to) ≤ int.val σ.(durable_to)).
End log_state.

Section heap.
Context `{!heapG Σ}.
Definition update_val (up:u64*Slice.t): val :=
  (#(fst up), (slice_val (snd up), #()))%V.

Theorem update_val_t u : val_ty (update_val u) (struct.t Update.S).
Proof.
  repeat constructor.
  destruct u; rewrite /blockT; val_ty.
Qed.

(* TODO: this should probably also have a fraction *)
Definition is_block (s:Slice.t) (b:Block) :=
  is_slice_small s byteT 1 (Block_to_vals b).

Definition updates_slice (bk_s: Slice.t) (bs: list update.t): iProp Σ :=
  ∃ bks, is_slice_small bk_s (struct.t Update.S) 1 (update_val <$> bks) ∗
   [∗ list] _ ↦ b_upd;upd ∈ bks;bs , let '(update.mk a b) := upd in
                                     is_block (snd b_upd) b ∗
                                     ⌜fst b_upd = a⌝.
End heap.

Hint Resolve update_val_t : val_ty.
