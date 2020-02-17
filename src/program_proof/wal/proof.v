From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import wal.abstraction.
From Perennial.program_proof Require Import wal.circular_proof.

Definition LogPositionT := wal.LogPosition.
Definition LogPosition := u64.
Definition LogDiskBlocks := 513.

Class ToVal {ext:ext_op} {ext_ty: ext_types ext} T (t: @ty val_tys) :=
  { to_val : T → val;
    to_val_ty : forall x, val_ty (to_val x) t;
  }.

Transparent slice.T.

Module WalogM.
  Record t :=
    mk { memLock: loc;
         d: Disk_ty;
         circ: loc;

         (* these are condition variables and behave like indirect access to
         memLock *)
         condLogger: loc;
         condInstall: loc;

         memLog: Slice.t; (* size 2 *)
         memStart: LogPosition;
         nextDiskEnd: LogPosition;

         (* these have no bearing on the abstraction relation *)
         shutdown: bool;
         nthread: u64;
         condShut: loc;

         memLogMap: loc;
       }.

  Instance t_val : ToVal t (struct.t Walog.S).
  refine {| to_val x :=
              (#x.(memLock), ExtV DiskInterfaceVal, #x.(circ),
               #x.(condLogger), #x.(condInstall),
               slice_val x.(memLog), #(LitInt x.(memStart)), #(LitInt x.(nextDiskEnd)),
               #x.(shutdown), #x.(nthread), #x.(condShut),
               #x.(memLogMap))%V |}.
  intros []; simpl.
  repeat constructor; simpl.
  { rewrite /Disk.
    exact (ext_def_ty DiskInterfaceTy). }
  Defined.
End WalogM.

Section heap.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Implicit Types (Φ: val → iProp Σ).
Implicit Types (v:val) (z:Z).

Theorem post_upto_intval Φ (x1 x2: u64) :
  int.val x1 = int.val x2 →
  Φ #x1 -∗ Φ #x2.
Proof.
  iIntros (Heq%word.unsigned_inj) "HΦ".
  subst; auto.
Qed.

Theorem LogDiskBlocks_ok Φ :
  Φ #LogDiskBlocks -∗ WP LOGDISKBLOCKS {{ Φ }}.
Proof.
  iIntros "HΦ".
  rewrite /LOGDISKBLOCKS /HDRADDRS.
  wp_pures.
  iApply "HΦ".
Qed.

Definition apply_update (u: update.t) : disk → disk :=
  <[int.val u.(update.addr) := u.(update.b)]>.

Definition apply_updates (us: list update.t) (d:disk): disk :=
  foldr apply_update d us.

Definition take_updates (from to : u64) (log: list update.t) (logStart: u64) : list update.t :=
  let start := (int.nat from - int.nat logStart)%nat in
  let num := (int.nat to - int.nat from)%nat in
  take num (drop start log).

Definition lockInv (l: loc) (σ: log_state.t): iProp Σ :=
  (∃ memLog diskLog
     (memStart: u64) (diskStart: u64) (nextDiskEnd: u64)
     memLogCache
     (installedDisk: disk),
      let log_σ := circΣ.mk diskLog diskStart in
      (* these are the real positions; the abstract state lags them *)
      let durable_to := circΣ.diskEnd log_σ in
      let installed_to := diskStart in
      (is_circular (l +ₗ 2) log_σ) ∗
      (∃ s, (l +ₗ 5) ↦[slice.T (struct.t Update.S)] (slice_val s) ∗
      updates_slice s memLog) ∗
      (l +ₗ 7) ↦[uint64T] #memStart ∗
      (l +ₗ 8) ↦[uint64T] #nextDiskEnd ∗
      is_map (l +ₗ 12) memLogCache ∗
      ⌜int.val memStart ≤ int.val diskStart⌝ ∗
      ⌜∃ memLog', memLog = diskLog ++ memLog'⌝ ∗
      ⌜int.val σ.(log_state.durable_to) <= int.val durable_to⌝ ∗
      ⌜int.val σ.(log_state.installed_to) <= int.val installed_to⌝ ∗
      ⌜σ.(log_state.txn_disk) !! installed_to = Some installedDisk⌝ ∗
      ([∗ map] a↦b ∈ installedDisk, LogDiskBlocks d↦ b) ∗
      ⌜ forall pos1 pos2 (d1 d2: disk),
          σ.(log_state.txn_disk) !! pos1 = Some d1 ->
          σ.(log_state.txn_disk) !! pos2 = Some d2 ->
          int.val pos1 <= int.val pos2 ->
          int.val durable_to ≤ int.val pos2 ->
          d2 = apply_updates (take_updates pos1 pos2 memLog memStart) d1 ⌝
  ).

Definition walN: namespace := nroot .@ "wal".

Definition is_wal (l: loc) (σ: log_state.t): iProp Σ :=
  ∃ γ, is_lock walN γ #(l +ₗ 0) (lockInv l σ) ∗
       lock.is_cond walN γ (l +ₗ 4) (lockInv l σ) ∗
       lock.is_cond walN γ (l +ₗ 5) (lockInv l σ).

End heap.
