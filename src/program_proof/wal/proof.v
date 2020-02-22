From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import wal.abstraction.
From Perennial.program_proof Require Import wal.circular_proof.
From Perennial.Helpers Require Import GenHeap.

Definition LogPositionT := wal.LogPosition.
Definition LogPosition := u64.
Definition LogDiskBlocks := 513.

Transparent slice.T.

Section heap.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!inG Σ (authR mnatUR)}.
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

Definition is_wal_state (st: loc) (σ: log_state.t) (γLog : gen_heapG u64 update.t Σ) γstart γend: iProp Σ :=
  ∃ (memLogPtr diskEnd nextDiskEnd memLogMapPtr: loc) (memStart diskEnd: u64) memLog memLogMap,
    st ↦[structTy WalogState.S] (#memLogPtr, #memStart, #diskEnd, #nextDiskEnd, #memLogMapPtr) ∗
    (∃ s, memLogPtr ↦[slice.T (struct.t Update.S)] (slice_val s) ∗
    updates_slice s memLog) ∗
    (* relate memLog to \gammaLog *)
    is_map memLogMapPtr memLogMap ∗
    own γstart (◯ ((int.nat memStart) : mnat)) ∗
    own γend (◯ ((int.nat diskEnd) : mnat)).

Definition is_circular_appender (circ: loc) γlog γstart γend: iProp Σ :=
  ∃ (diskaddr:loc) s addrList,
    circ ↦[struct.t circularAppender.S] #diskaddr ∗
    diskaddr ↦[slice.T uint64T] (slice_val s) ∗
    is_slice s uint64T addrList ∗
    (∃ mh,
        gen_heap_ctx (hG := γlog) mh ∗
        (* relate addrList to the home address of blocks in log; how slice and map? *)
        (* ⌜ mh !! (word.add σ.(circΣ.start) i) = Some(upd) ⌝ → upd.Addr = addr * *)
        is_circ γlog γstart γend).

Definition walN: namespace := nroot .@ "wal".

Definition is_wal (l: loc) (σ: log_state.t): iProp Σ :=
  ∃ memLock d (circ st condL condI:loc) γh γstart γend,
    (* ro ->? *)
    l ↦[structTy Walog.S] (#memLock, #d, #circ, #st, #condL, #condI) ∗
    is_circular_appender circ γh γstart γend ∗
    (∃ γ,
        is_lock walN γ #memLock (is_wal_state st σ γh γstart γend) ∗
        lock.is_cond condL #memLock ∗
        lock.is_cond condI #memLock).

(* old lockInv, parts need to be incorporated above

Definition lockInv (l: loc) (σ: log_state.t): iProp Σ :=
  (∃ memLog diskLog
     (memStart: u64) (diskStart: u64) (nextDiskEnd: u64)
     memLogCache
     (installedDisk: disk),
      let log_σ := circΣ.mk diskLog diskStart in
      (* these are the real positions; the abstract state lags them *)
      let durable_to := circΣ.diskEnd log_σ in
      let installed_to := diskStart in
      (* (is_circularAppender (l +ₗ 2) log_σ) ∗ *)
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
       lock.is_cond (l +ₗ 4) #(l +ₗ 0) ∗
       lock.is_cond (l +ₗ 5) #(l +ₗ 0).
 *)

End heap.
