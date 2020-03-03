From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import wal.abstraction.
From Perennial.program_proof Require Import wal.circular_proof.
From Perennial.Helpers Require Import GenHeap.

Definition LogPositionT := wal.LogPosition.
Definition LogPosition := u64.
Definition LogDiskBlocks := 513.

Canonical Structure u64C := leibnizO u64.

Transparent slice.T.

Section heap.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!inG Σ (authR mnatUR)}.
Context `{!inG Σ (authR (optionUR (exclR (listO updateO))))}.
Context `{!inG Σ (authR (optionUR (exclR u64C)))}.

Implicit Types (Φ: val → iProp Σ).
Implicit Types (v:val) (z:Z).

Context (Pwal: log_state.t -> iProp Σ).
Context (walN : namespace).
Definition circN: namespace := walN .@ "circ".

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

Fixpoint compute_memLogMap (memLog : list update.t) (pos : u64) (m : gmap u64 val) : gmap u64 val :=
  match memLog with
  | nil => m
  | u :: memLog' =>
    compute_memLogMap memLog' (word.add pos 1) (<[ update.addr u := #pos ]> m)
  end.

Definition is_wal_state (st: loc) (γmemstart γmdiskend: gname) (γmemlog: gname) : iProp Σ :=
  ∃ (memLogPtr diskEnd nextDiskEnd memLogMapPtr: loc) (memStart diskEnd: u64) (memLog : list update.t) (memLogMap : gmap u64 val * val),
    st ↦[WalogState.S :: "memLog"] #memLogPtr ∗
    st ↦[WalogState.S :: "memStart"] #memStart ∗
    st ↦[WalogState.S :: "diskEnd"] #diskEnd ∗
    st ↦[WalogState.S :: "nextDiskEnd"] #nextDiskEnd ∗
    st ↦[WalogState.S :: "memLogMap"] #memLogMapPtr ∗
    (∃ s, memLogPtr ↦[slice.T (struct.t Update.S)] (slice_val s) ∗
          updates_slice s memLog) ∗
    is_map memLogMapPtr memLogMap ∗
    ⌜fst memLogMap = compute_memLogMap memLog memStart ∅⌝ ∗
    own γmemstart (● (Excl' memStart)) ∗
    own γmdiskend (● (Excl' diskEnd)) ∗
    own γmemlog (● (Excl' memLog))
    .

Definition is_wal_mem (l: loc) γlock γmemstart γmdiskend γmemlog : iProp Σ :=
  ∃ (memLock : loc) d (circ st : loc) (shutdown : bool) (nthread : u64) (condLogger condInstall condShut : loc),
    inv walN (∃ q, l ↦[Walog.S :: "memLock"]{q} #memLock) ∗
    inv walN (∃ q, l ↦[Walog.S :: "d"]{q} d) ∗
    inv walN (∃ q, l ↦[Walog.S :: "circ"]{q} #circ) ∗
    inv walN (∃ q, l ↦[Walog.S :: "st"]{q} #st) ∗
    inv walN (∃ q, l ↦[Walog.S :: "condLogger"]{q} #condLogger) ∗
    inv walN (∃ q, l ↦[Walog.S :: "condInstall"]{q} #condInstall) ∗
    inv walN (∃ q, l ↦[Walog.S :: "condShut"]{q} #condShut) ∗
    inv walN (∃ q, l ↦[Walog.S :: "shutdown"]{q} #shutdown) ∗
    inv walN (∃ q, l ↦[Walog.S :: "nthread"]{q} #nthread) ∗
    lock.is_cond condLogger #memLock ∗
    lock.is_cond condInstall #memLock ∗
    lock.is_cond condShut #memLock ∗
    is_lock walN γlock #memLock (is_wal_state st γmemstart γmdiskend γmemlog).

Definition is_wal_circ γdiskstart γdisklog (σ : circΣ.t) : iProp Σ :=
  own γdiskstart (● (Excl' σ.(circΣ.start))) ∗
  own γdisklog (● (Excl' σ.(circΣ.upds))).

Definition is_wal_sigma (σ: log_state.t) (memStart: u64) (memlog: list update.t) (diskend: nat) : iProp Σ :=
  ∃ d,
    ( [∗ map] a ↦ b ∈ d, a d↦ b ) ∗
    ⌜int.nat σ.(log_state.durable_to) = diskend⌝ ∗

    (* all disks agree on the addresses they cover *)
    ( [∗ map] pos ↦ td ∈ σ.(log_state.txn_disk), ⌜∀ a, d !! a = None <-> td !! a = None⌝ ) ∗

    (*
     * complication: what to do when we are midway through installing some transactions?
     * the current installed disk state isn't any specific transaction state..  we promise
     * that the installed disk contents match some transaction between installed_to and
     * durable_to..
     *)
    ( [∗ map] a ↦ b ∈ d,
      ∃ pos td, ⌜σ.(log_state.txn_disk) !! pos = Some td⌝ ∗
                ⌜td !! a = Some b⌝ ) ∗

    (*
     * connect [memlog] to σ.(log_state.txn_disk)
     *)
    True.

Definition is_wal_inner (γmemstart γdiskstart γmdiskend γdisklog γmemlog : gname) : iProp Σ :=
  ∃ (σ: log_state.t) (memStart diskStart mDiskEnd : u64) (disklog memlog : list update.t),
    Pwal σ ∗
    own γmemstart (◯ (Excl' memStart)) ∗
    own γdiskstart (◯ (Excl' diskStart)) ∗
    own γmdiskend (◯ (Excl' mDiskEnd)) ∗
    own γdisklog (◯ (Excl' disklog)) ∗
    own γmemlog (◯ (Excl' memlog)) ∗
    ⌜int.val memStart <= int.val diskStart⌝ ∗
    ⌜int.val mDiskEnd <= (int.val diskStart + (length disklog))⌝ ∗
    [∗ list] off ↦ u ∈ disklog,
      ⌜memlog !! Z.to_nat (int.val diskStart + off - int.val memStart) = Some u⌝ ∗
    is_wal_sigma σ memStart memlog (int.nat diskStart + length disklog).

Definition is_wal (l : loc) γcirc : iProp Σ :=
  ∃ γlock γmemstart γmdiskend γmemlog γdisklog γdiskstart,
    is_wal_mem l γlock γmemstart γmdiskend γmemlog ∗
    inv walN (is_wal_inner γmemstart γdiskstart γmdiskend γdisklog γmemlog) ∗
    is_circular circN (is_wal_circ γdiskstart γdisklog) γcirc.

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
 *)

End heap.
