From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From Perennial.algebra Require Import fmcounter.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import wal.abstraction.
From Perennial.program_proof Require Import wal.circ_proof.

Definition LogPositionT := wal.LogPosition.
Definition LogPosition := u64.
Definition LogDiskBlocks := 513.

Canonical Structure u64C := leibnizO u64.
Canonical Structure circΣC := leibnizO circΣ.t.

Transparent slice.T.

Section heap.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!fmcounterG Σ}.
Context `{!inG Σ (authR mnatUR)}.
Context `{!inG Σ (authR (optionUR (exclR (listO updateO))))}.
Context `{!inG Σ (authR (optionUR (exclR u64C)))}.
Context `{!inG Σ (authR (optionUR (exclR natO)))}.
Context `{!inG Σ (authR (optionUR (exclR circΣC)))}.
Context `{!inG Σ (authR (optionUR (exclR (listO u64O))))}.
Context `{!inG Σ (authR (optionUR (exclR (listO blockO))))}.
Context `{!inG Σ fmcounterUR}.

Implicit Types (Φ: val → iProp Σ).
Implicit Types (v:val) (z:Z).

Context (Pwal: log_state.t -> iProp Σ).
Context (walN : namespace).
Definition circN: namespace := walN .@ "circ".

Fixpoint compute_memLogMap (memLog : list update.t) (pos : u64) (m : gmap u64 val) : gmap u64 val :=
  match memLog with
  | nil => m
  | u :: memLog' =>
    compute_memLogMap memLog' (word.add pos 1) (<[ update.addr u := #pos ]> m)
  end.

Definition is_wal_state (st: loc) γcirc (γmemstart γmemlog: gname): iProp Σ :=
  ∃ (memLogSlice : Slice.t)
    (memLogMapPtr : loc)
    (memStart diskEnd nextDiskEnd : u64)
    (memLog : list update.t)
    (memLogMap : gmap u64 val),
    st ↦[WalogState.S :: "memLog"] (slice_val memLogSlice) ∗
    st ↦[WalogState.S :: "memStart"] #memStart ∗
    st ↦[WalogState.S :: "diskEnd"] #diskEnd ∗
    st ↦[WalogState.S :: "nextDiskEnd"] #nextDiskEnd ∗
    st ↦[WalogState.S :: "memLogMap"] #memLogMapPtr ∗
    (updates_slice memLogSlice memLog) ∗
    is_map memLogMapPtr (compute_memLogMap memLog memStart ∅, #0) ∗
    diskEnd_at_least γcirc (int.val diskEnd) ∗
    start_at_least γcirc memStart ∗
    own γmemstart (● (Excl' memStart)) ∗
    own γmemlog (● (Excl' memLog))
    .

Definition is_wal_mem (l: loc) γlock γcirc γmemstart γmemlog : iProp Σ :=
  ∃ q (memLock : loc) (d : val) (circ st : loc)
      (shutdown : bool) (nthread : u64)
      (condLogger condInstall condShut : loc),
    l ↦[Walog.S :: "memLock"]{q} #memLock ∗
    l ↦[Walog.S :: "d"]{q} d ∗
    l ↦[Walog.S :: "circ"]{q} #circ ∗
    l ↦[Walog.S :: "st"]{q} #st ∗
    l ↦[Walog.S :: "condLogger"]{q} #condLogger ∗
    l ↦[Walog.S :: "condInstall"]{q} #condInstall ∗
    l ↦[Walog.S :: "condShut"]{q} #condShut ∗
    l ↦[Walog.S :: "shutdown"]{q} #shutdown ∗
    l ↦[Walog.S :: "nthread"]{q} #nthread ∗
    lock.is_cond condLogger #memLock ∗
    lock.is_cond condInstall #memLock ∗
    lock.is_cond condShut #memLock ∗
    is_lock walN γlock #memLock (is_wal_state st γcirc γmemstart γmemlog).

Definition circular_pred (γcs : gname) (cs : circΣ.t) : iProp Σ :=
  own γcs (● (Excl' cs)).

Definition circ_matches_memlog (memStart : u64) (memLog : list update.t)
                               (circStart : u64) (circLog : list update.t) :=
  ∀ (off : nat) u,
    circLog !! off = Some u ->
    memLog !! (off + int.nat circStart - int.nat memStart)%nat = Some u.

Definition is_wal_inner (l : loc) (γcs : gname) (γcirc : circ_names)
                        (γlock γinstalled : gname) : iProp Σ :=
  ∃ cs (s : log_state.t) γmemstart γmemlog (memStart : u64)
       (memLog : list update.t) (fully_installed : disk),
    own γcs (◯ (Excl' cs)) ∗
    Pwal s ∗
    is_wal_mem l γlock γcirc γmemstart γmemlog ∗
    own γmemstart (◯ (Excl' memStart)) ∗
    own γmemlog (◯ (Excl' memLog)) ∗
    ⌜ circ_matches_memlog memStart memLog cs.(circΣ.start) cs.(circΣ.upds) ⌝ ∗
    ( [∗ map] a ↦ v ∈ fully_installed, (LogSz + 2 + a) d↦ v ) ∗
    ( ∃ (installed_txn_id : nat),
      own γinstalled (◯ (Excl' installed_txn_id)) ∗
      ⌜ is_Some (s.(log_state.txns) !! installed_txn_id) ∧
        s.(log_state.installed_to) ≤ installed_txn_id ∧
        let installed_disk := disk_at_txn_id installed_txn_id s in
        ∀ (a : u64) (b : Block),
          updates_since installed_txn_id a s = nil ->
          installed_disk !! int.val a = Some b ->
          fully_installed !! int.val a = Some b ⌝ ) ∗
    

(*
 * complication: what to do when we are midway through installing some transactions?
 * the current installed disk state isn't any specific transaction state..  we promise
 * that the installed disk contents match some transaction between installed_to and
 * durable_to..
 *)


(*
        d: disk;
        txns: list (u64 * list update.t);
        (* installed_lb promises what will be read after a cache miss *)
        installed_to: nat;
        (* durable_lb promises what will be on-disk after a crash *)
        durable_to: nat;
*)



Definition is_wal (l : loc) γlock γinstalled : iProp Σ :=
  ∃ γcs γcirc,
    inv walN (is_wal_inner l γcs γcirc γlock γinstalled) ∗
    is_circular circN (circular_pred γcs) γcirc.







 mDiskEnd : u64)
    (memLog : list update.t),
    own γmemstart (◯ (Excl' memStart)) ∗
    own γmdiskend (◯ (Excl' mDiskEnd)) ∗
    own γmemlog (◯ (Excl' memLog)) ∗
    ⌜int.val memStart <= int.val diskStart⌝ ∗
    ⌜int.val mDiskEnd <= (int.val diskStart + (length disklog))⌝ ∗
    [∗ list] off ↦ u ∈ disklog,
      ⌜memlog !! Z.to_nat (int.val diskStart + off - int.val memStart) = Some u⌝ ∗
    is_wal_sigma σ memStart memlog (int.nat diskStart + length disklog).


Definition circular_pred (γmemstart γmdiskend γmemlog : gname)
                         (cs : circΣ.t) : iProp Σ :=
  ∃ (memStart mDiskEnd : u64)
    (memLog : list update.t),
    own γmemstart (◯ (Excl' memStart)) ∗
    own γmdiskend (◯ (Excl' mDiskEnd)) ∗
    own γmemlog (◯ (Excl' memLog)) ∗
    ⌜int.val memStart <= int.val diskStart⌝ ∗
    ⌜int.val mDiskEnd <= (int.val diskStart + (length disklog))⌝ ∗
    [∗ list] off ↦ u ∈ disklog,
      ⌜memlog !! Z.to_nat (int.val diskStart + off - int.val memStart) = Some u⌝ ∗
    is_wal_sigma σ memStart memlog (int.nat diskStart + length disklog).

Definition is_wal (l : loc) γcirc γinstalled : iProp Σ :=
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
