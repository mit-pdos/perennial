From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From Perennial.algebra Require Import fmcounter.
From Perennial.algebra Require Import deletable_heap.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import wal.abstraction.
From Perennial.program_proof Require Import wal.circ_proof.
From Perennial.program_proof Require Import wal.specs.

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
Context `{!inG Σ (authR (optionUR (exclR (gmapO Z blockO))))}.
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

Definition is_wal_state (st: loc) γcirc (γmemstart γmemlog γnextDiskEnd: gname): iProp Σ :=
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
    own γmemlog (● (Excl' memLog)) ∗
    own γnextDiskEnd (● (Excl' nextDiskEnd))
    .

Definition is_wal_mem (l: loc) γlock γcirc γmemstart γmemlog γnextDiskEnd : iProp Σ :=
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
    is_lock walN γlock #memLock (is_wal_state st γcirc γmemstart γmemlog γnextDiskEnd).

Definition circular_pred (γcs : gname) (cs : circΣ.t) : iProp Σ :=
  own γcs (● (Excl' cs)).

Definition circ_matches_memlog (memStart : u64) (memLog : list update.t)
                               (circStart : u64) (circLog : list update.t) :=
  ∀ (off : nat) u,
    circLog !! off = Some u ->
    memLog !! (off + int.nat circStart - int.nat memStart)%nat = Some u.

Definition is_wal_inner (l : loc) (γcs : gname) (γcirc : circ_names)
                        (γlock γinstalled γinstaller_blocks : gname)
                        (γabsorptionBoundaries: gen_heapG nat unit Σ) : iProp Σ :=
  ∃ (cs: circΣ.t) (s : log_state.t) (γmemstart γmemlog: gname) (memStart : u64)
       (memLog : list update.t) (fully_installed being_installed : disk)
       (absorptionBoundaries : gmap nat unit) (γnextDiskEnd: gname),
    own γcs (◯ (Excl' cs)) ∗
    Pwal s ∗
    is_wal_mem l γlock γcirc γmemstart γmemlog γnextDiskEnd ∗
    own γmemstart (◯ (Excl' memStart)) ∗
    own γmemlog (◯ (Excl' memLog)) ∗
    ⌜ circ_matches_memlog memStart memLog cs.(circΣ.start) cs.(circΣ.upds) ⌝ ∗
    own γinstaller_blocks (◯ (Excl' being_installed)) ∗
    ( [∗ map] a ↦ v ∈ fully_installed, (LogSz + 2 + a) d↦ v ) ∗
    ( [∗ map] a ↦ v ∈ being_installed, (LogSz + 2 + a) d↦ v ) ∗
    ( ∃ (installed_txn_id : nat) (diskStart : u64),
      own γinstalled (◯ (Excl' installed_txn_id)) ∗
      start_is γcirc (1/4) diskStart ∗
      ⌜ fst <$> s.(log_state.txns) !! installed_txn_id = Some diskStart ∧
        s.(log_state.installed_to) ≤ installed_txn_id ∧
        let installed_disk := disk_at_txn_id installed_txn_id s in
        ∀ (a : u64) (b : Block),
          installed_disk !! int.val a = Some b ->
          ( updates_since installed_txn_id a s = nil ∧
            fully_installed !! int.val a = Some b ) ∨
          ∃ b0, being_installed !! int.val a = Some b0 ⌝ ) ∗
    gen_heap_ctx (hG:=γabsorptionBoundaries) absorptionBoundaries ∗
    ( ∃ (nextDiskEnd_txn_id : nat) (nextDiskEnd : u64),
      own γnextDiskEnd (◯ (Excl' nextDiskEnd)) ∗
      ⌜ absorptionBoundaries !! nextDiskEnd_txn_id = Some tt ⌝ ∗
      ⌜ fst <$> s.(log_state.txns) !! nextDiskEnd_txn_id = Some nextDiskEnd ⌝ ) ∗
    ( ∃ (diskEnd_txn_id : nat) (diskEnd : u64),
      diskEnd_is γcirc (1/4) (int.val diskEnd) ∗
      ⌜ absorptionBoundaries !! diskEnd_txn_id = Some tt ⌝ ∗
      ⌜ fst <$> s.(log_state.txns) !! diskEnd_txn_id = Some diskEnd ⌝ ) ∗
    ⌜ ∃ (memStart_txn_id : nat),
      fst <$> s.(log_state.txns) !! memStart_txn_id = Some memStart ∧
      ∀ (txn_id : nat) (pos : u64),
        fst <$> s.(log_state.txns) !! txn_id = Some pos ->
        ( ( memStart_txn_id ≤ txn_id ∧ absorptionBoundaries !! txn_id = Some tt ) ∨
          txn_id = length s.(log_state.txns) ) ->
        apply_upds (take (int.nat pos - int.nat memStart) memLog) ∅ =
        apply_upds (txn_upds (drop memStart_txn_id (take txn_id s.(log_state.txns)))) ∅ ⌝.

Definition is_wal (l : loc) γlock γinstalled γinstaller_blocks γabsorptionBoundaries : iProp Σ :=
  ∃ γcs γcirc ,
    inv walN (is_wal_inner l γcs γcirc γlock γinstalled γinstaller_blocks γabsorptionBoundaries) ∗
    is_circular circN (circular_pred γcs) γcirc.

End heap.
