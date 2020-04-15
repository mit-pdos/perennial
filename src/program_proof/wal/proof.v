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

Record wal_names :=
  { circ_name: circ_names;
    memStart_name : gname;
    memLog_name : gname;
    nextDiskEnd_name : gname;
    lock_name : gname;
    cs_name : gname;
    installer_blocks_name : gname;
    installed_name : gname;
    absorptionBoundaries_name : gen_heapG nat unit Σ;
  }.

Implicit Types (γ: wal_names).

Fixpoint compute_memLogMap (memLog : list update.t) (pos : u64) (m : gmap u64 val) : gmap u64 val :=
  match memLog with
  | nil => m
  | u :: memLog' =>
    compute_memLogMap memLog' (word.add pos 1) (<[ update.addr u := #pos ]> m)
  end.

Definition is_wal_state (st: loc) γ : iProp Σ :=
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
    diskEnd_at_least γ.(circ_name) (int.val diskEnd) ∗
    start_at_least γ.(circ_name) memStart ∗
    own γ.(memStart_name) (● (Excl' memStart)) ∗
    own γ.(memLog_name) (● (Excl' memLog)) ∗
    own γ.(nextDiskEnd_name) (● (Excl' nextDiskEnd))
    .

Definition is_wal_mem (l: loc) γ : iProp Σ :=
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
    is_lock walN γ.(lock_name) #memLock (is_wal_state st γ).

Definition circular_pred γ (cs : circΣ.t) : iProp Σ :=
  own γ.(cs_name) (● (Excl' cs)).

Definition circ_matches_memlog (memStart : u64) (memLog : list update.t)
                               (circStart : u64) (circLog : list update.t) :=
  ∀ (off : nat) u,
    circLog !! off = Some u ->
    memLog !! (off + int.nat circStart - int.nat memStart)%nat = Some u.

(** subslice takes elements with indices [n, m) in list [l] *)
Definition subslice {A} (n m: nat) (l: list A): list A :=
  drop n (take m l).

Theorem subslice_length {A} n m (l: list A) :
  (m <= length l)%nat ->
  length (subslice n m l) = (m - n)%nat.
Proof.
  rewrite /subslice; intros; autorewrite with len.
  lia.
Qed.

(* TODO: how will installer have enough information to know what's being
installed? how will ReadInstalled be able to prove something is in
fully_installed (which is currently implicitly the complement of
being_installed)? *)
Definition is_being_installed γ (being_installed: disk): iProp Σ :=
    (own γ.(installer_blocks_name) (◯ (Excl' being_installed)) ∗
    ( [∗ map] a ↦ v ∈ being_installed, a d↦ v ∗ ⌜2 + LogSz <= int.val a⌝ ))%I.

Definition is_installer_disks (s: log_state.t)
           (installed_txn_id: nat) (fully_installed being_installed: disk): Prop :=
  s.(log_state.installed_lb) ≤ installed_txn_id ∧
  let installed_disk := disk_at_txn_id installed_txn_id s in
  ∀ (a : u64) (b : Block),
    installed_disk !! int.val a = Some b ->
    ( updates_since installed_txn_id a s = nil ∧
      fully_installed !! int.val a = Some b ) ∨
    ∃ b0, being_installed !! int.val a = Some b0.

(* this part of the invariant holds the installed disk blocks from the data
region of the disk and relates them to the logical installed disk, computed via
the updates through some installed transaction. The things in this invariant are
generally maintained by the installer thread, which will need some ownership
transfer plan between the invariant and its local state. *)
Definition is_installed (s: log_state.t) γ : iProp Σ :=
  ∃ (fully_installed being_installed: disk),
    ( [∗ map] a ↦ v ∈ fully_installed,
      a d↦ v ∗ ⌜2 + LogSz <= int.val a⌝ ) ∗
    is_being_installed γ being_installed ∗
    ( ∃ (installed_txn_id : nat) (diskStart : u64),
      own γ.(installed_name) (◯ (Excl' installed_txn_id)) ∗
      start_is γ.(circ_name) (1/4) diskStart ∗
      ⌜is_txn s installed_txn_id diskStart⌝ ∗
      ⌜is_installer_disks s installed_txn_id fully_installed being_installed⌝ ).

Definition is_memlog (s: log_state.t)
           (memStart_txn_id: nat) memLog
           (absorptionBoundaries: gmap nat unit) (memStart: u64): Prop :=
      (* the high-level structure here is to relate each transaction "governed" by the memLog to the
      "cumulative updates" through that transaction. *)
      ∀ (txn_id : nat) (pos : u64),
        is_txn s txn_id pos ->
        (* the "governed" part - both transactions in absorptionBoundaries
        that have gone through the nextDiskEnd -> logger flow ... *)
        ( ( memStart_txn_id ≤ txn_id ∧ absorptionBoundaries !! txn_id = Some tt ) ∨
          (* ...as well as the current transaction, including all the
          potentially absorbed transactions that won't be logged *)
          txn_id = length s.(log_state.txns) ) ->
        (* the "cumulative updates" part - we can't talk about update lists here
        because the abstract state has all the updates that have gone through
        the system while the implementation maintains post-absorption
        transactions. Instead we state that the updates when coalesced in order
        are the same using [apply_upds] on an empty disk, which automatically
        captures that the latest update to each address should match, including
        the absence of any updates. The result is that the cached read from the
        memLog is a correct way to read from the abstract list of updates
        through txn.

        We don't just say [apply_upds memLog ∅ = apply_upds (skip memStart
        s.txns)]. This would only cover reads from the current in-memory state.
        We also say that earlier transactions are correct, since if we crash
        memLog will get trimmed to just the updates through diskEnd. (TODO(tej):
        could we just say this about the current state and diskEnd? or do we
        need the intermediate transactions to be inductive?) *)
        apply_upds (take (int.nat pos - int.nat memStart) memLog) ∅ =
        (* need +1 since txn_id should be included in subslice *)
        apply_upds (txn_upds (subslice memStart_txn_id (txn_id+1) s.(log_state.txns))) ∅.

Definition is_wal_inner (l : loc) γ : iProp Σ :=
  ∃ (cs: circΣ.t) (s : log_state.t) (γmemstart γmemlog: gname) (memStart : u64)
       (memLog : list update.t)
       (absorptionBoundaries : gmap nat unit) (γnextDiskEnd: gname),
    own γ.(cs_name) (◯ (Excl' cs)) ∗
    Pwal s ∗
    is_wal_mem l γ ∗
    own γmemstart (◯ (Excl' memStart)) ∗
    own γmemlog (◯ (Excl' memLog)) ∗
    ⌜ circ_matches_memlog memStart memLog cs.(circΣ.start) cs.(circΣ.upds) ⌝ ∗
    is_installed s γ ∗
    gen_heap_ctx (hG:=γ.(absorptionBoundaries_name)) absorptionBoundaries ∗
    (* a group-commit transaction is logged by setting nextDiskEnd to its pos -
       these conditions ensure that it is recorded as an absorption boundary,
       since at this point it becomes a plausible crash point *)
    ( ∃ (nextDiskEnd_txn_id : nat) (nextDiskEnd : u64),
      own γnextDiskEnd (◯ (Excl' nextDiskEnd)) ∗
      ⌜ absorptionBoundaries !! nextDiskEnd_txn_id = Some tt ⌝ ∗
      ⌜ is_txn s nextDiskEnd_txn_id nextDiskEnd ⌝ ) ∗
    (* next, transactions are actually logged to the circ buffer *)
    ( ∃ (diskEnd_txn_id : nat) (diskEnd : u64),
      diskEnd_is γ.(circ_name) (1/4) (int.val diskEnd) ∗
      ⌜ absorptionBoundaries !! diskEnd_txn_id = Some tt ⌝ ∗
      ⌜ is_txn s diskEnd_txn_id diskEnd ⌝ ∗
      (* TODO(tej): does this make sense? it's the only constraint on
         durable_lb *)
      ⌜ s.(log_state.durable_lb) ≤ diskEnd_txn_id ⌝ ) ∗
    (* Here we establish what the memLog contains, which is necessary for reads
    to work (they read through memLogMap, but the lock invariant establishes
    that this matches memLog). This is complicated a bit by the fact that the
    memLog can contain elements before diskStart (before the installer has a
    chance to trim them), contains all the logged updates, contains
    established transactions in absorptionBoundaries, and finally contains a
    tail of transactions that are subject to absorption and not owned by the
    logger. *)
    ∃ (memStart_txn_id : nat),
      ⌜is_txn s memStart_txn_id memStart⌝ ∗
      ⌜is_memlog s memStart_txn_id memLog absorptionBoundaries memStart⌝.

Definition is_wal (l : loc) : iProp Σ :=
  ∃ γ, inv walN (is_wal_inner l γ) ∗
    is_circular circN (circular_pred γ) γ.(circ_name).

End heap.
