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

Context (P: log_state.t -> iProp Σ).
Context (walN : namespace).
Definition circN: namespace := walN .@ "circ".

Record wal_names :=
  { circ_name: circ_names;
    memStart_name : gname;
    memLog_name : gname;
    nextDiskEnd_name : gname;
    lock_name : gname;
    cs_name : gname;
    installed_name : gname;
    installed_data_name : gname;
    absorptionBoundaries_name : gen_heapG nat unit Σ;
  }.

Implicit Types (γ: wal_names).

Fixpoint compute_memLogMap (memLog : list update.t) (pos : u64) (m : gmap u64 val) : gmap u64 val :=
  match memLog with
  | nil => m
  | u :: memLog' =>
    compute_memLogMap memLog' (word.add pos 1) (<[ update.addr u := #pos ]> m)
  end.

(** the lock invariant protecting the WalogState, corresponding to l.memLock *)
Definition wal_linv (st: loc) γ : iProp Σ :=
  ∃ (memLogSlice : Slice.t)
    (* TODO: group these into a Record *)
    (memLogMapPtr : loc)
    (memStart diskEnd nextDiskEnd : u64)
    (shutdown:bool) (nthread: u64)
    (memLog : list update.t),
    (st ↦[WalogState.S :: "memLog"] (slice_val memLogSlice) ∗
     st ↦[WalogState.S :: "memStart"] #memStart ∗
     st ↦[WalogState.S :: "diskEnd"] #diskEnd ∗
     st ↦[WalogState.S :: "nextDiskEnd"] #nextDiskEnd ∗
     st ↦[WalogState.S :: "memLogMap"] #memLogMapPtr ∗
     st ↦[WalogState.S :: "shutdown"] #shutdown ∗
     st ↦[WalogState.S :: "nthread"] #nthread) ∗
    (updates_slice memLogSlice memLog) ∗
    is_map memLogMapPtr (compute_memLogMap memLog memStart ∅, #0) ∗
    diskEnd_at_least γ.(circ_name) (int.val diskEnd) ∗
    start_at_least γ.(circ_name) memStart ∗
    own γ.(memStart_name) (● (Excl' memStart)) ∗
    own γ.(memLog_name) (● (Excl' memLog)) ∗
    own γ.(nextDiskEnd_name) (● (Excl' nextDiskEnd))
    .

Definition is_wal_mem (l: loc) γ : iProp Σ :=
  (* TODO: group these into a record *)
  ∃ (memLock : loc) (d : val) (circ st : loc)
      (condLogger condInstall condShut : loc),
    (∃ q,  l ↦[Walog.S :: "memLock"]{q} #memLock ∗
           l ↦[Walog.S :: "d"]{q} d ∗
           l ↦[Walog.S :: "circ"]{q} #circ ∗
           l ↦[Walog.S :: "st"]{q} #st ∗
           l ↦[Walog.S :: "condLogger"]{q} #condLogger ∗
           l ↦[Walog.S :: "condInstall"]{q} #condInstall ∗
           l ↦[Walog.S :: "condShut"]{q} #condShut) ∗
    lock.is_cond condLogger #memLock ∗
    lock.is_cond condInstall #memLock ∗
    lock.is_cond condShut #memLock ∗
    is_lock walN γ.(lock_name) #memLock (wal_linv st γ).

Typeclasses Opaque struct_field_mapsto.

Theorem is_wal_mem_dup l γ :
    is_wal_mem l γ -∗ is_wal_mem l γ ∗ is_wal_mem l γ.
Proof.
  iIntros "Hinv".
  iDestruct "Hinv" as
      (memLock d circ st
         condLogger condInstall condShut)
        "(Hfields&HcondLogger&HcondInstall&HcondShut&#His_lock)".
  iDestruct "Hfields" as (q) "([Hf1 ?] & [Hf2 ?] & [Hf3 ?] & [Hf4 ?] & [Hf5 ?] & [Hf6 ?] & [Hf7 ?])".
  iDestruct (is_cond_dup with "HcondLogger") as "[Hcond1 ?]".
  iDestruct (is_cond_dup with "HcondInstall") as "[Hcond2 ?]".
  iDestruct (is_cond_dup with "HcondShut") as "[Hcond3 ?]".
  iSplitL "Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hcond1 Hcond2 Hcond3".
  { iExists memLock, d, circ, st.
    iExists condLogger, condInstall, condShut.
    iFrame "∗ His_lock".
    iExists (q/2)%Qp; iFrame. }
  { iExists memLock, d, circ, st.
    iExists condLogger, condInstall, condShut.
    iFrame "∗ His_lock".
    iExists (q/2)%Qp; iFrame. }
Qed.

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

(* TODO: make this spatial - change absorptionBoundaries to include the
txn_id, make this mapsto γ.(absorptionBoundaries_name) txn_id pos *)
Definition txn_pos s txn_id pos: iProp Σ :=
  ⌜is_txn s txn_id pos⌝.

Definition is_boundary γ txn_id : iProp Σ :=
  mapsto (hG:=γ.(absorptionBoundaries_name)) txn_id 1 ().

(* this part of the invariant holds the installed disk blocks from the data
region of the disk and relates them to the logical installed disk, computed via
the updates through some installed transaction. *)
Definition is_installed (s: log_state.t) γ : iProp Σ :=
  ∃ installed_txn_id diskStart,
    own γ.(installed_name) (◯ Excl' installed_txn_id) ∗
    start_is γ.(circ_name) (1/4) diskStart ∗
    txn_pos s installed_txn_id diskStart ∗
    ([∗ map] a ↦ _ ∈ s.(log_state.d),
     ∃ (b: Block),
       (* every disk block has at least through installed_txn_id (most have
        exactly, but some blocks may be in the process of being installed) *)
       (* TODO: need to let installer keep track of exactly which blocks are
       at a new txn_id, so that it can update installed_txn_id *)
       ⌜∃ txn_id', (installed_txn_id ≤ txn_id')%nat ∧
                   let txns := take txn_id' s.(log_state.txns) in
                   apply_upds (txn_upds txns) s.(log_state.d) !! a = Some b⌝ ∗
       a d↦ b ∗ ⌜2 + LogSz ≤ int.val a⌝).

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

Definition is_wal_inner (l : loc) γ s : iProp Σ :=
  ∃ (cs: circΣ.t) (memStart : u64)
       (memLog : list update.t)
       (absorptionBoundaries : gmap nat unit),
    is_wal_mem l γ ∗
    own γ.(cs_name) (◯ (Excl' cs)) ∗
    own γ.(memStart_name) (◯ (Excl' memStart)) ∗
    own γ.(memLog_name) (◯ (Excl' memLog)) ∗
    ⌜ circ_matches_memlog memStart memLog cs.(circΣ.start) cs.(circΣ.upds) ⌝ ∗
    is_installed s γ ∗
    gen_heap_ctx (hG:=γ.(absorptionBoundaries_name)) absorptionBoundaries ∗
    (* a group-commit transaction is logged by setting nextDiskEnd to its pos -
       these conditions ensure that it is recorded as an absorption boundary,
       since at this point it becomes a plausible crash point *)
    ( ∃ (nextDiskEnd_txn_id : nat) (nextDiskEnd : u64),
      own γ.(nextDiskEnd_name) (◯ (Excl' nextDiskEnd)) ∗
      ⌜ absorptionBoundaries !! nextDiskEnd_txn_id = Some tt ⌝ ∗
      txn_pos s nextDiskEnd_txn_id nextDiskEnd ) ∗
    (* next, transactions are actually logged to the circ buffer *)
    ( ∃ (diskEnd_txn_id : nat) (diskEnd : u64),
      diskEnd_is γ.(circ_name) (1/4) (int.val diskEnd) ∗
      ⌜ absorptionBoundaries !! diskEnd_txn_id = Some tt ⌝ ∗
      txn_pos s diskEnd_txn_id diskEnd ∗
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
      txn_pos s memStart_txn_id memStart ∗
      ⌜is_memlog s memStart_txn_id memLog absorptionBoundaries memStart⌝.

Definition is_wal (l : loc) γ : iProp Σ :=
  inv walN (∃ σ, is_wal_inner l γ σ ∗ P σ) ∗
  is_circular circN (circular_pred γ) γ.(circ_name).

Instance is_cond_timeless (c l: loc) : Timeless (is_cond c #l).
Proof.
  rewrite /is_cond.
  refine _.
Qed.

Theorem is_wal_read_mem l γ : is_wal l γ -∗ |={⊤}=> ▷ is_wal_mem l γ.
Proof.
  iIntros "#Hwal".
  iDestruct "Hwal" as "[Hinv _]".
  iApply (inv_dup_acc with "Hinv"); first by set_solver.
  iIntros "HinvI".
  iDestruct "HinvI" as (σ) "[HinvI HP]".
  iDestruct "HinvI" as (cs memStart memLog absorptionBoundaries) "(Hmem&Hrest)".
  iDestruct (is_wal_mem_dup with "Hmem") as "[Hmem1 Hmem2]".
  iSplitR "Hmem2"; last by auto.
  iExists _; iFrame.
  iExists _, _, _, _; iFrame.
Qed.

Theorem wal_linv_shutdown st γ :
  wal_linv st γ -∗ ∃ (shutdown:bool) (nthread:u64),
      (st ↦[WalogState.S :: "shutdown"] #shutdown ∗
          st ↦[WalogState.S :: "nthread"] #nthread) ∗
      (∀ (shutdown: bool) (nthread: u64),
          st ↦[WalogState.S :: "shutdown"] #shutdown -∗
          st ↦[WalogState.S :: "nthread"] #nthread -∗
          wal_linv st γ).
Proof.
  iIntros "Hlkinv".
  iDestruct "Hlkinv" as (memLogSlice memLogMapPtr memStart diskEnd nextDiskEnd shutdown nthread memLog) "[Hfields Hrest]".
  iDestruct "Hfields" as "(HmemLog&HmemStart&HdiskEnd&HnextDiskEnd&HmemLogMap&Hshutdown&Hnthread)".
  iExists shutdown, nthread.
  iFrame.
  iIntros (shutdown' nthread') "Hshutdown Hnthread".
  iExists memLogSlice, memLogMapPtr, memStart, diskEnd, nextDiskEnd.
  iExists _, _, memLog.
  iFrame.
Qed.

Theorem wp_Walog__logAppend l γ q (st: loc) (memLock: loc) (condLogger condInstall: loc) :
  {{{ l ↦[Walog.S :: "memLock"]{q} #memLock ∗
      l ↦[Walog.S :: "condLogger"]{q} #condLogger ∗
      l ↦[Walog.S :: "condInstall"]{q} #condInstall ∗
      l ↦[Walog.S :: "st"]{q} #st ∗
      is_cond condLogger #memLock ∗
      is_cond condInstall #memLock ∗
      wal_linv st γ ∗
      locked γ.(lock_name) ∗
      is_lock walN γ.(lock_name) #memLock (wal_linv st γ)
  }}}
    Walog__logAppend #l
  {{{ (progress:bool), RET #progress;
      l ↦[Walog.S :: "memLock"]{q} #memLock ∗
      l ↦[Walog.S :: "condLogger"]{q} #condLogger ∗
      l ↦[Walog.S :: "condInstall"]{q} #condInstall ∗
      l ↦[Walog.S :: "st"]{q} #st ∗
      is_cond condLogger #memLock ∗
      is_cond condInstall #memLock ∗
      wal_linv st γ ∗
      locked γ.(lock_name)
  }}}.
Proof.
  iIntros (Φ) "(HmemLock& HcondLogger& HcondInstall&
              Hf& His_cond1& His_cond2& Hlkinv& Hlocked& #His_lock) HΦ".
  wp_call.
  wp_bind (For _ _ _).
  (* TODO: need inner part of wal_linv with fixed memLog, so we can say after
  this wait loop [length memLog ≤ Z.of_nat LogSz] *)
  wp_apply (wp_forBreak_cond
              (λ b, l ↦[Walog.S :: "st"]{q} #st ∗
                    l ↦[Walog.S :: "condInstall"]{q} #condInstall ∗
                    is_cond condInstall #memLock ∗
                    locked γ.(lock_name) ∗
                      wal_linv st γ)%I
              with "[] [$Hf $HcondInstall $His_cond2 $Hlkinv $Hlocked]").
  { iIntros "!>" (Φ') "(Hf&Hf2&His_cond2&Hlocked&Hlkinv) HΦ".
    wp_loadField.
    iDestruct "Hlkinv" as (memLogSlice memLogMapPtr memStart diskEnd nextDiskEnd shutdown nthread memLog) "[Hfields Hrest]".
    iDestruct "Hfields" as "(HmemLog&HmemStart&HdiskEnd&HnextDiskEnd&HmemLogMap&Hshutdown&Hnthread)".
    wp_loadField.
    wp_apply wp_slice_len; wp_pures.
    change (int.val $ word.divu (word.sub 4096 8) 8) with LogSz.
    wp_if_destruct.
    - wp_loadField.
      wp_apply (wp_condWait with "[$His_cond2 $Hlocked $His_lock HmemLog HmemStart HdiskEnd HnextDiskEnd HmemLogMap Hshutdown Hnthread Hrest]").
      { iExists _, _, _, _, _, _, _, _; iFrame. }
      iIntros "(His_cond&Hlocked&Hlkinv)".
      wp_pures.
      iApply ("HΦ" with "[$]").
    - iApply "HΦ"; iFrame.
      iExists _, _, _, _, _, _, _, _; iFrame.
  }
Admitted.

Ltac shutdown_fields :=
  let shutdown := fresh "shutdown" in
  let nthread := fresh "nthread" in
  iDestruct (wal_linv_shutdown with "Hlkinv") as (shutdown nthread) "[[? ?] Hlkinv]";
  (repeat wp_loadField);
  (repeat wp_storeField);
  iSpecialize ("Hlkinv" with "[$] [$]");
  try (clear shutdown);
  try (clear nthread).

Theorem wp_Walog__logger l γ :
  {{{ is_wal l γ }}}
    Walog__logger #l
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "#Hwal HΦ".
  iMod (is_wal_read_mem with "Hwal") as "Hmem".
  wp_call.
  iDestruct "Hmem" as (memLock d circ st condLogger condInstall condShut) "Hmem".
  iDestruct "Hmem" as "(Hfields&HcondLogger&HcondInstall&HcondShut&#Hlk)".
  iDestruct "Hfields" as (q) "(Hf1&Hf2&Hf3&Hf4&Hf5&Hf6&Hf7)".
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "(Hlk_held&Hlkinv)".
  wp_pures.
  wp_bind (struct.storeF _ _ _ _).
  shutdown_fields.
  wp_pures.
  wp_bind (For _ _ _).
  wp_apply (wp_forBreak_cond (fun b => wal_linv st γ ∗
                                       l ↦[Walog.S :: "st"]{q} #st)%I
              with "[] [Hlkinv Hf4]").
  { iIntros "!>" (Φ') "[Hlkinv Hf4] HΦ".
    shutdown_fields.
    wp_pures.
    wp_if_destruct.
    - wp_pures.
      (* XXX: can't apply wp_Walog__logAppend, need a bunch more stuff in the
      loop invariant *)
      admit.
    - iApply "HΦ". iFrame.
  }
  { iFrame. }
  iIntros "(Hlkinv&Hf4)".
  wp_apply util_proof.wp_DPrintf.
  shutdown_fields.
  wp_loadField.
  wp_apply (wp_condSignal with "HcondShut").
  iIntros "His_cond".
  wp_loadField.
  wp_apply (release_spec with "[$Hlk $Hlk_held $Hlkinv]").
  iApply ("HΦ" with "[$]").
Abort.

End heap.
