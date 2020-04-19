From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From RecordUpdate Require Import RecordSet.
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
    groupTxns_name : gen_heapG nat u64 Σ;
  }.

Implicit Types (γ: wal_names).

Fixpoint compute_memLogMap (memLog : list update.t) (pos : u64) (m : gmap u64 val) : gmap u64 val :=
  match memLog with
  | nil => m
  | u :: memLog' =>
    compute_memLogMap memLog' (word.add pos 1) (<[ update.addr u := #pos ]> m)
  end.

(** low-level, unimportant state *)
Record lowState :=
  { memLogSlice: Slice.t;
    memLogMapPtr: loc;
    shutdown: bool;
    nthread: u64;
  }.

Instance lowState_eta: Settable _ :=
  settable! Build_lowState <memLogSlice; memLogMapPtr; shutdown; nthread>.

Record locked_state :=
  { memStart: u64;
    diskEnd: u64;
    nextDiskEnd: u64;
    memLog: list update.t; }.

Instance locked_state_eta: Settable _ :=
  settable! Build_locked_state <memStart; diskEnd; nextDiskEnd; memLog>.

(** the lock invariant protecting the WalogState, corresponding to l.memLock *)
Definition wal_linv (st: loc) γ : iProp Σ :=
  ∃ σₗ σ,
    (st ↦[WalogState.S :: "memLog"] (slice_val σₗ.(memLogSlice)) ∗
     st ↦[WalogState.S :: "memStart"] #σ.(memStart) ∗
     st ↦[WalogState.S :: "diskEnd"] #σ.(diskEnd) ∗
     st ↦[WalogState.S :: "nextDiskEnd"] #σ.(nextDiskEnd) ∗
     st ↦[WalogState.S :: "memLogMap"] #σₗ.(memLogMapPtr) ∗
     st ↦[WalogState.S :: "shutdown"] #σₗ.(shutdown) ∗
     st ↦[WalogState.S :: "nthread"] #σₗ.(nthread)) ∗
    (updates_slice σₗ.(memLogSlice) σ.(memLog)) ∗
    is_map σₗ.(memLogMapPtr) (compute_memLogMap σ.(memLog) σ.(memStart) ∅, #0) ∗
    diskEnd_at_least γ.(circ_name) (int.val σ.(diskEnd)) ∗
    start_at_least γ.(circ_name) σ.(memStart) ∗
    own γ.(memStart_name) (● (Excl' σ.(memStart))) ∗
    own γ.(nextDiskEnd_name) (● (Excl' σ.(nextDiskEnd)))
    (* TODO: inline groupTxns, memLog invariant *)
    .

(** The implementation state contained in the *Walog struct, which is all
read-only. *)
Record wal_state :=
  { memLock: loc;
    wal_d: val;
    circ: loc;
    wal_st: loc;
    condLogger: loc;
    condInstall: loc;
    condShut: loc;
  }.

Instance wal_state_eta : Settable _ :=
  settable! Build_wal_state <memLock; wal_d; circ; wal_st; condLogger; condInstall; condShut>.

Definition is_wal_mem (l: loc) γ : iProp Σ :=
  ∃ σₛ,
    (readonly (l ↦[Walog.S :: "memLock"] #σₛ.(memLock)) ∗
     readonly (l ↦[Walog.S :: "d"] σₛ.(wal_d)) ∗
     readonly (l ↦[Walog.S :: "circ"] #σₛ.(circ)) ∗
     readonly (l ↦[Walog.S :: "st"] #σₛ.(wal_st)) ∗
     readonly (l ↦[Walog.S :: "condLogger"] #σₛ.(condLogger)) ∗
     readonly (l ↦[Walog.S :: "condInstall"] #σₛ.(condInstall)) ∗
     readonly (l ↦[Walog.S :: "condShut"] #σₛ.(condShut))) ∗
    lock.is_cond σₛ.(condLogger) #σₛ.(memLock) ∗
    lock.is_cond σₛ.(condInstall) #σₛ.(memLock) ∗
    lock.is_cond σₛ.(condShut) #σₛ.(memLock) ∗
    is_lock walN γ.(lock_name) #σₛ.(memLock) (wal_linv σₛ.(wal_st) γ).

Instance is_wal_mem_persistent : Persistent (is_wal_mem l γ) := _.

Typeclasses Opaque struct_field_mapsto.

Definition circular_pred γ (cs : circΣ.t) : iProp Σ :=
  own γ.(cs_name) (● (Excl' cs)).

Definition circ_matches_memlog (memStart : u64) (memLog : list update.t)
                               (cs: circΣ.t) :=
  ∀ (off : nat) u,
    cs.(circΣ.upds) !! off = Some u ->
    memLog !! (off + int.nat cs.(circΣ.start) - int.nat memStart)%nat = Some u.

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

Definition txn_pos s txn_id pos: iProp Σ :=
  ⌜is_txn s txn_id pos⌝.

Definition group_txn γ txn_id (pos: u64) : iProp Σ :=
  readonly (mapsto (hG:=γ.(groupTxns_name)) txn_id 1%Qp pos).

(* this part of the invariant holds the installed disk blocks from the data
region of the disk and relates them to the logical installed disk, computed via
the updates through some installed transaction. *)
Definition is_installed (s: log_state.t) γ : iProp Σ :=
  ∃ installed_txn_id diskStart,
    own γ.(installed_name) (◯ Excl' installed_txn_id) ∗
    start_is γ.(circ_name) (1/4) diskStart ∗
    group_txn γ installed_txn_id diskStart ∗
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

(** the simple role of the memLog is to contain all the transactions in the
abstract state starting at the memStart_txn_id *)
Definition is_mem_memlog γ memLog txns memStart_txn_id : Prop :=
  apply_upds memLog ∅ =
  apply_upds (txn_upds (drop memStart_txn_id txns)) ∅.

(** the more complicated role of memLog is to correctly store committed
transactions if we roll it back to a [group_txn] boundary, which is what happens
on crash where [memLog] is restored from the circ log *)
Definition is_crash_memlog γ
           (memStart_txn_id: nat) memLog txns (memStart: u64): iProp Σ :=
      (* the high-level structure here is to relate each group-committed transaction to the
      "cumulative updates" through that transaction. *)
      ∀ (txn_id : nat) (pos : u64),
        ⌜memStart_txn_id ≤ txn_id⌝ -∗
        (* note that we'll only read from this for the durable txn, but we need
        to track it from the moment a group txn is allocated (when nextDiskEnd
        is set) *)
        group_txn γ txn_id pos -∗
        (* the "cumulative updates" part - we can't talk about update lists here
        because the abstract state has all the updates that have gone through
        the system while the implementation maintains post-absorption
        transactions. Instead we state that the updates when coalesced in order
        are the same using [apply_upds] on an empty disk, which automatically
        captures that the latest update to each address should match, including
        the absence of any updates. The result is that the cached read from the
        memLog is a correct way to read from the abstract list of updates
        through txn. *)
        ⌜apply_upds (take (int.nat pos - int.nat memStart) memLog) ∅ =
        apply_upds (txn_upds (subslice memStart_txn_id (txn_id+1) txns)) ∅⌝.

(** an invariant governing the data logged for crash recovery of (a prefix of)
memLog. *)
Definition log_inv γ txns : iProp Σ :=
  ∃ (memStart: u64) (memLog: list update.t) cs,
    own γ.(memStart_name) (◯ (Excl' memStart)) ∗
    own γ.(cs_name) (◯ (Excl' cs)) ∗
    ⌜circ_matches_memlog memStart memLog cs ⌝ ∗
    ∃ (memStart_txn_id : nat),
      group_txn γ memStart_txn_id memStart ∗
      is_crash_memlog γ memStart_txn_id memLog txns memStart.

(** the complete wal invariant *)
Definition is_wal_inner (l : loc) γ s : iProp Σ :=
  ∃ (memStart : u64) (memLog : list update.t)
    (groupTxns : gmap nat u64),
    is_wal_mem l γ ∗
    log_inv γ s.(log_state.txns) ∗
    is_installed s γ ∗
    gen_heap_ctx (hG:=γ.(groupTxns_name)) groupTxns ∗
    (* a group-commit transaction is logged by setting nextDiskEnd to its pos -
       these conditions ensure that it is recorded as an absorption boundary,
       since at this point it becomes a plausible crash point *)
    ( ∃ (nextDiskEnd_txn_id : nat) (nextDiskEnd : u64),
      own γ.(nextDiskEnd_name) (◯ (Excl' nextDiskEnd)) ∗
      group_txn γ nextDiskEnd_txn_id nextDiskEnd ) ∗
    (* next, transactions are actually logged to the circ buffer *)
    ( ∃ (diskEnd_txn_id : nat) (diskEnd : u64),
      diskEnd_is γ.(circ_name) (1/4) (int.val diskEnd) ∗
      group_txn γ diskEnd_txn_id diskEnd ∗
      txn_pos s diskEnd_txn_id diskEnd ∗
      (* TODO(tej): does this make sense? it's the only constraint on
         durable_lb *)
      ⌜ s.(log_state.durable_lb) ≤ diskEnd_txn_id ⌝ ) ∗
    (* Here we establish what the memLog contains, which is necessary for reads
    to work (they read through memLogMap, but the lock invariant establishes
    that this matches memLog). This is complicated a bit by the fact that the
    memLog can contain elements before diskStart (before the installer has a
    chance to trim them), contains all the logged updates, contains
    grouped transactions in groupTxns, and finally contains a
    tail of transactions that are subject to absorption and not owned by the
    logger. *)
    ∃ (memStart_txn_id : nat),
      group_txn γ memStart_txn_id memStart ∗
      ⌜is_mem_memlog γ memLog s.(log_state.txns) memStart_txn_id⌝.

Definition is_wal (l : loc) γ : iProp Σ :=
  inv walN (∃ σ, is_wal_inner l γ σ ∗ P σ) ∗
  is_circular circN (circular_pred γ) γ.(circ_name).

Theorem is_wal_read_mem l γ : is_wal l γ -∗ |={⊤}=> ▷ is_wal_mem l γ.
Proof.
  iIntros "#Hwal".
  iDestruct "Hwal" as "[Hinv _]".
  iApply (inv_dup_acc with "Hinv"); first by set_solver.
  iIntros "HinvI".
  iDestruct "HinvI" as (σ) "[HinvI HP]".
  iDestruct "HinvI" as (memStart memLog groupTxns) "(#Hmem&Hrest)".
  iSplitL; last by auto.
  iExists _; iFrame.
  iExists _, _, _; iFrame "∗ Hmem".
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
  iDestruct "Hlkinv" as (σₗ σ) "[Hfields Hrest]".
  iDestruct "Hfields" as "(HmemLog&HmemStart&HdiskEnd&HnextDiskEnd&HmemLogMap&Hshutdown&Hnthread)".
  iExists _, _.
  iFrame.
  iIntros (shutdown' nthread') "Hshutdown Hnthread".
  iExists (set shutdown (λ _, shutdown') (set nthread (λ _, nthread') σₗ)), σ; simpl.
  iFrame.
Qed.


Theorem wp_Walog__logAppend l γ σₛ :
  {{{ readonly (l ↦[Walog.S :: "memLock"] #σₛ.(memLock)) ∗
      readonly (l ↦[Walog.S :: "condLogger"] #σₛ.(condLogger)) ∗
      readonly (l ↦[Walog.S :: "condInstall"] #σₛ.(condInstall)) ∗
      is_cond σₛ.(condLogger) #σₛ.(memLock) ∗
      is_cond σₛ.(condInstall) #σₛ.(memLock) ∗
      readonly (l ↦[Walog.S :: "st"] #σₛ.(wal_st)) ∗
      wal_linv σₛ.(wal_st) γ ∗
      locked γ.(lock_name) ∗
      is_lock walN γ.(lock_name) #σₛ.(memLock) (wal_linv σₛ.(wal_st) γ)
  }}}
    Walog__logAppend #l
  {{{ (progress:bool), RET #progress;
      wal_linv σₛ.(wal_st) γ ∗
      locked γ.(lock_name)
  }}}.
Proof.
  iIntros (Φ) "(#HmemLock& #HcondLogger& #HcondInstall &
              #His_cond1 & #His_cond2 & #Hf & Hlkinv& Hlocked& #His_lock) HΦ".
  wp_call.
  wp_bind (For _ _ _).
  (* TODO: need inner part of wal_linv with fixed memLog, so we can say after
  this wait loop [length memLog ≤ Z.of_nat LogSz] *)
  wp_apply (wp_forBreak_cond
              (λ b, locked γ.(lock_name) ∗
                    wal_linv σₛ.(wal_st) γ)%I
              with "[] [$Hlkinv $Hlocked]").
  { iIntros "!>" (Φ') "(Hlocked&Hlkinv) HΦ".
    wp_loadField.
    iDestruct "Hlkinv" as (σₗ σ) "[Hfields Hrest]".
    iDestruct "Hfields" as "(HmemLog&HmemStart&HdiskEnd&HnextDiskEnd&HmemLogMap&Hshutdown&Hnthread)".
    wp_loadField.
    wp_apply wp_slice_len; wp_pures.
    change (int.val (word.divu (word.sub 4096 8) 8)) with LogSz.
    wp_if_destruct.
    - wp_loadField.
      wp_apply (wp_condWait with "[$His_cond2 $Hlocked $His_lock HmemLog HmemStart HdiskEnd HnextDiskEnd HmemLogMap Hshutdown Hnthread Hrest]").
      { iExists _, _; iFrame. }
      iIntros "(Hlocked&Hlkinv)".
      wp_pures.
      iApply ("HΦ" with "[$]").
    - iApply "HΦ"; iFrame.
      iExists _, _; iFrame.
  }
  iIntros "(Hlocked&Hlkinv)".
Admitted.

Ltac shutdown_fields :=
  let shutdown := fresh "shutdown" in
  let nthread := fresh "nthread" in
  iDestruct (wal_linv_shutdown with "Hlkinv") as (shutdown nthread) "[[? ?] Hlkinv]";
  repeat wp_loadField;
  repeat wp_storeField;
  iSpecialize ("Hlkinv" with "[$] [$]");
  try (clear shutdown);
  try (clear nthread).

Lemma wp_inc_nthread l (st: loc) γ :
  {{{ readonly (l ↦[Walog.S :: "st"] #st) ∗ wal_linv st γ }}}
    struct.storeF WalogState.S "nthread" (struct.loadF Walog.S "st" #l)
    (struct.loadF WalogState.S "nthread" (struct.loadF Walog.S "st" #l) + #1)
    {{{ RET #(); wal_linv st γ }}}.
Proof.
  iIntros (Φ) "[#Hst Hlkinv] HΦ".
  shutdown_fields.
  iApply ("HΦ" with "[$]").
Qed.

Lemma wp_dec_nthread l (st: loc) γ :
  {{{ readonly (l ↦[Walog.S :: "st"] #st) ∗ wal_linv st γ }}}
    struct.storeF WalogState.S "nthread" (struct.loadF Walog.S "st" #l)
    (struct.loadF WalogState.S "nthread" (struct.loadF Walog.S "st" #l) - #1)
    {{{ RET #(); wal_linv st γ }}}.
Proof.
  iIntros (Φ) "[#Hst Hlkinv] HΦ".
  shutdown_fields.
  iApply ("HΦ" with "[$]").
Qed.

Theorem wp_Walog__logger l γ :
  {{{ is_wal l γ }}}
    Walog__logger #l
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "#Hwal HΦ".
  iMod (is_wal_read_mem with "Hwal") as "#Hmem".
  wp_call.
  iDestruct "Hmem" as (σₛ) "(Hfields&HcondLogger&HcondInstall&HcondShut&#Hlk)".
  iDestruct "Hfields" as "(Hf1&Hf2&Hf3&Hf4&Hf5&Hf6&Hf7)".
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "(Hlk_held&Hlkinv)".
  wp_pures.

  wp_apply (wp_inc_nthread with "[$Hf4 $Hlkinv]"); iIntros "Hlkinv".
  wp_pures.
  wp_bind (For _ _ _).
  wp_apply (wp_forBreak_cond (fun b => wal_linv σₛ.(wal_st) γ ∗ locked γ.(lock_name))%I
              with "[] [$Hlkinv $Hlk_held]").
  { iIntros "!>" (Φ') "(Hlkinv&Hlk_held) HΦ".
    shutdown_fields.
    wp_pures.
    wp_if_destruct.
    - wp_pures.
      wp_apply (wp_Walog__logAppend with "[$Hlkinv $Hlk_held]").
      { iFrame "#". }
      iIntros (progress) "(Hlkinv&Hlk_held)".
      wp_pures.
      destruct (negb progress); [ wp_if_true | wp_if_false ]; wp_pures.
      + wp_loadField.
        wp_apply (wp_condWait with "[$HcondLogger $Hlk $Hlkinv $Hlk_held]").
        iIntros "(Hlk_held&Hlkinv)".
        wp_pures.
        iApply ("HΦ" with "[$]").
      + iApply ("HΦ" with "[$]").
    - iApply ("HΦ" with "[$]").
  }
  iIntros "(Hlkinv&Hlk_held)".
  wp_apply util_proof.wp_DPrintf.
  wp_apply (wp_dec_nthread with "[$Hf4 $Hlkinv]"); iIntros "Hlkinv".
  wp_loadField.
  wp_apply (wp_condSignal with "HcondShut").
  wp_loadField.
  wp_apply (release_spec with "[$Hlk $Hlk_held $Hlkinv]").
  iApply ("HΦ" with "[//]").
Qed.

End heap.
