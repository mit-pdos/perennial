From Goose.github_com.mit_pdos.goose_nfsd Require Export wal.
From RecordUpdate Require Import RecordSet.

From Perennial.Helpers Require Export Transitions NamedProps Map.

From Perennial.algebra Require Export deletable_heap.
From Perennial.program_proof Require Export proof_prelude.
From Perennial.program_proof Require Export wal.lib.
From Perennial.program_proof Require Export wal.circ_proof.
From Perennial.program_proof Require Export wal.specs.

Canonical Structure circO := leibnizO circΣ.t.

Transparent slice.T.
Typeclasses Opaque struct_field_mapsto.

Class walG Σ :=
  { wal_circ         :> circG Σ;
    wal_circ_state   :> inG Σ (ghostR $ circO);
    wal_txn_id       :> inG Σ (ghostR $ prodO u64O natO);
    wal_list_update  :> inG Σ (ghostR $ listO updateO);
    wal_txns         :> inG Σ (ghostR $ listO $ prodO u64O (listO updateO));
    wal_nat          :> inG Σ (ghostR $ natO);
    wal_addr_set     :> inG Σ (ghostR $ gmapO ZO unitO);
  }.

Section goose_lang.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!walG Σ}.

Implicit Types (v:val) (z:Z).

Context (P: log_state.t -> iProp Σ).
Definition walN := nroot .@ "wal".
Let N := walN.
Let circN := walN .@ "circ".

Record wal_names :=
  { circ_name: circ_names;
    memStart_name : gname;
    memLog_name : gname;
    lock_name : gname;
    cs_name : gname;
    groupTxns_name : gen_heapG nat u64 Σ;
    txns_name : gname;
    new_installed_name : gname;
    being_installed_name : gname;
  }.

Implicit Types (γ: wal_names).
Implicit Types (s: log_state.t) (memLog: list update.t) (txns: list (u64 * list update.t)).
Implicit Types (pos: u64) (txn_id: nat).

Fixpoint compute_memLogMap (memLog : list update.t) (pos : u64) (m : gmap u64 u64) : gmap u64 u64 :=
  match memLog with
  | nil => m
  | u :: memLog' =>
    compute_memLogMap memLog' (word.add pos 1) (<[ update.addr u := pos ]> m)
  end.

(** low-level, unimportant state *)
Record lowState :=
  { memLogSlice: Slice.t;
    memLogMapPtr: loc;
    shutdown: bool;
    nthread: u64;
  }.

Global Instance lowState_eta: Settable _ :=
  settable! Build_lowState <memLogSlice; memLogMapPtr; shutdown; nthread>.

Global Instance lowState_witness: Inhabited lowState :=
  populate (Build_lowState inhabitant inhabitant inhabitant inhabitant).

Record locked_state :=
  { memStart: u64;
    diskEnd: u64;
    nextDiskEnd: u64;
    memLog: list update.t; }.

Global Instance locked_state_eta: Settable _ :=
  settable! Build_locked_state <memStart; diskEnd; nextDiskEnd; memLog>.

(** TODO: rename.

 [group_txn] no longer has anything to do with grouping, it's just a persistent
fact about a valid (transaction, pos) pair. *)
Definition group_txn γ txn_id (pos: u64) : iProp Σ :=
  readonly (mapsto (hG:=γ.(groupTxns_name)) txn_id 1%Qp pos).

(** the simple role of the memLog is to contain all the transactions in the
abstract state starting at the memStart_txn_id *)
Definition is_mem_memLog γ memLog txns memStart_txn_id : Prop :=
  apply_upds memLog ∅ =
  apply_upds (txn_upds (drop memStart_txn_id txns)) ∅.

Definition memLog_linv γ memStart (memLog: list update.t) : iProp Σ :=
  (∃ (memStart_txn_id: nat) (txns: list (u64 * list update.t)),
      "HownmemStart" ∷ own γ.(memStart_name) (● Excl' (memStart, memStart_txn_id)) ∗
      "HownmemLog" ∷ own γ.(memLog_name) (● Excl' memLog) ∗
      "Howntxns" ∷ own γ.(txns_name) (● Excl' txns) ∗
      "HmemStart_txn" ∷ group_txn γ memStart_txn_id memStart ∗
      (* Here we establish what the memLog contains, which is necessary for reads
      to work (they read through memLogMap, but the lock invariant establishes
      that this matches memLog). *)
      "%His_memLog" ∷ ⌜is_mem_memLog γ memLog txns memStart_txn_id⌝).

Definition wal_linv_fields st σ: iProp Σ :=
  (∃ σₗ,
      "Hfield_ptsto" ∷
         ("HmemLog" ∷ st ↦[WalogState.S :: "memLog"] (slice_val σₗ.(memLogSlice)) ∗
          "HmemStart" ∷ st ↦[WalogState.S :: "memStart"] #σ.(memStart) ∗
          "HdiskEnd" ∷ st ↦[WalogState.S :: "diskEnd"] #σ.(diskEnd) ∗
          "HnextDiskEnd" ∷ st ↦[WalogState.S :: "nextDiskEnd"] #σ.(nextDiskEnd) ∗
          "HmemLogMap" ∷ st ↦[WalogState.S :: "memLogMap"] #σₗ.(memLogMapPtr) ∗
          "Hshutdown" ∷ st ↦[WalogState.S :: "shutdown"] #σₗ.(shutdown) ∗
          "Hnthread" ∷ st ↦[WalogState.S :: "nthread"] #σₗ.(nthread)) ∗
  "His_memLogMap" ∷ is_map σₗ.(memLogMapPtr) (compute_memLogMap σ.(memLog) σ.(memStart) ∅) ∗
  "His_memLog" ∷ updates_slice σₗ.(memLogSlice) σ.(memLog))%I.

(** the lock invariant protecting the WalogState, corresponding to l.memLock *)
Definition wal_linv (st: loc) γ : iProp Σ :=
  ∃ σ,
    "Hfields" ∷ wal_linv_fields st σ ∗
    "#HdiskEnd_at_least" ∷ diskEnd_at_least γ.(circ_name) (int.val σ.(diskEnd)) ∗
    "#Hstart_at_least" ∷ start_at_least γ.(circ_name) σ.(memStart) ∗
    "HmemLog_linv" ∷ memLog_linv γ σ.(memStart) σ.(memLog) ∗
    (* a group-commit transaction is logged by setting nextDiskEnd to its pos -
       these conditions ensure that it is recorded as an absorption boundary,
       since at this point it becomes a plausible crash point *)
    "HnextDiskEnd_txn" ∷ ( ∃ (nextDiskEnd_txn_id : nat),
      group_txn γ nextDiskEnd_txn_id σ.(nextDiskEnd) )
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

Global Instance wal_state_eta : Settable _ :=
  settable! Build_wal_state <memLock; wal_d; circ; wal_st; condLogger; condInstall; condShut>.

(* I guess this needs no arguments because the in-memory state doesn't
    correspond directly to any part of the abstract state *)
Definition is_wal_mem (l: loc) γ : iProp Σ :=
  ∃ σₛ,
    "Hstfields" ∷ ("memlock" ∷ readonly (l ↦[Walog.S :: "memLock"] #σₛ.(memLock)) ∗
     "d" ∷ readonly (l ↦[Walog.S :: "d"] σₛ.(wal_d)) ∗
     "circ" ∷ readonly (l ↦[Walog.S :: "circ"] #σₛ.(circ)) ∗
     "st" ∷ readonly (l ↦[Walog.S :: "st"] #σₛ.(wal_st)) ∗
     "condLogger" ∷ readonly (l ↦[Walog.S :: "condLogger"] #σₛ.(condLogger)) ∗
     "condInstall" ∷ readonly (l ↦[Walog.S :: "condInstall"] #σₛ.(condInstall)) ∗
     "condShut" ∷ readonly (l ↦[Walog.S :: "condShut"] #σₛ.(condShut))) ∗
    "cond_logger" ∷ lock.is_cond σₛ.(condLogger) #σₛ.(memLock) ∗
    "cond_install" ∷ lock.is_cond σₛ.(condInstall) #σₛ.(memLock) ∗
    "cond_shut" ∷ lock.is_cond σₛ.(condShut) #σₛ.(memLock) ∗
    "lk" ∷ is_lock N γ.(lock_name) #σₛ.(memLock) (wal_linv σₛ.(wal_st) γ).

Global Instance is_wal_mem_persistent : Persistent (is_wal_mem l γ) := _.

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

(* this part of the invariant holds the installed disk blocks from the data
region of the disk and relates them to the logical installed disk, computed via
the updates through some installed transaction. *)
Definition is_installed γ d txns installed_lb : iProp Σ :=
  ∃ (installed_txn_id: nat) (new_installed_txn_id: nat) (being_installed: gmap Z unit) diskStart,
    "Hstart_is" ∷ start_is γ.(circ_name) (1/4) diskStart ∗
    "#Hstart_txn" ∷ group_txn γ installed_txn_id diskStart ∗
    (* TODO: the other half of these are owned by the installer, giving it full
     knowledge of in-progress installations and exclusive update rights; need to
     write down what it maintains as part of its loop invariant *)
    "Howninstalled" ∷ (own γ.(new_installed_name) (● Excl' new_installed_txn_id) ∗
     own γ.(being_installed_name) (● Excl' being_installed)) ∗
    "%Hinstalled_bounds" ∷ ⌜(installed_lb ≤ installed_txn_id ≤ new_installed_txn_id)%nat⌝ ∗
    "Hdata" ∷ ([∗ map] a ↦ _ ∈ d,
     ∃ (b: Block),
       (* every disk block has at least through installed_txn_id (most have
        exactly, but some blocks may be in the process of being installed) *)
       ⌜let txn_id' := (if being_installed !! a
                        then new_installed_txn_id
                        else installed_txn_id) in
        let txns := take txn_id' txns in
        apply_upds (txn_upds txns) d !! a = Some b⌝ ∗
       a d↦ b ∗ ⌜2 + LogSz ≤ a⌝).

(* weakening of [is_installed] for the sake of reading *)
Definition is_installed_read γ d txns installed_lb : iProp Σ :=
  ([∗ map] a ↦ _ ∈ d,
    ∃ (b: Block),
      ⌜∃ txn_id', (installed_lb ≤ txn_id')%nat ∧
      let txns := take txn_id' txns in
      apply_upds (txn_upds txns) d !! a = Some b⌝ ∗
      a d↦ b ∗ ⌜2 + LogSz ≤ a⌝)%I.

Global Instance is_installed_read_Timeless {γ d txns installed_lb} :
  Timeless (is_installed_read γ d txns installed_lb).
Proof.
  apply _.
Qed.

Theorem is_installed_weaken_read γ d txns installed_lb :
  is_installed γ d txns installed_lb -∗
  is_installed_read γ d txns installed_lb ∗ (is_installed_read γ d txns installed_lb -∗
                                            is_installed γ d txns installed_lb).
Proof.
  rewrite /is_installed /is_installed_read.
  iIntros "I".
  iNamed "I".
  iSplitL "Hdata".
  { iApply (big_sepM_mono with "Hdata").
    iIntros (a b0 Hlookup) "HI".
    iDestruct "HI" as (b') "(%&Hb&%)".
    iExists b'; iFrame.
    iPureIntro.
    split; auto.
    destruct (being_installed !! a); [ exists new_installed_txn_id | exists installed_txn_id ].
    - split; auto; lia.
    - split; auto; lia. }
  iIntros "Hmap".
  admit.
Admitted.

Theorem is_installed_to_read γ d txns installed_lb E :
  ▷ is_installed γ d txns installed_lb -∗
    (|={E}=> is_installed_read γ d txns installed_lb) ∗
    ▷ (is_installed_read γ d txns installed_lb -∗
       is_installed γ d txns installed_lb).
Proof.
  iIntros "Hfull".
  iDestruct (is_installed_weaken_read with "Hfull") as "[Hread $]".
  iDestruct "Hread" as ">$".
  auto.
Qed.

(** the more complicated role of memLog is to correctly store committed
transactions if we roll it back to a [group_txn] boundary, which is what happens
on crash where [memLog] is restored from the circ log *)
(* This is complicated a bit by the fact that the memLog can contain elements
   before diskStart (before the installer has a chance to trim them), contains
   all the logged updates, contains grouped transactions in groupTxns, and
   finally contains a tail of transactions that are subject to absorption and
   not owned by the logger. *)
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
Definition log_inv γ txns diskEnd_txn_id : iProp Σ :=
  ∃ (memStart: u64) (memStart_txn_id: nat) (memLog: list update.t) (cs: circΣ.t),
    own γ.(memStart_name) (◯ (Excl' (memStart, memStart_txn_id))) ∗
    own γ.(memLog_name) (◯ Excl' memLog) ∗
    own γ.(cs_name) (◯ (Excl' cs)) ∗
    ⌜circ_matches_memlog memStart memLog cs⌝ ∗
    is_crash_memlog γ memStart_txn_id memLog txns memStart ∗
    (* this sub-part establishes that diskEnd_txn_id is the durable point *)
    (∃ (diskEnd: u64),
        group_txn γ diskEnd_txn_id diskEnd ∗
        diskEnd_is γ.(circ_name) (1/4) (int.val diskEnd)).

Definition is_durable γ txns durable_lb : iProp Σ :=
  (∃ (diskEnd_txn_id: nat),
    (* TODO(tej): does this make sense? it's the only constraint on
        durable_lb *)
      ⌜(durable_lb ≤ diskEnd_txn_id)%nat ⌝ ∗
       log_inv γ txns diskEnd_txn_id).

Definition txns_pos_map (txns: list (u64 * list update.t)) : gmap nat u64 :=
  list_to_imap txns.*1.

Theorem txns_pos_is_txn txns (txn_id: nat) (pos: u64) :
  is_txn txns txn_id pos <-> txns_pos_map txns !! txn_id = Some pos.
Proof.
  rewrite /is_txn /txns_pos_map.
  rewrite -list_lookup_fmap.
  rewrite lookup_list_to_imap //.
Qed.

Definition is_groupTxns γ txns : iProp Σ :=
    gen_heap_ctx (hG:=γ.(groupTxns_name)) (txns_pos_map txns) ∗
    ([∗ map] txn_id↦pos ∈ (txns_pos_map txns),
     group_txn γ txn_id pos).

Theorem alloc_group_txn γ txns E pos upds :
  is_groupTxns γ txns ={E}=∗
  is_groupTxns γ (txns ++ [(pos, upds)]) ∗ group_txn γ (length txns) pos.
Proof.
  iIntros "[Hctx Htxns]".
  rewrite /is_groupTxns /txns_pos_map.
  rewrite fmap_app /=.
  rewrite list_to_imap_app1.
  assert (list_to_imap txns.*1 !! length txns.*1 = None) as Hempty.
  { rewrite lookup_list_to_imap.
    apply lookup_ge_None_2; lia. }
  iMod (gen_heap_alloc _ (length txns.*1) pos with "Hctx") as "[$ Hmapsto]"; first by auto.
  rewrite -> big_sepM_insert by auto.
  iFrame.
  iMod (readonly_alloc_1 with "Hmapsto") as "#Hgroup_txn".
  iModIntro.
  iFrame "#".
  autorewrite with len.
  iFrame "#".
Qed.

Theorem is_groupTxns_complete γ txns txn_id pos :
  is_txn txns txn_id pos ->
  is_groupTxns γ txns -∗ group_txn γ txn_id pos.
Proof.
  rewrite txns_pos_is_txn; intros Hlookup.
  iIntros "[Hctx #Htxns]".
  iDestruct (big_sepM_lookup_acc _ _ _ _ Hlookup with "Htxns") as "[$ _]".
Qed.

Theorem group_txn_valid γ txns E txn_id pos :
  ↑nroot.@"readonly" ⊆ E ->
  is_groupTxns γ txns -∗
  group_txn γ txn_id pos -∗
  |={E}=> ⌜is_txn txns txn_id pos⌝ ∗ is_groupTxns γ txns.
Proof.
  rewrite /is_groupTxns /group_txn.
  iIntros (Hsub) "Hgroup Htxn".
  iDestruct "Hgroup" as "[Hctx Hgroup_txns]".
  iMod (readonly_load with "Htxn") as (q) "Htxn_id"; first by set_solver.
  iDestruct (gen_heap_valid with "Hctx Htxn_id") as %Hlookup.
  apply txns_pos_is_txn in Hlookup.
  iIntros "!>".
  iSplit; eauto.
Qed.

(** the complete wal invariant *)
Definition is_wal_inner (l : loc) γ s : iProp Σ :=
    "%Hwf" ∷ ⌜wal_wf s⌝ ∗
    "Hmem" ∷ is_wal_mem l γ ∗
    "Howntxns" ∷ own γ.(txns_name) (◯ Excl' s.(log_state.txns)) ∗
    "Hdurable" ∷ is_durable γ s.(log_state.txns) s.(log_state.durable_lb) ∗
    "Hinstalled" ∷ is_installed γ s.(log_state.d) s.(log_state.txns) s.(log_state.installed_lb) ∗
    "Htxns" ∷ is_groupTxns γ s.(log_state.txns).

Definition is_wal (l : loc) γ : iProp Σ :=
  inv N (∃ σ, is_wal_inner l γ σ ∗ P σ) ∗
  is_circular circN (circular_pred γ) γ.(circ_name).

Theorem is_wal_read_mem l γ : is_wal l γ -∗ |={⊤}=> ▷ is_wal_mem l γ.
Proof.
  iIntros "#Hwal".
  iDestruct "Hwal" as "[Hinv _]".
  iApply (inv_dup_acc with "Hinv"); first by set_solver.
  iIntros "HinvI".
  iDestruct "HinvI" as (σ) "[HinvI HP]".
  iDestruct "HinvI" as "(%Hwf&#Hmem&Hrest)".
  iSplitL; last by auto.
  iExists _; iFrame.
  by iFrame "∗ Hmem".
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
  iNamed "Hlkinv".
  iNamed "Hfields".
  iNamed "Hfield_ptsto".
  iExists _, _.
  iFrame.
  iIntros (shutdown' nthread') "Hshutdown Hnthread".
  iExists σ; iFrame "# ∗".
  iExists (set shutdown (λ _, shutdown') (set nthread (λ _, nthread') σₗ)); simpl.
  iFrame.
Qed.

Theorem wal_linv_load_nextDiskEnd st γ :
  wal_linv st γ -∗
    ∃ (x:u64),
      st ↦[WalogState.S :: "nextDiskEnd"]{1/2} #x ∗
         (st ↦[WalogState.S :: "nextDiskEnd"]{1/2} #x -∗ wal_linv st γ).
Proof.
  iIntros "Hlkinv".
  iNamed "Hlkinv".
  iNamed "Hfields".
  iNamed "Hfield_ptsto".
  iDestruct "HnextDiskEnd" as "[HnextDiskEnd1 HnextDiskEnd2]".
  iExists _; iFrame "HnextDiskEnd2".
  iIntros "HnextDiskEnd2".
  iCombine "HnextDiskEnd1 HnextDiskEnd2" as "HnextDiskEnd".
  iExists _; iFrame "# ∗".
  iExists _; iFrame.
Qed.

Lemma wal_wf_txns_mono_pos {σ txn_id1 pos1 txn_id2 pos2} :
  wal_wf σ ->
  is_txn σ.(log_state.txns) txn_id1 pos1 ->
  is_txn σ.(log_state.txns) txn_id2 pos2 ->
  int.val pos1 < int.val pos2 ->
  (txn_id1 ≤ txn_id2)%nat.
Proof.
  destruct 1 as (_&Hmono&_).
  rewrite /is_txn; intros.
  destruct (decide (txn_id1 ≤ txn_id2)%nat); first by auto.
  assert (txn_id2 < txn_id1)%nat as Hord by lia.
  eapply Hmono in Hord; eauto.
  word. (* contradiction from [pos1 = pos2] *)
Qed.

End goose_lang.

Ltac destruct_is_wal :=
  iMod (is_wal_read_mem with "Hwal") as "#Hmem";
  wp_call;
  iNamed "Hmem"; iNamed "Hstfields".
