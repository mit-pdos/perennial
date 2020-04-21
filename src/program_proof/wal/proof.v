From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From RecordUpdate Require Import RecordSet.

From Perennial.Helpers Require Import Transitions.

From Perennial.algebra Require Import deletable_heap.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import wal.abstraction.
From Perennial.program_proof Require Import wal.circ_proof.
From Perennial.program_proof Require Import wal.specs.

Definition LogPositionT := wal.LogPosition.
Definition LogPosition := u64.
Definition LogDiskBlocks := 513.
Hint Unfold LogDiskBlocks.

Canonical Structure circO := leibnizO circΣ.t.

Transparent slice.T.

Class walG Σ :=
  { wal_circ         :> circG Σ;
    wal_circ_state   :> inG Σ (ghostR $ circO);
    wal_txn_id       :> inG Σ (ghostR $ prodO u64O natO);
    wal_list_update  :> inG Σ (ghostR $ listO updateO);
    wal_txns         :> inG Σ (ghostR $ listO $ prodO u64O (listO updateO));
    wal_nat          :> inG Σ (ghostR $ natO);
    wal_addr_set     :> inG Σ (ghostR $ gmapO ZO unitO);
  }.

Section heap.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!walG Σ}.

Implicit Types (Φ: val → iProp Σ).
Implicit Types (v:val) (z:Z).

Context (P: log_state.t -> iProp Σ).
Context (walN : namespace).
Let N := nroot .@ "wal" .@ walN.
Definition circN: namespace := N .@ "circ".

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

Instance lowState_eta: Settable _ :=
  settable! Build_lowState <memLogSlice; memLogMapPtr; shutdown; nthread>.

Record locked_state :=
  { memStart: u64;
    diskEnd: u64;
    nextDiskEnd: u64;
    memLog: list update.t; }.

Instance locked_state_eta: Settable _ :=
  settable! Build_locked_state <memStart; diskEnd; nextDiskEnd; memLog>.

Definition group_txn γ txn_id (pos: u64) : iProp Σ :=
  readonly (mapsto (hG:=γ.(groupTxns_name)) txn_id 1%Qp pos).

(** the simple role of the memLog is to contain all the transactions in the
abstract state starting at the memStart_txn_id *)
Definition is_mem_memLog γ memLog txns memStart_txn_id : Prop :=
  apply_upds memLog ∅ =
  apply_upds (txn_upds (drop memStart_txn_id txns)) ∅.

Definition memLog_linv γ memStart (memLog: list update.t) : iProp Σ :=
  (∃ (memStart_txn_id: nat) (txns: list (u64 * list update.t)),
      own γ.(memStart_name) (● Excl' (memStart, memStart_txn_id)) ∗
      own γ.(memLog_name) (● Excl' memLog) ∗
      own γ.(txns_name) (● Excl' txns) ∗
      group_txn γ memStart_txn_id memStart ∗
      (* Here we establish what the memLog contains, which is necessary for reads
      to work (they read through memLogMap, but the lock invariant establishes
      that this matches memLog). *)
      ⌜is_mem_memLog γ memLog txns memStart_txn_id⌝).

(* TODO: de-duplicate this with the one in marshal_proof.v *)
Definition u64val (x: u64): val := #x.

Definition wal_linv_fields st σ: iProp Σ :=
  (∃ σₗ,
      (st ↦[WalogState.S :: "memLog"] (slice_val σₗ.(memLogSlice)) ∗
       st ↦[WalogState.S :: "memStart"] #σ.(memStart) ∗
       st ↦[WalogState.S :: "diskEnd"] #σ.(diskEnd) ∗
       st ↦[WalogState.S :: "nextDiskEnd"] #σ.(nextDiskEnd) ∗
       st ↦[WalogState.S :: "memLogMap"] #σₗ.(memLogMapPtr) ∗
       st ↦[WalogState.S :: "shutdown"] #σₗ.(shutdown) ∗
       st ↦[WalogState.S :: "nthread"] #σₗ.(nthread)) ∗
  is_map σₗ.(memLogMapPtr) (u64val <$> compute_memLogMap σ.(memLog) σ.(memStart) ∅, u64val (U64 0)) ∗
  updates_slice σₗ.(memLogSlice) σ.(memLog))%I.

(** the lock invariant protecting the WalogState, corresponding to l.memLock *)
Definition wal_linv (st: loc) γ : iProp Σ :=
  ∃ σ,
    wal_linv_fields st σ ∗
    diskEnd_at_least γ.(circ_name) (int.val σ.(diskEnd)) ∗
    start_at_least γ.(circ_name) σ.(memStart) ∗
    memLog_linv γ σ.(memStart) σ.(memLog) ∗
    (* a group-commit transaction is logged by setting nextDiskEnd to its pos -
       these conditions ensure that it is recorded as an absorption boundary,
       since at this point it becomes a plausible crash point *)
    ( ∃ (nextDiskEnd_txn_id : nat),
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

Instance wal_state_eta : Settable _ :=
  settable! Build_wal_state <memLock; wal_d; circ; wal_st; condLogger; condInstall; condShut>.

(* I guess this needs no arguments because the in-memory state doesn't
    correspond directly to any part of the abstract state *)
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
    is_lock N γ.(lock_name) #σₛ.(memLock) (wal_linv σₛ.(wal_st) γ).

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

(* this part of the invariant holds the installed disk blocks from the data
region of the disk and relates them to the logical installed disk, computed via
the updates through some installed transaction. *)
Definition is_installed γ d txns installed_lb : iProp Σ :=
  ∃ (installed_txn_id: nat) (new_installed_txn_id: nat) (being_installed: gmap Z unit) diskStart,
    start_is γ.(circ_name) (1/4) diskStart ∗
    group_txn γ installed_txn_id diskStart ∗
    (* TODO: the other half of these are owned by the installer, giving it full
     knowledge of in-progress installations and exclusive update rights; need to
     write down what it maintains as part of its loop invariant *)
    (own γ.(new_installed_name) (● Excl' new_installed_txn_id) ∗
     own γ.(being_installed_name) (● Excl' being_installed)) ∗
    ⌜(installed_lb ≤ installed_txn_id ≤ new_installed_txn_id)%nat⌝ ∗
    ([∗ map] a ↦ _ ∈ d,
     ∃ (b: Block),
       (* every disk block has at least through installed_txn_id (most have
        exactly, but some blocks may be in the process of being installed) *)
       ⌜let txn_id' := (if being_installed !! a
                        then new_installed_txn_id
                        else installed_txn_id) in
        let txns := take txn_id' txns in
        apply_upds (txn_upds txns) d !! a = Some b⌝ ∗
       a d↦ b ∗ ⌜2 + LogSz ≤ int.val a⌝).

(* weakening of [is_installed] for the sake of reading *)
Definition is_installed_read γ d txns installed_lb : iProp Σ :=
  ([∗ map] a ↦ _ ∈ d,
    ∃ (b: Block),
      ⌜∃ txn_id', (installed_lb ≤ txn_id')%nat ∧
      let txns := take txn_id' txns in
      apply_upds (txn_upds txns) d !! a = Some b⌝ ∗
      a d↦ b ∗ ⌜2 + LogSz ≤ int.val a⌝)%I.

Theorem is_installed_weaken_read γ d txns installed_lb :
  is_installed γ d txns installed_lb -∗ is_installed_read γ d txns installed_lb.
Proof.
  rewrite /is_installed /is_installed_read.
  iIntros "I".
  iDestruct "I" as (installed_txn_id new_installed_txn_id being_installed diskStart)
                     "(_&_&_&%&Hd)".
  iApply (big_sepM_mono with "Hd").
  iIntros (a b0 Hlookup) "HI".
  iDestruct "HI" as (b') "(%&Hb&%)".
  iExists b'; iFrame.
  iPureIntro.
  split; auto.
  destruct (being_installed !! a); [ exists new_installed_txn_id | exists installed_txn_id ].
  - split; auto; lia.
  - split; auto; lia.
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

Definition is_groupTxns γ txns : iProp Σ :=
  ∃ (groupTxns: gmap nat u64),
    gen_heap_ctx (hG:=γ.(groupTxns_name)) groupTxns ∗
    ⌜∀ txn_id pos, groupTxns !! txn_id = Some pos ->
                   is_txn txns txn_id pos⌝.

Theorem group_txn_valid γ txns E txn_id pos :
  ↑nroot.@"readonly" ⊆ E ->
  is_groupTxns γ txns -∗
  group_txn γ txn_id pos -∗
  |={E}=> ⌜is_txn txns txn_id pos⌝ ∗ is_groupTxns γ txns.
Proof.
  rewrite /is_groupTxns /group_txn.
  iIntros (Hsub) "Hgroup Htxn".
  iDestruct "Hgroup" as (groupTxns) "[Hctx %HgroupTxns]".
  iMod (readonly_load with "Htxn") as (q) "Htxn_id"; first by set_solver.
  iDestruct (gen_heap_valid with "Hctx Htxn_id") as %Hlookup.
  iIntros "!>".
  iSplit; eauto.
Qed.

(** the complete wal invariant *)
Definition is_wal_inner (l : loc) γ s : iProp Σ :=
    ⌜wal_wf s⌝ ∗
    is_wal_mem l γ ∗
    own γ.(txns_name) (◯ Excl' s.(log_state.txns)) ∗
    is_durable γ s.(log_state.txns) s.(log_state.durable_lb) ∗
    is_installed γ s.(log_state.d) s.(log_state.txns) s.(log_state.installed_lb) ∗
    is_groupTxns γ s.(log_state.txns).

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
  iDestruct "Hlkinv" as (σ) "[Hfields Hrest]".
  iDestruct "Hfields" as (σₗ) "(Hfield_ptsto&His_memLogMap&His_memLog)".
  iDestruct "Hfield_ptsto" as "(HmemLog&HmemStart&HdiskEnd&HnextDiskEnd&HmemLogMap&Hshutdown&Hnthread)".
  iExists _, _.
  iFrame.
  iIntros (shutdown' nthread') "Hshutdown Hnthread".
  iExists σ; iFrame "Hrest".
  iExists (set shutdown (λ _, shutdown') (set nthread (λ _, nthread') σₗ)); simpl.
  iFrame.
Qed.

Theorem wp_copyUpdateBlock stk E (u: u64 * Slice.t) b :
  {{{ is_block (snd u) b }}}
    copyUpdateBlock (update_val u) @ stk; E
  {{{ (s':Slice.t), RET (slice_val s'); is_block (snd u) b ∗ is_block s' b }}}.
Proof.
  iIntros (Φ) "Hb HΦ".
  destruct u as [a s]; simpl.
  wp_call.
  wp_apply wp_new_slice; first by auto.
  iIntros (s') "Hs'".
  iDestruct (is_slice_to_small with "Hs'") as "Hs'".
  wp_pures.
  wp_apply (wp_SliceCopy_full with "[$Hb $Hs']").
  { iPureIntro.
    autorewrite with len.
    rewrite length_Block_to_vals.
    reflexivity. }
  iIntros "(Hs&Hs')".
  wp_pures.
  iApply ("HΦ" with "[$]").
Qed.

(* TODO: move to map/map.v *)
Lemma map_get_fmap {V} {m:gmap u64 V} {def: V} {to_val: V -> val} {a v ok} :
  map_get (to_val <$> m, to_val def) a = (v, ok) ->
  exists x, v = to_val x.
Proof.
  rewrite /map_get.
  inversion_clear 1; subst.
  destruct ((to_val <$> m) !! a) eqn:Hlookup; eauto.
  rewrite lookup_fmap in Hlookup.
  apply fmap_Some in Hlookup as [x [Hlookup ->]]; eauto.
Qed.

Opaque struct.t.

(* TODO: move out of here to some general wal library *)
Theorem wp_SliceGet_updates stk E bk_s bs (i: u64) (u: update.t) :
  {{{ updates_slice bk_s bs ∗ ⌜bs !! int.nat i = Some u⌝ }}}
    SliceGet (struct.t Update.S) (slice_val bk_s) #i @ stk; E
  {{{ uv, RET (update_val uv);
      ⌜uv.1 = u.(update.addr)⌝ ∗
      is_block uv.2 u.(update.b) ∗
      (is_block uv.2 u.(update.b) -∗ updates_slice bk_s bs)
  }}}.
Proof.
  iIntros (Φ) "[Hupds %Hlookup] HΦ".
  iDestruct "Hupds" as (bks) "[Hbk_s Hbks]".
  iDestruct (big_sepL2_lookup_2_some _ _ _ _ _ Hlookup with "Hbks")
    as %[b_upd Hlookup_bs].
  iDestruct (is_slice_small_acc with "Hbk_s") as "[Hbk_s Hbk_s_rest]".
  wp_apply (wp_SliceGet with "[$Hbk_s]").
  { iPureIntro.
    rewrite list_lookup_fmap.
    rewrite Hlookup_bs //. }
  iIntros "[Hbk_s _]".
  iDestruct ("Hbk_s_rest" with "Hbk_s") as "Hbk_s".
  iApply "HΦ".
  iDestruct (big_sepL2_lookup_acc with "Hbks") as "[Hbi Hbks]"; eauto.
  destruct u as [a b]; simpl.
  iDestruct "Hbi" as "[Hbi <-]".
  iSplit; first by auto.
  iFrame.
  iIntros "Hbi".
  iSpecialize ("Hbks" with "[$Hbi //]").
  rewrite /updates_slice.
  iExists _; iFrame.
Qed.

Lemma memLogMap_ok_memLog_lookup memStart memLog a i :
  int.val memStart + Z.of_nat (length memLog) < 2^64 ->
  map_get (u64val <$> compute_memLogMap memLog memStart ∅, u64val 0) a
  = (u64val i, true) ->
  ∃ b, memLog !! int.nat (word.sub i memStart) = Some (update.mk a b)
  (* also, i is the highest index such that this is true *).
Proof.
  intros Hbound Hlookup.
  apply map_get_true in Hlookup.
  rewrite lookup_fmap in Hlookup.
  apply fmap_Some in Hlookup as [i' [Hlookup Heq]].
  inversion Heq; subst.
  assert (int.val memStart ≤ int.val i') by admit. (* from how memLogMap is computed and lack of overflow *)
  replace (int.nat (word.sub i' memStart)) with (int.nat i' - int.nat memStart)%nat by word.
  (* this is hard, induction is hard with this left fold *)
Admitted.

Theorem wp_WalogState__readMem γ (st: loc) σ (a: u64) :
  {{{ wal_linv_fields st σ ∗
      memLog_linv γ σ.(memStart) σ.(memLog) }}}
    WalogState__readMem #st #a
  {{{ b_s b (ok:bool), RET (slice_val b_s, #ok);
      if ok then is_block b_s b ∗
                 ⌜apply_upds σ.(memLog) ∅ !! int.val a = Some b⌝ ∗
                 memLog_linv γ σ.(memStart) σ.(memLog)
      else True
  }}}.
Proof.
  iIntros (Φ) "(Hfields&HmemLog_inv) HΦ".
  iDestruct "Hfields" as (σₗ) "(Hfield_ptsto&His_memLogMap&His_memLog)".
  iDestruct "Hfield_ptsto" as "(HmemLog&HmemStart&HdiskEnd&HnextDiskEnd&HmemLogMap&Hshutdown&Hnthread)".
  wp_call.
  wp_loadField.
  wp_apply (wp_MapGet with "His_memLogMap").
  iIntros (v ok) "(%Hmapget&His_memLogMap)".
  destruct (map_get_fmap Hmapget) as [i ->].
  wp_pures.
  wp_if_destruct.
  - wp_apply util_proof.wp_DPrintf.
    wp_loadField. wp_loadField.
    apply memLogMap_ok_memLog_lookup in Hmapget as [b HmemLog_lookup];
      last by admit. (* TODO: in-bounds proof *)
    wp_apply (wp_SliceGet_updates with "[$His_memLog]"); eauto.
    simpl.
    iIntros ([a' u_s]) "(<-&Hb&His_memLog)".
    wp_apply (wp_copyUpdateBlock with "Hb").
    iIntros (s') "[Hb Hb_new]".
    iSpecialize ("His_memLog" with "Hb").
    wp_pures.
    iApply "HΦ".
    iFrame.
    simpl in HmemLog_lookup |- *.
    (* TODO: this comes from HmemLog_lookup plus that a' is maximal (the
    apply_upds formulation is actually a good way to phrase it, especially since
    [apply_upds] and [compute_memLogMap] are similar fold_left's) *)
Admitted.

Ltac destruct_is_wal :=
  iMod (is_wal_read_mem with "Hwal") as "#Hmem";
  wp_call;
  iDestruct "Hmem" as (σₛ) "(Hfields&HcondLogger&HcondInstall&HcondShut&#Hlk)";
  iDestruct "Hfields" as "(Hf1&Hf2&Hf3&Hf4&Hf5&Hf6&Hf7)".

Theorem wp_Walog__ReadMem (Q: option Block -> iProp Σ) l γ a :
  {{{ is_wal l γ ∗
       (∀ σ σ' mb,
         ⌜wal_wf σ⌝ -∗
         ⌜relation.denote (log_read_cache a) σ σ' mb⌝ -∗
         (P σ ={⊤ ∖ ↑N}=∗ P σ' ∗ Q mb))
   }}}
    Walog__ReadMem #l #a
  {{{ (ok:bool) bl, RET (slice_val bl, #ok); if ok
                                             then ∃ b, is_block bl b ∗ Q (Some b)
                                             else Q None}}}.
Proof.
  iIntros (Φ) "[#Hwal Hfupd] HΦ".
  destruct_is_wal.
  wp_loadField.
  wp_apply (acquire_spec with "Hlk"). iIntros "(Hlocked&Hlkinv)".
  wp_loadField.
Abort.

Theorem wal_linv_load_nextDiskEnd st γ :
  wal_linv st γ -∗
    ∃ (x:u64),
      st ↦[WalogState.S :: "nextDiskEnd"]{1/2} #x ∗
         (st ↦[WalogState.S :: "nextDiskEnd"]{1/2} #x -∗ wal_linv st γ).
Proof.
  iIntros "Hlkinv".
  iDestruct "Hlkinv" as (σ) "(Hfields&Hrest)".
  iDestruct "Hfields" as (σₗ) "(Hfield_ptsto&His_memLogMap&His_memLog)".
  iDestruct "Hfield_ptsto" as "(HmemLog&HmemStart&HdiskEnd&HnextDiskEnd&HmemLogMap&Hshutdown&Hnthread)".
  iDestruct "HnextDiskEnd" as "[HnextDiskEnd1 HnextDiskEnd2]".
  iExists _; iFrame.
  iIntros "HnextDiskEnd2".
  iCombine "HnextDiskEnd1 HnextDiskEnd2" as "HnextDiskEnd".
  iExists _; iFrame.
  iExists _; iFrame.
Qed.

Theorem wp_endGroupTxn st γ :
  {{{ wal_linv st γ }}}
    WalogState__endGroupTxn #st
  {{{ RET #(); wal_linv st γ }}}.
Proof.
  iIntros (Φ) "Hlkinv HΦ".
  iDestruct "Hlkinv" as (σ) "(Hfields&Hrest)".
  iDestruct "Hfields" as (σₗ) "(Hfield_ptsto&His_memLogMap&His_memLog)".
  iDestruct "Hfield_ptsto" as "(HmemLog&HmemStart&HdiskEnd&HnextDiskEnd&HmemLogMap&Hshutdown&Hnthread)".
  rewrite -wp_fupd.
  wp_call.
  wp_loadField. wp_loadField. wp_apply wp_slice_len. wp_storeField.
  iApply "HΦ".
  iDestruct (updates_slice_len with "His_memLog") as %HmemLog_len.
  iExists (set nextDiskEnd (λ _, word.add σ.(memStart) σₗ.(memLogSlice).(Slice.sz)) σ).
  simpl.
  iSplitL "HmemLog HmemStart HdiskEnd HnextDiskEnd HmemLogMap Hshutdown Hnthread His_memLogMap His_memLog".
  { iModIntro.
    iExists σₗ; simpl.
    iFrame. }
  iDestruct "Hrest" as "($&$&$&HnextDiskEnd)".
  (* TODO: definitely not enough, need the wal invariant to allocate a new group_txn *)
Admitted.

Theorem is_txn_bound txns diskEnd_txn_id diskEnd :
  is_txn txns diskEnd_txn_id diskEnd ->
  (diskEnd_txn_id ≤ length txns)%nat.
Proof.
  rewrite /is_txn -list_lookup_fmap.
  intros H%lookup_lt_Some.
  autorewrite with len in H; lia.
Qed.

Theorem wal_wf_update_durable :
  relation.wf_preserved (update_durable) wal_wf.
Proof.
  intros s1 s2 [] Hwf ?; simpl in *; monad_inv.
  destruct Hwf as (Hwf1&Hwf2&Hwf3).
  destruct s1; split; unfold log_state.updates in *; simpl in *; eauto.
  split; eauto.
  lia.
Qed.

(* just an example, to work out the Flush proof without all the complications *)
Theorem wp_updateDurable (Q: iProp Σ) l γ :
  {{{ is_wal l γ ∗
       (∀ σ σ' b,
         ⌜wal_wf σ⌝ -∗
         ⌜relation.denote (update_durable) σ σ' b⌝ -∗
         (P σ ={⊤ ∖ ↑N}=∗ P σ' ∗ Q))
   }}}
    Skip
  {{{ RET #(); Q}}}.
Proof.
  iIntros (Φ) "[#Hwal Hfupd] HΦ".
  iDestruct "Hwal" as "[Hwal Hcirc]".
  iInv "Hwal" as "Hinv".
  wp_call.
  iDestruct "Hinv" as (σ) "(Hinner&HP)".
  iDestruct "Hinner" as "(%Hwf&Hmem&Howntxns&Hdurable&Hinstalled&Htxns)".
  iDestruct "Hdurable" as (diskEnd_txn_id Hdurable_bound) "Hloginv".
  iDestruct "Hloginv" as (memStart memStart_txn_id memLog cs)
                           "(HownmemStart&HownmemLog&Howncs&%Hcircmatches&HcrashmemLog&HdiskEnd)".
  iDestruct "HdiskEnd" as (diskEnd) "[#HdiskEnd_txn Hcirc_diskEnd]".
  iMod (group_txn_valid with "Htxns HdiskEnd_txn") as "(%HdiskEnd_txn_valid&Htxns)"; first by solve_ndisj.
  apply is_txn_bound in HdiskEnd_txn_valid.
  iMod ("Hfupd" $! σ (set log_state.durable_lb (λ _, diskEnd_txn_id) σ)
          with "[% //] [%] [$HP]") as "[HP HQ]".
  { simpl.
    econstructor; monad_simpl.
    econstructor; monad_simpl; lia. }
  iSpecialize ("HΦ" with "HQ").
  iFrame "HΦ".
  iIntros "!> !>".
  iExists _; iFrame "HP".
  iSplit.
  - iPureIntro.
    eapply wal_wf_update_durable; eauto.
    { simpl; monad_simpl.
      econstructor; monad_simpl.
      econstructor; monad_simpl; lia. }
  - simpl.
    iFrame.
    iExists diskEnd_txn_id.
    iSplit; first by (iPureIntro; lia).
    iExists _, _, _, _; iFrame.
    iSplit; auto.
Qed.

(* TODO: move this out to some core control flow library *)
(** A proof principle for if e { do_stuff(); } where do_stuff() is optional and
does something irrelevant to the proof using resources R. Allows to re-use the
proof for both branches, carrying on with resources R. *)
Theorem wp_If_optional stk E (R: iProp Σ) (b: bool) e :
  (∀ (Φ': val -> iProp Σ), R -∗ ▷ (R -∗ Φ' #()) -∗ WP e @ stk; E {{ Φ' }}) -∗
  ∀ Φ, R -∗ ▷ (R -∗ Φ #()) -∗ WP If #b e #() @ stk; E {{ Φ }}.
Proof.
  iIntros "Hwp" (Φ) "HR HΦ".
  wp_if_destruct.
  - wp_apply ("Hwp" with "[$HR]").
    iFrame.
  - iApply ("HΦ" with "HR").
Qed.

Theorem simulate_flush l γ Q pos txn_id :
  is_wal l γ -∗
  diskEnd_at_least γ.(circ_name) (int.val pos) -∗
  (* TODO: the actual fact we want is not just for grouped txns but any valid
  one; furthermore, there's a complication that we really need the highest
  transaction id for this position since we'll only flush that *)
  group_txn γ txn_id pos -∗
  (∀ (σ σ' : log_state.t) (b : ()),
      ⌜wal_wf σ⌝
        -∗ ⌜relation.denote (log_flush pos) σ σ' b⌝ -∗ P σ ={⊤ ∖ ↑N}=∗ P σ' ∗ Q) -∗
  |={⊤}=> ▷ Q.
Proof.
  iIntros "#Hwal #Hlb #Hpos_txn Hfupd".
  iDestruct "Hwal" as "[Hwal _]".
  iInv "Hwal" as "Hinv" "Hclose".
  iAssert (∃ σ, is_wal_inner l γ σ ∗ P σ)%I with "[Hinv]" as "Hinv".
  { admit. }
  iDestruct "Hinv" as (σ) "[Hinner HP]".
  iDestruct "Hinner" as "(%Hwf&Hmem&Howntxns&Hdurable&Hinstalled&Htxns)".
  iDestruct "Hdurable" as (diskEnd_txn_id Hdurable_bound) "Hloginv".
  iDestruct "Hloginv" as (memStart memStart_txn_id memLog cs)
                           "(HownmemStart&HownmemLog&Howncs&%Hcircmatches&HcrashmemLog&HdiskEnd)".
  iDestruct "HdiskEnd" as (diskEnd) "[#HdiskEnd_txn Hcirc_diskEnd]".
  iMod (group_txn_valid with "Htxns Hpos_txn") as (His_txn) "Htxns"; first by solve_ndisj.
  iMod (group_txn_valid with "Htxns HdiskEnd_txn") as (HdiskEnd_is_txn) "Htxns"; first by solve_ndisj.
  pose proof (is_txn_bound _ _ _ His_txn).
  pose proof (is_txn_bound _ _ _ HdiskEnd_is_txn).
  iMod ("Hfupd" $! σ (set log_state.durable_lb (λ _, Nat.max σ.(log_state.durable_lb) txn_id) σ) with "[% //] [%] HP") as "[HP HQ]".
  { simpl; monad_simpl.
    repeat (econstructor; monad_simpl; eauto).
    { admit. }
    lia.
  }
  iFrame.
  iApply "Hclose".
  iNext.
  iExists _; iFrame "HP".
  iSplit; auto.
  { iPureIntro.
    eapply wal_wf_update_durable; eauto.
    simpl; monad_simpl.
    repeat (econstructor; monad_simpl; eauto); lia.
  }
  simpl.
  iFrame.
  iExists diskEnd_txn_id; iFrame.
  iSplit.
  { iPureIntro.
    admit. }
  iExists _, _, _, _; iFrame.
  iSplit; auto.
Admitted.

Theorem wp_Walog__Flush (Q: iProp Σ) l γ pos :
  {{{ is_wal l γ ∗
       (∀ σ σ' b,
         ⌜wal_wf σ⌝ -∗
         ⌜relation.denote (log_flush pos) σ σ' b⌝ -∗
         (P σ ={⊤ ∖ ↑N}=∗ P σ' ∗ Q))
   }}}
    Walog__Flush #l #pos
  {{{ RET #(); Q}}}.
Proof.
  iIntros (Φ) "[#Hwal Hfupd] HΦ".
  destruct_is_wal.

  wp_apply util_proof.wp_DPrintf.
  wp_loadField.
  wp_apply (acquire_spec with "Hlk"). iIntros "(Hlocked&Hlkinv)".
  wp_loadField.
  wp_apply (wp_condBroadcast with "HcondLogger").
  wp_loadField.
  iDestruct (wal_linv_load_nextDiskEnd with "Hlkinv")
    as (nextDiskEnd) "[HnextDiskEnd Hlkinv]".
  wp_loadField.
  iSpecialize ("Hlkinv" with "HnextDiskEnd").
  wp_pures.

  wp_apply (wp_If_optional with "[] [Hlkinv Hlocked]"); [ | iAccu | ].
  {
    iIntros (Φ') "(Hlkinv&Hlocked) HΦ".
    wp_loadField.
    wp_apply (wp_endGroupTxn with "[$Hlkinv]").
    iIntros "Hlkinv".
    wp_pures.
    iApply ("HΦ" with "[$]").
  }
  iIntros "(Hlkinv&Hlocked)".
  wp_pures.

  wp_bind (For _ _ _).
  wp_apply (wp_forBreak_cond (λ b,
               wal_linv σₛ.(wal_st) γ ∗ locked γ.(lock_name) ∗
               if b then ⊤ else diskEnd_at_least γ.(circ_name) (int.val pos))%I
           with "[] [$Hlkinv $Hlocked]").
  { iIntros "!>" (Φ') "(Hlkinv&Hlocked&_) HΦ".
    wp_loadField.
    iDestruct "Hlkinv" as (σ) "[Hfields Hrest]".
    iDestruct "Hfields" as (σₗ) "(Hfield_ptsto&His_memLogMap&His_memLog)".
    iDestruct "Hfield_ptsto" as "(HmemLog&HmemStart&HdiskEnd&HnextDiskEnd&HmemLogMap&Hshutdown&Hnthread)".
    wp_loadField.
    wp_pures.
    wp_if_destruct.
    - wp_loadField.
      wp_apply (wp_condWait with "[-HΦ $HcondLogger $Hlk $Hlocked]").
      { iExists _; iFrame.
        iExists _; iFrame. }
      iIntros "(Hlocked&Hlockin)".
      wp_pures.
      iApply "HΦ"; iFrame.
    - iApply "HΦ".
      iFrame "Hlocked".
      apply negb_false_iff in Heqb.
      apply bool_decide_eq_true in Heqb.
      iDestruct "Hrest" as "(#HdiskEnd_at_least&Hrest)".
      iSplitL.
      { iExists _; iFrame "HdiskEnd_at_least ∗".
        iExists _; iFrame. }
      iApply (diskEnd_at_least_mono with "HdiskEnd_at_least"); auto.
  }

  iIntros "(Hlkinv&Hlocked&#HdiskEnd_lb)".
  iDestruct "Hwal" as "[Hwal _]".

  iInv "Hwal" as "Hinv" "Hclose".
  wp_pures.
  wp_loadField.
  wp_call.
  iDestruct "Hinv" as (σ) "(Hinner&HP)".
  iDestruct "Hinner" as "(%Hwf&Hmem&Howntxns&Hdurable&Hinstalled&Htxns)".
  iDestruct "Hdurable" as (diskEnd_txn_id Hdurable_bound) "Hloginv".
  iDestruct "Hloginv" as (memStart memStart_txn_id memLog cs)
                           "(HownmemStart&HownmemLog&Howncs&%Hcircmatches&HcrashmemLog&HdiskEnd)".
  iDestruct "HdiskEnd" as (diskEnd) "[#HdiskEnd_txn Hcirc_diskEnd]".

  (* TODO: this is where we simulate *)
  (* FIXME: we need to know pos is a valid log position for a transaction for UB
  avoidance, probably best done with a persistent token about a position (a
  little like group_txn) that we take in the precondition. Then we know it gets
  flushed because every valid transaction at the time of locking gets
  flushed. *)
  wp_loadField.
  wp_apply (release_spec with "[$Hlk $Hlocked $Hlkinv]").
Abort.

Theorem wp_Walog__logAppend l γ σₛ :
  {{{ readonly (l ↦[Walog.S :: "memLock"] #σₛ.(memLock)) ∗
      readonly (l ↦[Walog.S :: "condLogger"] #σₛ.(condLogger)) ∗
      readonly (l ↦[Walog.S :: "condInstall"] #σₛ.(condInstall)) ∗
      is_cond σₛ.(condLogger) #σₛ.(memLock) ∗
      is_cond σₛ.(condInstall) #σₛ.(memLock) ∗
      readonly (l ↦[Walog.S :: "st"] #σₛ.(wal_st)) ∗
      wal_linv σₛ.(wal_st) γ ∗
      locked γ.(lock_name) ∗
      is_lock N γ.(lock_name) #σₛ.(memLock) (wal_linv σₛ.(wal_st) γ)
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
    iDestruct "Hlkinv" as (σ) "[Hfields Hrest]".
    iDestruct "Hfields" as (σₗ) "(Hfield_ptsto&His_memLogMap&His_memLog)".
    iDestruct "Hfield_ptsto" as "(HmemLog&HmemStart&HdiskEnd&HnextDiskEnd&HmemLogMap&Hshutdown&Hnthread)".
    wp_loadField.
    wp_apply wp_slice_len; wp_pures.
    change (int.val (word.divu (word.sub 4096 8) 8)) with LogSz.
    wp_if_destruct.
    - wp_loadField.
      wp_apply (wp_condWait with "[$His_cond2 $Hlocked $His_lock His_memLog His_memLogMap HmemLog HmemStart HdiskEnd HnextDiskEnd HmemLogMap Hshutdown Hnthread Hrest]").
      { iExists _; iFrame. iExists _; iFrame. }
      iIntros "(Hlocked&Hlkinv)".
      wp_pures.
      iApply ("HΦ" with "[$]").
    - iApply "HΦ"; iFrame.
      iExists _; iFrame. iExists _; iFrame.
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
