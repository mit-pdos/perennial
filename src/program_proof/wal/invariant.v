From Goose.github_com.mit_pdos.goose_nfsd Require Export wal.
From RecordUpdate Require Import RecordSet.
From iris.algebra Require Import gset.

From Perennial.Helpers Require Export Transitions List NamedProps PropRestore Map.

From Perennial.algebra Require Export deletable_heap append_list.
From Perennial.program_proof Require Export proof_prelude.
From Perennial.program_proof Require Export wal.lib wal.highest wal.thread_owned.
From Perennial.program_proof Require Export wal.circ_proof wal.sliding_proof.
From Perennial.program_proof Require Export wal.transitions.

Canonical Structure circO := leibnizO circΣ.t.

Transparent slice.T.
Typeclasses Opaque struct_field_mapsto.

Class walG Σ :=
  { wal_circ         :> circG Σ;
    wal_txns_map     :> gen_heapPreG nat (u64 * list update.t) Σ;
    wal_circ_state   :> inG Σ (ghostR $ circO);
    wal_txn_id       :> inG Σ (ghostR $ prodO u64O natO);
    wal_list_update  :> inG Σ (ghostR $ listO updateO);
    wal_txns         :> inG Σ (ghostR $ listO $ prodO u64O (listO updateO));
    wal_nat          :> inG Σ (ghostR $ natO);
    wal_addr_set     :> inG Σ (ghostR $ gmapO ZO unitO); (* TODO: probably unused *)
    wal_addr_set_gset :> inG Σ (ghostR $ gsetO Z);
    wal_thread_owned :> thread_ownG Σ;
    wal_txns_alist   :> alistG Σ (u64 * list update.t);
  }.

Section goose_lang.
Context `{!heapG Σ}.
Context `{!walG Σ}.

Implicit Types (v:val) (z:Z).

Context (P: log_state.t -> iProp Σ).
Definition walN := nroot .@ "wal".
Let N := walN.
Let innerN := walN .@ "wal".
Let circN := walN .@ "circ".

Record wal_names := mkWalNames
  { circ_name: circ_names;
    cs_name : gname;
    txns_ctx_name : gname;
    txns_name : gname;
    new_installed_name : gname;
    being_installed_name : gname;
    diskEnd_avail_name : gname;
    diskEnd_txn_id_name : gname;
    start_avail_name : gname;
  }.

Global Instance _eta_wal_names : Settable _ :=
  settable! mkWalNames <circ_name; cs_name; txns_ctx_name; txns_name;
                        new_installed_name; being_installed_name;
                        diskEnd_avail_name; diskEnd_txn_id_name; start_avail_name>.

Implicit Types (γ: wal_names).
Implicit Types (s: log_state.t) (memLog: slidingM.t) (txns: list (u64 * list update.t)).
Implicit Types (pos: u64) (installed_txn_id diskEnd_txn_id nextDiskEnd_txn_id txn_id: nat).

(** low-level, unimportant state *)
Record lowState :=
  { memLogPtr: loc;
    shutdown: bool;
    nthread: u64;
  }.

Global Instance lowState_eta: Settable _ :=
  settable! Build_lowState <memLogPtr; shutdown; nthread>.

Global Instance lowState_witness: Inhabited lowState := populate!.

Record locked_state :=
  { diskEnd: u64;
    locked_diskEnd_txn_id: nat;
    memLog: slidingM.t; }.

Global Instance locked_state_eta: Settable _ :=
  settable! Build_locked_state <diskEnd; locked_diskEnd_txn_id; memLog>.

Global Instance locked_state_witness: Inhabited locked_state := populate!.

Definition locked_wf (σ: locked_state) :=
  int.val σ.(memLog).(slidingM.start) ≤ int.val σ.(diskEnd) ≤ int.val σ.(memLog).(slidingM.mutable) ∧
  slidingM.wf σ.(memLog).

(*
txns: list (u64 * list update.t)
txn_id is referenced by pos, log < pos contains updates through and including upds
[txn_id: (pos, upds)]
*)

Definition txn_val γ txn_id (txn: u64 * list update.t): iProp Σ :=
  list_el γ.(txns_ctx_name) txn_id txn.

Definition txn_pos γ txn_id (pos: u64) : iProp Σ :=
  ∃ upds, txn_val γ txn_id (pos, upds).

Definition txns_ctx γ txns : iProp Σ := list_ctx γ.(txns_ctx_name) txns.

Theorem txn_val_to_pos γ txn_id pos upds :
  txn_val γ txn_id (pos, upds) -∗ txn_pos γ txn_id pos.
Proof.
  rewrite /txn_pos.
  iIntros "Hval".
  iExists _; iFrame.
Qed.

Global Instance txn_pos_persistent γ txn_id pos :
  Persistent (txn_pos γ txn_id pos) := _.

(** the simple role of the memLog is to contain all the transactions in the
abstract state starting at the memStart_txn_id *)
Definition is_mem_memLog memLog txns memStart_txn_id : Prop :=
  has_updates memLog.(slidingM.log) (drop memStart_txn_id txns) ∧
  (Forall (λ pos, int.val pos ≤ slidingM.memEnd memLog) txns.*1).

Definition memLog_linv_pers_core γ (σ: slidingM.t) (diskEnd: u64) diskEnd_txn_id (txns: list (u64 * list update.t)) : iProp Σ :=
  (∃ (memStart_txn_id: nat) (nextDiskEnd_txn_id: nat),
      "%Htxn_id_ordering" ∷ ⌜(memStart_txn_id ≤ diskEnd_txn_id ≤ nextDiskEnd_txn_id)%nat⌝ ∗
      "HmemStart_txn" ∷ txn_pos γ memStart_txn_id σ.(slidingM.start) ∗
      "%HdiskEnd_txn" ∷ ⌜is_highest_txn txns diskEnd_txn_id diskEnd⌝ ∗
      "HnextDiskEnd_txn" ∷ txn_pos γ nextDiskEnd_txn_id σ.(slidingM.mutable) ∗
      "HmemEnd_txn" ∷ txn_pos γ (length txns - 1)%nat (slidingM.endPos σ) ∗
      (* Here we establish what the memLog contains, which is necessary for reads
      to work (they read through memLogMap, but the lock invariant establishes
      that this matches memLog). *)
      "%His_memLog" ∷ ⌜is_mem_memLog σ txns memStart_txn_id⌝ ∗
      "%His_nextTxn" ∷
        ⌜has_updates
          (drop (slidingM.logIndex σ σ.(slidingM.mutable))
                σ.(slidingM.log))
          (drop nextDiskEnd_txn_id txns)⌝ ∗
      (* when nextDiskEnd gets set, we track that it has the right updates to
      use for [is_durable] when the new transaction is logged *)
      "%His_nextDiskEnd" ∷
        ⌜has_updates
          (subslice (slidingM.logIndex σ diskEnd)
                    (slidingM.logIndex σ σ.(slidingM.mutable))
                    σ.(slidingM.log))
          (subslice (S diskEnd_txn_id) (S nextDiskEnd_txn_id) txns)⌝
  ).

Global Instance memLog_linv_pers_core_persistent γ σ diskEnd diskEnd_txn_id txns:
  Persistent (memLog_linv_pers_core γ σ diskEnd diskEnd_txn_id txns).
Proof. apply _. Qed.

Definition memLog_linv γ (σ: slidingM.t) (diskEnd: u64) diskEnd_txn_id : iProp Σ :=
  (∃ (memStart_txn_id: nat) (nextDiskEnd_txn_id: nat) (txns: list (u64 * list update.t)),
      "%Htxn_id_ordering" ∷ ⌜(memStart_txn_id ≤ diskEnd_txn_id ≤ nextDiskEnd_txn_id)%nat⌝ ∗
      "HmemStart_txn" ∷ txn_pos γ memStart_txn_id σ.(slidingM.start) ∗
      "%HdiskEnd_txn" ∷ ⌜is_highest_txn txns diskEnd_txn_id diskEnd⌝ ∗
      "HnextDiskEnd_txn" ∷ txn_pos γ nextDiskEnd_txn_id σ.(slidingM.mutable) ∗
      "HmemEnd_txn" ∷ txn_pos γ (length txns - 1)%nat (slidingM.endPos σ) ∗
      "Howntxns" ∷ own γ.(txns_name) (◯E txns) ∗
      (* Here we establish what the memLog contains, which is necessary for reads
      to work (they read through memLogMap, but the lock invariant establishes
      that this matches memLog). *)
      "%His_memLog" ∷ ⌜is_mem_memLog σ txns memStart_txn_id⌝ ∗
      "%His_nextTxn" ∷
        ⌜has_updates
          (drop (slidingM.logIndex σ σ.(slidingM.mutable))
                σ.(slidingM.log))
          (drop nextDiskEnd_txn_id txns)⌝ ∗
      (* when nextDiskEnd gets set, we track that it has the right updates to
      use for [is_durable] when the new transaction is logged *)
      "%His_nextDiskEnd" ∷
        ⌜has_updates
          (subslice (slidingM.logIndex σ diskEnd)
                    (slidingM.logIndex σ σ.(slidingM.mutable))
                    σ.(slidingM.log))
          (subslice (S diskEnd_txn_id) (S nextDiskEnd_txn_id) txns)⌝
  ).

Definition wal_linv_fields st σ: iProp Σ :=
  (∃ σₗ,
      "Hfield_ptsto" ∷
         ("HmemLog" ∷ st ↦[WalogState.S :: "memLog"] #σₗ.(memLogPtr) ∗
          "HdiskEnd" ∷ st ↦[WalogState.S :: "diskEnd"] #σ.(diskEnd) ∗
          "Hshutdown" ∷ st ↦[WalogState.S :: "shutdown"] #σₗ.(shutdown) ∗
          "Hnthread" ∷ st ↦[WalogState.S :: "nthread"] #σₗ.(nthread)) ∗
  "%Hlocked_wf" ∷ ⌜locked_wf σ⌝ ∗
  "His_memLog" ∷ is_sliding σₗ.(memLogPtr) σ.(memLog)
  )%I.

Definition diskEnd_linv γ (diskEnd: u64) diskEnd_txn_id: iProp Σ :=
  "#HdiskEnd_at_least" ∷ diskEnd_at_least γ.(circ_name) (int.val diskEnd) ∗
  "HdiskEnd_exactly" ∷ thread_own_ctx γ.(diskEnd_avail_name)
                         ("HdiskEnd_is" ∷ diskEnd_is γ.(circ_name) (1/2) (int.val diskEnd) ∗
                          "γdiskEnd_txn_id1" ∷ own γ.(diskEnd_txn_id_name) (●{1/2} Excl' diskEnd_txn_id)).

Definition diskStart_linv γ (start: u64): iProp Σ :=
  "#Hstart_at_least" ∷ start_at_least γ.(circ_name) start ∗
  "Hstart_exactly" ∷ thread_own_ctx γ.(start_avail_name)
                       (start_is γ.(circ_name) (1/2) start).

(** the lock invariant protecting the WalogState, corresponding to l.memLock *)
Definition wal_linv (st: loc) γ : iProp Σ :=
  ∃ σ,
    "Hfields" ∷ wal_linv_fields st σ ∗
    "HdiskEnd_circ" ∷ diskEnd_linv γ σ.(diskEnd) σ.(locked_diskEnd_txn_id) ∗
    "Hstart_circ" ∷ diskStart_linv γ σ.(memLog).(slidingM.start) ∗
    "HmemLog_linv" ∷ memLog_linv γ σ.(memLog) σ.(diskEnd) σ.(locked_diskEnd_txn_id).

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
    "lk" ∷ is_lock N #σₛ.(memLock) (wal_linv σₛ.(wal_st) γ).

Global Instance is_wal_mem_persistent : Persistent (is_wal_mem l γ) := _.

(* this part of the invariant holds the installed disk blocks from the data
region of the disk and relates them to the logical installed disk, computed via
the updates through some installed transaction. *)
Definition is_installed γ d txns (installed_txn_id: nat) (diskEnd_txn_id: nat) : iProp Σ :=
  ∃ (new_installed_txn_id: nat) (being_installed: gset Z),
    (* TODO: the other half of these are owned by the installer, giving it full
     knowledge of in-progress installations and exclusive update rights; need to
     write down what it maintains as part of its loop invariant *)
    "Howninstalled" ∷ (own γ.(new_installed_name) (●E new_installed_txn_id) ∗
     own γ.(being_installed_name) (●E being_installed)) ∗
    "%Hinstalled_bounds" ∷ ⌜(installed_txn_id ≤ new_installed_txn_id ≤ diskEnd_txn_id ∧ diskEnd_txn_id < length txns)%nat⌝ ∗
    "Hdata" ∷ ([∗ map] a ↦ _ ∈ d,
     ∃ (b: Block),
       (* every disk block has at least through installed_txn_id (most have
        exactly, but some blocks may be in the process of being installed) *)
       ⌜let txn_id' := (if decide (a ∈ being_installed)
                        then new_installed_txn_id
                        else installed_txn_id) in
        let txns := take (S txn_id') txns in
        apply_upds (txn_upds txns) d !! a = Some b⌝ ∗
       a d↦ b ∗ ⌜2 + LogSz ≤ a⌝).

Global Instance is_installed_Timeless γ d txns installed_txn_id diskEnd_txn_id :
  Timeless (is_installed γ d txns installed_txn_id diskEnd_txn_id) := _.

(* weakening of [is_installed] for the sake of reading *)
Definition is_installed_read γ d txns installed_lb diskEnd_txn_id : iProp Σ :=
  ([∗ map] a ↦ _ ∈ d,
    ∃ (b: Block),
      ⌜∃ txn_id', (installed_lb ≤ txn_id' ≤ diskEnd_txn_id ∧ diskEnd_txn_id < length txns)%nat ∧
      apply_upds (txn_upds (take (S txn_id') txns)) d !! a = Some b⌝ ∗
      a d↦ b ∗ ⌜2 + LogSz ≤ a⌝)%I.

Definition circular_pred γ (cs : circΣ.t) : iProp Σ :=
  own γ.(cs_name) (●E cs).

Definition circ_matches_txns (cs:circΣ.t) txns installed_txn_id diskEnd_txn_id :=
  has_updates cs.(circΣ.upds) (subslice installed_txn_id (S diskEnd_txn_id) txns) ∧
  (installed_txn_id ≤ diskEnd_txn_id)%nat.

(** an invariant governing the data logged for crash recovery of (a prefix of)
memLog. *)
Definition is_durable γ cs txns installed_txn_id diskEnd_txn_id : iProp Σ :=
    "%Hcirc_matches" ∷ ⌜circ_matches_txns cs txns installed_txn_id diskEnd_txn_id⌝.

Definition is_installed_txn γ cs txns installed_txn_id installed_lb: iProp Σ :=
    "%Hinstalled_bound" ∷ ⌜(installed_lb ≤ installed_txn_id)%nat⌝ ∗
    "%Hstart_txn" ∷ ⌜is_highest_txn txns installed_txn_id (circΣ.start cs)⌝.

Definition is_durable_txn γ cs txns diskEnd_txn_id durable_lb: iProp Σ :=
  ∃ (diskEnd: u64),
    "%Hdurable_lb" ∷ ⌜(durable_lb ≤ diskEnd_txn_id)%nat⌝ ∗
    "%HdiskEnd_val" ∷ ⌜int.val diskEnd = circΣ.diskEnd cs⌝ ∗
    "%Hend_txn" ∷ ⌜is_txn txns diskEnd_txn_id diskEnd⌝.

Definition disk_inv γ s (cs: circΣ.t) : iProp Σ :=
 ∃ installed_txn_id diskEnd_txn_id,
      "γdiskEnd_txn_id2" ∷ own γ.(diskEnd_txn_id_name) (●{1/2} Excl' diskEnd_txn_id) ∗
      "Hinstalled" ∷ is_installed γ s.(log_state.d) s.(log_state.txns) installed_txn_id diskEnd_txn_id ∗
      "Hdurable"   ∷ is_durable γ cs s.(log_state.txns) installed_txn_id diskEnd_txn_id ∗
      "#circ.start" ∷ is_installed_txn γ cs s.(log_state.txns) installed_txn_id s.(log_state.installed_lb) ∗
      "#circ.end"   ∷ is_durable_txn γ cs s.(log_state.txns) diskEnd_txn_id s.(log_state.durable_lb).

Definition disk_inv_durable γ s (cs: circΣ.t) : iProp Σ :=
 ∃ installed_txn_id diskEnd_txn_id,
      (* TODO: what to do with diskEnd_txn_id_name ghost variable? *)
      "Hinstalled" ∷ is_installed_read γ s.(log_state.d) s.(log_state.txns) s.(log_state.installed_lb) diskEnd_txn_id ∗
      "#Hdurable"   ∷ is_durable γ cs s.(log_state.txns) installed_txn_id diskEnd_txn_id ∗
      "#circ.start" ∷ is_installed_txn γ cs s.(log_state.txns) installed_txn_id s.(log_state.installed_lb) ∗
      "#circ.end"   ∷ is_durable_txn γ cs s.(log_state.txns) diskEnd_txn_id s.(log_state.durable_lb).

(** the complete wal invariant *)
Definition is_wal_inner (l : loc) γ s : iProp Σ :=
    "%Hwf" ∷ ⌜wal_wf s⌝ ∗
    "Hmem" ∷ is_wal_mem l γ ∗
    "Htxns_ctx" ∷ txns_ctx γ s.(log_state.txns) ∗
    "γtxns"  ∷ own γ.(txns_name) (●E s.(log_state.txns)) ∗
    "Hdisk" ∷ ∃ cs, "Howncs" ∷ own γ.(cs_name) (◯E cs) ∗ "Hdisk" ∷ disk_inv γ s cs
.

(* holds for log states which are possible after a crash (essentially these have
no mutable state) *)
Definition wal_post_crash σ: Prop :=
  S (σ.(log_state.durable_lb)) = length σ.(log_state.txns).

Definition is_wal_inner_durable γ s : iProp Σ :=
    "%Hwf" ∷ ⌜wal_wf s⌝ ∗
    "%Hpostcrash" ∷ ⌜wal_post_crash s⌝ ∗
    "Hdisk" ∷ ∃ cs, "Hdiskinv" ∷ disk_inv_durable γ s cs ∗
                    "Hcirc" ∷ is_circular_state γ.(circ_name) cs
.

(* This is produced by recovery as a post condition, can be used to get is_wal *)
Definition is_wal_inv_pre (l: loc) γ s : iProp Σ :=
  is_wal_inner l γ s ∗ (∃ cs, is_circular_state γ.(circ_name) cs ∗ circular_pred γ cs).

Definition is_wal (l : loc) γ : iProp Σ :=
  inv innerN (∃ σ, is_wal_inner l γ σ ∗ P σ) ∗
  is_circular circN (circular_pred γ) γ.(circ_name).

(** logger_inv is the resources exclusively owned by the logger thread *)
Definition logger_inv γ circ_l: iProp Σ :=
  "HnotLogging" ∷ thread_own γ.(diskEnd_avail_name) Available ∗
  "*" ∷ (∃ diskEnd_txn_id, "Hown_diskEnd_txn_id" ∷ own γ.(diskEnd_txn_id_name) (◯E diskEnd_txn_id)) ∗
  "Happender" ∷ is_circular_appender γ.(circ_name) circ_l.

(* TODO: also needs authoritative ownership of some other variables *)
Definition installer_inv γ: iProp Σ :=
  "HnotInstalling" ∷ thread_own γ.(start_avail_name) Available.

Global Instance is_installed_read_Timeless {γ d txns installed_lb diskEnd_txn_id} :
  Timeless (is_installed_read γ d txns installed_lb diskEnd_txn_id) := _.

(* this illustrates what reads rely on and is used by the crash proof, since
after a crash we only rely on this property to restore the stronger
invariant. *)
Theorem is_installed_weaken_read γ d txns installed_lb diskEnd_txn_id :
  is_installed γ d txns installed_lb diskEnd_txn_id -∗
  is_installed_read γ d txns installed_lb diskEnd_txn_id.
Proof.
  rewrite /is_installed /is_installed_read.
  iIntros "I".
  iNamed "I".
  iApply (big_sepM_mono with "Hdata").
  iIntros (a b0 Hlookup) "HI".
  iDestruct "HI" as (b') "(%&Hb&%)".
  iExists b'; iFrame.
  iPureIntro.
  split; auto.
  destruct (decide _); [ exists new_installed_txn_id | exists installed_lb ];
    split_and!; auto; try lia.
Qed.

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

Theorem is_wal_open l wn E :
  ↑innerN ⊆ E ->
  is_wal l wn
  ={E, E ∖ ↑innerN}=∗
    ∃ σ, ▷ P σ ∗
    ( ▷ P σ ={E ∖ ↑innerN, E}=∗ emp ).
Proof.
  iIntros (HN) "[#? _]".
  iInv innerN as (σ) "[Hwalinner HP]" "Hclose".
  iModIntro.
  iExists _. iFrame.
  iIntros "HP".
  iApply "Hclose". iNext.
  iExists _. iFrame.
Qed.

Theorem is_circular_diskEnd_lb_agree E γ lb cs :
  ↑circN ⊆ E ->
  diskEnd_at_least γ.(circ_name) lb -∗
  is_circular circN (circular_pred γ) γ.(circ_name) -∗
  own γ.(cs_name) (◯E cs) -∗
  |={E}=> ⌜lb ≤ circΣ.diskEnd cs⌝ ∗ own γ.(cs_name) (◯E cs).
Proof.
  rewrite /circular_pred.
  iIntros (Hsub) "#HdiskEnd_lb #Hcirc Hown".
  iInv "Hcirc" as ">Hinner" "Hclose".
  iDestruct "Hinner" as (σ) "(Hstate&Hγ)".
  unify_ghost.
  iFrame "Hown".
  iDestruct (is_circular_state_pos_acc with "Hstate") as "([HdiskStart HdiskEnd]&Hstate)".
  iDestruct (diskEnd_is_agree_2 with "HdiskEnd HdiskEnd_lb") as %Hlb.
  iFrame (Hlb).
  iSpecialize ("Hstate" with "[$HdiskStart $HdiskEnd]").
  iApply "Hclose".
  iNext.
  iExists _; iFrame.
Qed.

Theorem is_circular_diskEnd_is_agree E q γ diskEnd cs :
  ↑circN ⊆ E ->
  diskEnd_is γ.(circ_name) q diskEnd -∗
  is_circular circN (circular_pred γ) γ.(circ_name) -∗
  own γ.(cs_name) (◯E cs) -∗
  |={E}=> ⌜diskEnd = circΣ.diskEnd cs⌝ ∗
          diskEnd_is γ.(circ_name) q diskEnd ∗
          own γ.(cs_name) (◯E cs).
Proof.
  rewrite /circular_pred.
  iIntros (Hsub) "HdiskEnd_is #Hcirc Hown".
  iInv "Hcirc" as ">Hinner" "Hclose".
  iDestruct "Hinner" as (σ) "(Hstate&Hγ)".
  unify_ghost.
  iFrame "Hown".
  iDestruct (is_circular_state_pos_acc with "Hstate") as "([HdiskStart HdiskEnd]&Hstate)".
  iDestruct (diskEnd_is_agree with "HdiskEnd HdiskEnd_is") as %Heq; subst; iFrame.
  iSpecialize ("Hstate" with "[$HdiskStart $HdiskEnd]").
  iMod ("Hclose" with "[-]") as "_"; auto.
  iNext.
  iExists _; iFrame.
Qed.

(** * some facts about txn_ctx *)
Theorem txn_map_to_is_txn txns (txn_id: nat) (pos: u64) upds :
  list_to_imap txns !! txn_id = Some (pos, upds) ->
  is_txn txns txn_id pos.
Proof.
  rewrite /is_txn.
  rewrite lookup_list_to_imap.
  by intros ->.
Qed.

Global Instance circ_names_inhabited : Inhabited circ_names := populate!.

Definition wal_names_dummy {hG:gen_heapPreG nat (u64 * list update.t) Σ} : wal_names.
  constructor; try exact inhabitant.
Defined.

Theorem alloc_txns_ctx E txns :
  ↑nroot.@"readonly" ⊆ E →
  ⊢ |={E}=> ∃ γtxns, txns_ctx (set txns_ctx_name (λ _, γtxns) wal_names_dummy) txns.
Proof.
  iIntros (Hsub).
  iMod (alist_alloc txns) as (γtxns) "Hctx".
  iExists γtxns.
  rewrite /txns_ctx //=.
Qed.

Theorem alloc_txn_pos pos upds γ txns E :
  txns_ctx γ txns ={E}=∗
  txns_ctx γ (txns ++ [(pos, upds)]) ∗ txn_val γ (length txns) (pos, upds).
Proof.
  iIntros "Hctx".
  iMod (alist_app1 (pos,upds) with "Hctx") as "[Hctx Hval]".
  by iFrame.
Qed.

Theorem txns_ctx_complete γ txns txn_id txn :
  txns !! txn_id = Some txn ->
  txns_ctx γ txns -∗ txn_val γ txn_id txn.
Proof.
  iIntros (Hlookup) "Hctx".
  iDestruct (alist_lookup_el with "Hctx") as "Hel"; eauto.
Qed.

Theorem txns_ctx_complete' γ txns txn_id txn :
  txns !! txn_id = Some txn ->
  ▷ txns_ctx γ txns -∗ ▷ txn_val γ txn_id txn ∗ ▷ txns_ctx γ txns.
Proof.
  iIntros (Hlookup) "Hctx".
  iDestruct (txns_ctx_complete with "Hctx") as "#Hel"; eauto.
Qed.

Theorem txns_ctx_txn_pos γ txns txn_id pos :
  is_txn txns txn_id pos ->
  txns_ctx γ txns -∗ txn_pos γ txn_id pos.
Proof.
  intros [txn [Hlookup ->]]%fmap_Some_1.
  rewrite txns_ctx_complete; eauto.
  iIntros "Htxn_val".
  destruct txn as [pos upds].
  iExists _; iFrame.
Qed.

Theorem txn_val_valid_general γ txns txn_id txn :
  txns_ctx γ txns -∗
  txn_val γ txn_id txn -∗
  ⌜txns !! txn_id = Some txn⌝.
Proof.
  iIntros "Hctx Htxn".
  iDestruct (alist_lookup with "Hctx Htxn") as %Hlookup.
  eauto.
Qed.

Theorem txn_pos_valid_general γ txns txn_id pos :
  txns_ctx γ txns -∗
  txn_pos γ txn_id pos -∗
  ⌜is_txn txns txn_id pos⌝.
Proof.
  iIntros "Hctx Htxn".
  iDestruct "Htxn" as (upds) "Hval".
  iDestruct (alist_lookup with "Hctx Hval") as %Hlookup.
  iPureIntro.
  rewrite /is_txn Hlookup //.
Qed.

Theorem is_wal_txns_lookup l γ σ :
  is_wal_inner l γ σ -∗
  (∃ txns, txns_ctx γ txns ∗ own γ.(txns_name) (●E txns) ∗
             (txns_ctx γ txns ∗ own γ.(txns_name) (●E txns) -∗
              is_wal_inner l γ σ)).
Proof.
  iNamed 1.
  iExists _; iFrame.
  by iIntros "($ & $)".
Qed.

Theorem txn_pos_valid_locked l γ txns txn_id pos :
  is_wal l γ -∗
  txn_pos γ txn_id pos -∗
  own γ.(txns_name) (◯E txns) -∗
  |={⊤}=> ⌜is_txn txns txn_id pos⌝ ∗ own γ.(txns_name) (◯E txns).
Proof.
  iIntros "[#? _] #Hpos Howntxns".
  iInv innerN as (σ) "[Hinner HP]".
  iDestruct (is_wal_txns_lookup with "Hinner") as (txns') "(>Htxns_ctx & >γtxns & Hinner)".
  iDestruct (ghost_var_agree with "γtxns Howntxns") as %Hagree; subst.
  iFrame "Howntxns".
  iDestruct (txn_pos_valid_general with "Htxns_ctx Hpos") as %His_txn.
  iModIntro.
  iSplitL.
  { iNext.
    iExists _; iFrame.
    iApply ("Hinner" with "[$]"). }
  auto.
Qed.

Definition txns_are γ (start: nat) (txns_sub: list (u64*list update.t)) : iProp Σ :=
  list_subseq γ.(txns_ctx_name) start txns_sub.

Global Instance txns_are_Persistent γ start txns_sub : Persistent (txns_are γ start txns_sub).
Proof. apply _. Qed.

Theorem txns_are_sound γ txns start txns_sub :
  txns_ctx γ txns -∗
  txns_are γ start txns_sub -∗
  ⌜subslice start (start + length txns_sub)%nat txns = txns_sub⌝.
Proof.
  iIntros "Hctx Htxns_are".
  iDestruct (alist_subseq_lookup with "Hctx Htxns_are") as "$".
Qed.

Theorem get_txns_are l γ txns start till txns_sub :
  txns_sub = subslice start till txns →
  (start ≤ till ≤ length txns)%nat →
  own γ.(txns_name) (◯E txns) -∗
  is_wal l γ -∗
  |={⊤}=> txns_are γ start txns_sub ∗ own γ.(txns_name) (◯E txns).
Proof.
  iIntros (??) "Hown #Hwal".
  iDestruct "Hwal" as "[Hwal _]".
  iInv "Hwal" as (σ) "[Hinner HP]".
  iDestruct (is_wal_txns_lookup with "Hinner") as (txns') "(>Htxns_ctx & >γtxns & Hinner)".
  iDestruct (ghost_var_agree with "γtxns Hown") as %Heq; subst.
  iDestruct (alist_lookup_subseq _ start till with "Htxns_ctx") as "#$".
  { lia. }
  iModIntro.
  iSplitR "Hown"; [ | by iFrame ].
  iNext.
  iExists _; iFrame "HP".
  iApply "Hinner"; iFrame.
Qed.

(** * accessors for fields whose values don't matter for correctness *)
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
  by iFrame "# ∗".
Qed.

(* TODO: need a replacement in terms of memLog *)
Theorem wal_linv_load_nextDiskEnd st γ :
  wal_linv st γ -∗
    ∃ (x:u64),
      st ↦[WalogState.S :: "nextDiskEnd"]{1/2} #x ∗
         (st ↦[WalogState.S :: "nextDiskEnd"]{1/2} #x -∗ wal_linv st γ).
Proof.
Abort.

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
  rewrite -list_lookup_fmap in H.
  rewrite -list_lookup_fmap in H0.
  eapply (Hmono _ _) in Hord; eauto.
  word. (* contradiction from [pos1 = pos2] *)
Qed.

Lemma wal_wf_txns_mono_highest {σ txn_id1 pos1 txn_id2 pos2} :
  wal_wf σ ->
  is_txn σ.(log_state.txns) txn_id1 pos1 ->
  is_highest_txn σ.(log_state.txns) txn_id2 pos2 ->
  int.val pos1 ≤ int.val pos2 ->
  (txn_id1 ≤ txn_id2)%nat.
Proof.
  intros Hwf Htxn1 Htxn2 Hle.
  destruct (decide (pos1 = pos2)); subst.
  - apply Htxn2 in Htxn1; lia.
  - eapply wal_wf_txns_mono_pos; eauto.
    + eapply Htxn2.
    + assert (int.val pos1 ≠ int.val pos2).
      { intro H.
        assert (pos1 = pos2) by word; congruence. }
      lia.
Qed.

Lemma memLog_linv_pers_core_strengthen γ σ diskEnd diskEnd_txn_id txns:
  (memLog_linv_pers_core γ σ diskEnd diskEnd_txn_id txns) -∗
  (own γ.(txns_name) (◯E txns)) -∗
  memLog_linv γ σ diskEnd diskEnd_txn_id.
Proof.
  iNamed 1. iIntros "H". iExists _, _, _. iFrame. iFrame "%".
Qed.

(** * WPs for field operations in terms of lock invariant *)

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

Lemma wp_load_shutdown l (st: loc) γ :
  {{{ readonly (l ↦[Walog.S :: "st"] #st) ∗ wal_linv st γ  }}}
    struct.loadF WalogState.S "shutdown" (struct.loadF Walog.S "st" #l)
  {{{ (b:bool), RET #b; wal_linv st γ }}}.
Proof.
  iIntros (Φ) "[#Hst Hlkinv] HΦ".
  shutdown_fields.
  iApply ("HΦ" with "[$]").
Qed.

End goose_lang.

Ltac destruct_is_wal :=
  iMod (is_wal_read_mem with "Hwal") as "#Hmem";
  wp_call;
  iNamed "Hmem"; iNamed "Hstfields".

Hint Unfold locked_wf : word.
