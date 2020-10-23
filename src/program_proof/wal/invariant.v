From Goose.github_com.mit_pdos.goose_nfsd Require Export wal.
From RecordUpdate Require Import RecordUpdate.
From iris.algebra Require Import gset.

From Perennial.Helpers Require Export Transitions List NamedProps PropRestore Map.

From Perennial.algebra Require Export deletable_heap append_list auth_map.
From Perennial.program_proof Require Export proof_prelude.
From Perennial.program_proof Require Export wal.lib wal.highest wal.thread_owned.
From Perennial.program_proof Require Export wal.circ_proof wal.sliding_proof.
From Perennial.program_proof Require Export wal.transitions.

Transparent slice.T.
Typeclasses Opaque struct_field_mapsto.

Class walG Σ :=
  { wal_circ         :> circG Σ;
    wal_txns_map     :> gen_heapPreG nat (u64 * list update.t) Σ;
    wal_circ_state   :> ghost_varG Σ circΣ.t;
    wal_txn_id       :> ghost_varG Σ (u64 * nat);
    wal_list_update  :> ghost_varG Σ (list update.t);
    wal_txns         :> ghost_varG Σ (list (u64 * (list update.t)));
    wal_nat          :> ghost_varG Σ nat;
    wal_addr_set     :> ghost_varG Σ (gset Z);
    wal_thread_owned :> thread_ownG Σ;
    wal_txns_alist   :> alistG Σ (u64 * list update.t);
    wal_stable_map   :> ghost_varG Σ (gmap nat unit);
    wal_stable_mapG  :> mapG Σ nat unit;
    wal_logger_pos   :> ghost_varG Σ u64;
    wal_base_disk    :> inG Σ (agreeR (leibnizO disk));
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
    installed_txn_name : gname;
    being_installed_name : gname;
    being_installed_txns_name : gname;
    diskEnd_avail_name : gname;
    start_avail_name : gname;
    stable_txn_ids_name : gname;
    logger_pos_name : gname;
    (* TODO: this is the logger's next transaction id? *)
    logger_txn_id_name : gname;
    base_disk_name : gname;
  }.

Global Instance _eta_wal_names : Settable _ :=
  settable! mkWalNames <circ_name; cs_name; txns_ctx_name; txns_name;
                        installed_txn_name; being_installed_name; being_installed_txns_name;
                        diskEnd_avail_name; start_avail_name;
                        stable_txn_ids_name; logger_pos_name; logger_txn_id_name;
                        base_disk_name>.

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

Definition txns_ctx γ txns : iProp Σ := list_ctx γ.(txns_ctx_name) 1 txns.

Theorem txn_val_to_pos γ txn_id pos upds :
  txn_val γ txn_id (pos, upds) -∗ txn_pos γ txn_id pos.
Proof.
  rewrite /txn_pos.
  iIntros "Hval".
  iExists _; iFrame.
Qed.

Global Instance txn_pos_timeless γ txn_id pos :
  Timeless (txn_pos γ txn_id pos) := _.

Global Instance txn_pos_persistent γ txn_id pos :
  Persistent (txn_pos γ txn_id pos) := _.

Definition memLog_linv_txns (σ: slidingM.t) (diskEnd logger_pos: u64) txns memStart_txn_id diskEnd_txn_id logger_txn_id nextDiskEnd_txn_id : iProp Σ :=
  "%His_memStart" ∷
    ⌜has_updates
      (take (slidingM.logIndex σ diskEnd)
            σ.(slidingM.log))
      (subslice (S memStart_txn_id) (S diskEnd_txn_id) txns)⌝ ∗
  "%His_loggerEnd" ∷
    ⌜has_updates
      (subslice (slidingM.logIndex σ diskEnd)
                (slidingM.logIndex σ logger_pos)
                σ.(slidingM.log))
      (subslice (S diskEnd_txn_id) (S logger_txn_id) txns)⌝ ∗
  "%His_nextDiskEnd" ∷
    ⌜has_updates
      (subslice (slidingM.logIndex σ logger_pos)
                (slidingM.logIndex σ σ.(slidingM.mutable))
                σ.(slidingM.log))
      (subslice (S logger_txn_id) (S nextDiskEnd_txn_id) txns)⌝ ∗
  "%His_nextTxn" ∷
    ⌜has_updates
      (drop (slidingM.logIndex σ σ.(slidingM.mutable))
            σ.(slidingM.log))
      (drop (S nextDiskEnd_txn_id) txns)⌝.

(** the simple role of the memLog is to contain all the transactions in the
abstract state starting at the memStart_txn_id *)
Definition is_mem_memLog memLog txns memStart_txn_id : Prop :=
  has_updates memLog.(slidingM.log) (drop (S memStart_txn_id) txns) ∧
  (Forall (λ pos, int.val pos ≤ slidingM.memEnd memLog) txns.*1).

Definition memLog_linv_pers_core γ (σ: slidingM.t) (diskEnd: u64) diskEnd_txn_id nextDiskEnd_txn_id (txns: list (u64 * list update.t)) (logger_pos : u64) (logger_txn_id : nat) : iProp Σ :=
  (∃ (memStart_txn_id: nat),
      "%Htxn_id_ordering" ∷ ⌜(memStart_txn_id ≤ diskEnd_txn_id ≤ logger_txn_id ≤ nextDiskEnd_txn_id)%nat⌝ ∗
      "#HmemStart_txn" ∷ txn_pos γ memStart_txn_id σ.(slidingM.start) ∗
      "%HdiskEnd_txn" ∷ ⌜is_txn txns diskEnd_txn_id diskEnd⌝ ∗
      "#HdiskEnd_stable" ∷ diskEnd_txn_id [[γ.(stable_txn_ids_name)]]↦ro tt ∗
      "#HnextDiskEnd_txn" ∷ txn_pos γ nextDiskEnd_txn_id σ.(slidingM.mutable) ∗
      "#HmemEnd_txn" ∷ txn_pos γ (length txns - 1)%nat (slidingM.endPos σ) ∗
      "%HloggerPosOK" ∷ ⌜int.val diskEnd ≤ int.val logger_pos ≤ int.val σ.(slidingM.mutable)⌝ ∗
      (* Here we establish what the memLog contains, which is necessary for reads
      to work (they read through memLogMap, but the lock invariant establishes
      that this matches memLog). *)
      "#Htxns" ∷ memLog_linv_txns σ diskEnd logger_pos txns memStart_txn_id diskEnd_txn_id logger_txn_id nextDiskEnd_txn_id ∗
      "%Htxnpos_bound" ∷
        ⌜(Forall (λ pos, int.val pos ≤ slidingM.memEnd σ) txns.*1)⌝
  ).

Global Instance memLog_linv_pers_core_persistent γ σ diskEnd diskEnd_txn_id nextDiskEnd_txn_id txns logger_pos logger_txn_id :
  Persistent (memLog_linv_pers_core γ σ diskEnd diskEnd_txn_id nextDiskEnd_txn_id txns logger_pos logger_txn_id).
Proof. apply _. Qed.

Definition memLog_linv_nextDiskEnd_txn_id γ mutable nextDiskEnd_txn_id : iProp Σ :=
  ∃ (stable_txns: gmap nat unit),
      "HownStableSet" ∷ map_ctx γ.(stable_txn_ids_name) (1/2) stable_txns ∗
      "#HnextDiskEnd_stable" ∷ nextDiskEnd_txn_id [[γ.(stable_txn_ids_name)]]↦ro tt ∗
      "#HnextDiskEnd_txn" ∷ txn_pos γ nextDiskEnd_txn_id mutable ∗
      "%HnextDiskEnd_max_stable" ∷
        ⌜∀ txn_id, txn_id > nextDiskEnd_txn_id -> stable_txns !! txn_id = None⌝.

(* TODO: inline memLog_linv_pers_core *)
Definition memLog_linv γ (σ: slidingM.t) (diskEnd: u64) diskEnd_txn_id : iProp Σ :=
  (∃ (memStart_txn_id: nat) (nextDiskEnd_txn_id: nat)
     (txns: list (u64 * list update.t))
     (logger_pos: u64) (logger_txn_id : nat),
      "%Htxn_id_ordering" ∷ ⌜(memStart_txn_id ≤ diskEnd_txn_id ≤ logger_txn_id ≤ nextDiskEnd_txn_id)%nat⌝ ∗
      "#HmemStart_txn" ∷ txn_pos γ memStart_txn_id σ.(slidingM.start) ∗
      "%HdiskEnd_txn" ∷ ⌜is_txn txns diskEnd_txn_id diskEnd⌝ ∗
      "#HdiskEnd_stable" ∷ diskEnd_txn_id [[γ.(stable_txn_ids_name)]]↦ro tt ∗
      "#HmemEnd_txn" ∷ txn_pos γ (length txns - 1)%nat (slidingM.endPos σ) ∗
      "Howntxns" ∷ ghost_var γ.(txns_name) (1/2) txns ∗
      "HnextDiskEnd" ∷ memLog_linv_nextDiskEnd_txn_id γ σ.(slidingM.mutable) nextDiskEnd_txn_id ∗
      "HownLoggerPos_linv" ∷ ghost_var γ.(logger_pos_name) (1/2) logger_pos ∗
      "HownLoggerTxn_linv" ∷ ghost_var γ.(logger_txn_id_name) (1/2) logger_txn_id ∗
      "%HloggerPosOK" ∷ ⌜int.val diskEnd ≤ int.val logger_pos ≤ int.val σ.(slidingM.mutable)⌝ ∗
      (* Here we establish what the memLog contains, which is necessary for reads
      to work (they read through memLogMap, but the lock invariant establishes
      that this matches memLog). *)
      "#Htxns" ∷ memLog_linv_txns σ diskEnd logger_pos txns memStart_txn_id diskEnd_txn_id logger_txn_id nextDiskEnd_txn_id ∗
      "%Htxnpos_bound" ∷
        ⌜(Forall (λ pos, int.val pos ≤ slidingM.memEnd σ) txns.*1)⌝
  ).

(* this is what witnesses the basic role of the memLog, which is to contain all
the updates (expressed in memLog_linv_txns in a finer-grained way for all the
subsets, which are needed by the logger/installer but not for reads) *)
Lemma memLog_linv_txns_combined_updates memLog diskEnd logger_pos txns memStart_txn_id diskEnd_txn_id logger_txn_id nextDiskEnd_txn_id :
    ∀ (Htxn_id_ordering: (memStart_txn_id ≤ diskEnd_txn_id ≤ logger_txn_id ≤ nextDiskEnd_txn_id)%nat)
      (HloggerPosOK: int.val diskEnd ≤ int.val logger_pos ≤ int.val memLog.(slidingM.mutable)),
    memLog_linv_txns memLog diskEnd logger_pos txns memStart_txn_id diskEnd_txn_id logger_txn_id nextDiskEnd_txn_id -∗
    ⌜has_updates memLog.(slidingM.log) (drop (S memStart_txn_id) txns)⌝.
Proof.
  intros ??.
  iNamed 1.
  pose proof (has_updates_app _ _ _ _ His_memStart His_loggerEnd) as Hhas_updates_mid.
  rewrite -subslice_from_start subslice_app_contig in Hhas_updates_mid.
  2: rewrite /slidingM.logIndex; lia.
  rewrite subslice_from_start subslice_app_contig in Hhas_updates_mid.
  2: rewrite /slidingM.logIndex; lia.
  pose proof (has_updates_app _ _ _ _ Hhas_updates_mid His_nextDiskEnd) as Hhas_updates_mid'.
  rewrite -subslice_from_start subslice_app_contig in Hhas_updates_mid'.
  2: rewrite /slidingM.logIndex; lia.
  rewrite subslice_from_start subslice_app_contig in Hhas_updates_mid'.
  2: rewrite /slidingM.logIndex; lia.
  pose proof (has_updates_app _ _ _ _ Hhas_updates_mid' His_nextTxn) as Hhas_updates.
  rewrite take_drop /subslice drop_take_drop in Hhas_updates; try lia.
  auto.
Qed.

(* NOTE(tej): this is only proven because it was there before; it's just like
the above but integrates Htxnpos_bound into the result *)
Lemma memLog_linv_txns_to_is_mem_memLog memLog diskEnd logger_pos txns memStart_txn_id diskEnd_txn_id logger_txn_id nextDiskEnd_txn_id :
    ∀ (Htxn_id_ordering: (memStart_txn_id ≤ diskEnd_txn_id ≤ logger_txn_id ≤ nextDiskEnd_txn_id)%nat)
      (HloggerPosOK: int.val diskEnd ≤ int.val logger_pos ≤ int.val memLog.(slidingM.mutable))
      (Htxnpos_bound: Forall (λ pos, int.val pos ≤ slidingM.memEnd memLog) txns.*1),
    memLog_linv_txns memLog diskEnd logger_pos txns memStart_txn_id diskEnd_txn_id logger_txn_id nextDiskEnd_txn_id -∗
    ⌜is_mem_memLog memLog txns memStart_txn_id⌝.
Proof.
  iIntros (???) "Htxns".
  iDestruct (memLog_linv_txns_combined_updates with "Htxns") as %Hupds; auto.
Qed.

(* NOTE(tej): almost certainly useless, since txns is existential *)
Theorem memLog_linv_implies_is_mem_memLog γ memLog diskEnd diskEnd_txn_id :
  memLog_linv γ memLog diskEnd diskEnd_txn_id -∗
  ⌜∃ (memStart_txn_id: nat) (txns: list (u64 * list update.t)),
    is_mem_memLog memLog txns memStart_txn_id⌝.
Proof.
  iIntros "HmemLog".
  iNamed "HmemLog".
  iDestruct (memLog_linv_txns_to_is_mem_memLog with "Htxns") as %HmemLog; auto.
  eauto.
Qed.

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
                         ("HdiskEnd_is" ∷ diskEnd_is γ.(circ_name) (1/2) (int.val diskEnd)).

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
    (* TODO(tej): the other half of these are owned by the installer, giving it full
     knowledge of in-progress installations and exclusive update rights; need to
     write down what it maintains as part of its loop invariant *)
    "Howninstalled" ∷ (
      "Hinstalled_txn" ∷ ghost_var γ.(installed_txn_name) (1/2) installed_txn_id ∗
      "Hbeing_installed" ∷ ghost_var γ.(being_installed_name) (1/2) being_installed ∗
      (* TODO(tej): this should probably be replaced with a persistent [txns_are]
      fact rather than a new ghost variable *)
      "Hbeing_installed_txns" ∷ ghost_var γ.(being_installed_txns_name) (1/2)
        (subslice (S installed_txn_id) (S new_installed_txn_id) txns)) ∗
    "%Hinstalled_bounds" ∷ ⌜(installed_txn_id ≤ new_installed_txn_id ≤ diskEnd_txn_id ∧ diskEnd_txn_id < length txns)%nat⌝ ∗
    "Hdata" ∷ ([∗ map] a ↦ _ ∈ d,
     ∃ (b: Block) (txn_id': nat),
       (* every disk block has at least through installed_txn_id (most have
        exactly, but some blocks may be in the process of being installed) *)
       ⌜(if decide (a ∈ being_installed)
        then txn_id' = new_installed_txn_id
        else txn_id' = new_installed_txn_id ∨ txn_id' = installed_txn_id) ∧
        let txns := take (S txn_id') txns in
        apply_upds (txn_upds txns) d !! a = Some b⌝ ∗
       a d↦ b ∗ ⌜2 + LogSz ≤ a⌝).

Global Instance is_installed_Timeless γ d txns installed_txn_id diskEnd_txn_id :
  Timeless (is_installed γ d txns installed_txn_id diskEnd_txn_id) := _.

(* weakening of [is_installed] at crash time *)
(* TODO(tej): remove "read" from the name, reading actually uses an accessor
theorem rather than this weakening *)
Definition is_installed_read d txns installed_lb diskEnd_txn_id : iProp Σ :=
  ∃ new_installed_txn_id,
    ⌜(installed_lb ≤ new_installed_txn_id ≤ diskEnd_txn_id ∧ diskEnd_txn_id < length txns)%nat⌝ ∗
  ([∗ map] a ↦ _ ∈ d,
    ∃ (b: Block),
      ⌜∃ txn_id', (txn_id' = installed_lb ∨ txn_id' = new_installed_txn_id) ∧
      apply_upds (txn_upds (take (S txn_id') txns)) d !! a = Some b⌝ ∗
      a d↦ b ∗ ⌜2 + LogSz ≤ a⌝)%I.

Definition circular_pred γ (cs : circΣ.t) : iProp Σ :=
  ghost_var γ.(cs_name) (1/2) cs.

Definition circ_matches_txns (cs:circΣ.t) txns installed_txn_id diskEnd_txn_id :=
  has_updates cs.(circΣ.upds) (subslice installed_txn_id (S diskEnd_txn_id) txns) ∧
  (installed_txn_id ≤ diskEnd_txn_id)%nat.

(** an invariant governing the data logged for crash recovery of (a prefix of)
memLog. *)
Definition is_durable cs txns installed_txn_id diskEnd_txn_id : iProp Σ :=
    "%Hcirc_matches" ∷ ⌜circ_matches_txns cs txns installed_txn_id diskEnd_txn_id⌝.

Definition is_installed_txn γ cs txns installed_txn_id installed_lb: iProp Σ :=
    "%Hinstalled_bound" ∷ ⌜(installed_lb ≤ installed_txn_id)%nat⌝ ∗
    "%Hstart_txn" ∷ ⌜is_txn txns installed_txn_id (circΣ.start cs)⌝ ∗
    "#Hstart_txn_stable" ∷ installed_txn_id [[γ.(stable_txn_ids_name)]]↦ro tt.

Definition is_durable_txn γ cs txns diskEnd_txn_id durable_lb: iProp Σ :=
  ∃ (diskEnd: u64),
    "%Hdurable_lb" ∷ ⌜(durable_lb ≤ diskEnd_txn_id)%nat⌝ ∗
    "%HdiskEnd_val" ∷ ⌜int.val diskEnd = circΣ.diskEnd cs⌝ ∗
    "%Hend_txn" ∷ ⌜is_txn txns diskEnd_txn_id diskEnd⌝ ∗
    "#Hend_txn_stable" ∷ diskEnd_txn_id [[γ.(stable_txn_ids_name)]]↦ro tt.

Definition is_base_disk γ (d : disk) : iProp Σ :=
  own γ.(base_disk_name) (to_agree d : agreeR (leibnizO disk)).

Instance is_base_disk_persistent γ d : Persistent (is_base_disk γ d) := _.

Theorem is_base_disk_agree γ d0 d1 :
  is_base_disk γ d0 -∗ is_base_disk γ d1 -∗ ⌜d0=d1⌝.
Proof.
  rewrite /is_base_disk.
  iIntros "H0 H1".
  iDestruct (own_valid_2 with "H0 H1") as "%H".
Admitted.

Definition disk_inv γ s (cs: circΣ.t) (dinit: disk) : iProp Σ :=
  ∃ installed_txn_id diskEnd_txn_id,
      "Hinstalled" ∷ is_installed γ s.(log_state.d) s.(log_state.txns) installed_txn_id diskEnd_txn_id ∗
      "#Hdurable"   ∷ is_durable cs s.(log_state.txns) installed_txn_id diskEnd_txn_id ∗
      "#circ.start" ∷ is_installed_txn γ cs s.(log_state.txns) installed_txn_id s.(log_state.installed_lb) ∗
      "#circ.end"   ∷ is_durable_txn γ cs s.(log_state.txns) diskEnd_txn_id s.(log_state.durable_lb) ∗
      "%Hdaddrs_init" ∷ ⌜ ∀ a, is_Some (s.(log_state.d) !! a) ↔ is_Some (dinit !! a) ⌝ ∗
      "#Hbasedisk"  ∷ is_base_disk γ s.(log_state.d).

Definition disk_inv_durable γ s (cs: circΣ.t) (dinit: disk) : iProp Σ :=
 ∃ installed_txn_id diskEnd_txn_id,
      (* TODO: what to do with diskEnd_txn_id_name ghost variable? *)
      "Hinstalled" ∷ is_installed_read s.(log_state.d) s.(log_state.txns) s.(log_state.installed_lb) diskEnd_txn_id ∗
      "#Hdurable"   ∷ is_durable cs s.(log_state.txns) installed_txn_id diskEnd_txn_id ∗
      "#circ.start" ∷ is_installed_txn γ cs s.(log_state.txns) installed_txn_id s.(log_state.installed_lb) ∗
      "#circ.end"   ∷ is_durable_txn γ cs s.(log_state.txns) diskEnd_txn_id s.(log_state.durable_lb) ∗
      "%Hdaddrs_init" ∷ ⌜ ∀ a, is_Some (s.(log_state.d) !! a) ↔ is_Some (dinit !! a) ⌝.

Definition stable_sound (txns : list (u64 * list update.t)) (stable_txns : gmap nat unit) :=
  ∀ (txn_id txn_id' : nat) (pos : u64),
    txn_id' > txn_id ->
    stable_txns !! txn_id = Some tt ->
    is_txn txns txn_id pos ->
    is_txn txns txn_id' pos ->
    snd <$> txns !! txn_id' = Some nil.

Definition nextDiskEnd_inv γ (txns : list (u64 * list update.t)) : iProp Σ :=
  ∃ (stable_txns : gmap nat unit),
    "Hstablectx" ∷ map_ctx γ.(stable_txn_ids_name) (1/2) stable_txns ∗
    "Hstablero" ∷ ([∗ map] txn_id ↦ _ ∈ stable_txns, txn_id [[γ.(stable_txn_ids_name)]]↦ro tt) ∗
    "%HafterNextDiskEnd" ∷ ⌜stable_sound txns stable_txns⌝.

(** the complete wal invariant *)
Definition is_wal_inner (l : loc) γ s (dinit : disk) : iProp Σ :=
    "%Hwf" ∷ ⌜wal_wf s⌝ ∗
    "Hmem" ∷ is_wal_mem l γ ∗
    "Htxns_ctx" ∷ txns_ctx γ s.(log_state.txns) ∗
    "γtxns"  ∷ ghost_var γ.(txns_name) (1/2) s.(log_state.txns) ∗
    "HnextDiskEnd_inv" ∷ nextDiskEnd_inv γ s.(log_state.txns) ∗
    "Hdisk" ∷ ∃ cs, "Howncs" ∷ ghost_var γ.(cs_name) (1/2) cs ∗ "Hdisk" ∷ disk_inv γ s cs dinit
.

(* holds for log states which are possible after a crash (essentially these have
no mutable state) *)
Definition wal_post_crash σ: Prop :=
  S (σ.(log_state.durable_lb)) = length σ.(log_state.txns).

Definition is_wal_inner_durable γ s dinit : iProp Σ :=
    "%Hwf" ∷ ⌜wal_wf s⌝ ∗
    "%Hpostcrash" ∷ ⌜wal_post_crash s⌝ ∗
    "Hdisk" ∷ ∃ cs, "Hdiskinv" ∷ disk_inv_durable γ s cs dinit ∗
                    "Hcirc" ∷ is_circular_state γ.(circ_name) cs
.

(* This is produced by recovery as a post condition, can be used to get is_wal *)
Definition is_wal_inv_pre (l: loc) γ s (dinit : disk) : iProp Σ :=
  is_wal_inner l γ s dinit ∗ (∃ cs, is_circular_state γ.(circ_name) cs ∗ circular_pred γ cs).

Definition is_wal (l : loc) γ (dinit : disk) : iProp Σ :=
  inv innerN (∃ σ, is_wal_inner l γ σ dinit ∗ P σ) ∗
  is_circular circN (circular_pred γ) γ.(circ_name).

(** logger_inv is the resources exclusively owned by the logger thread *)
Definition logger_inv γ circ_l: iProp Σ :=
  "HnotLogging" ∷ thread_own γ.(diskEnd_avail_name) Available ∗
  "HownLoggerPos_logger" ∷ (∃ (logger_pos : u64), ghost_var γ.(logger_pos_name) (1/2) logger_pos) ∗
  "HownLoggerTxn_logger" ∷ (∃ (logger_txn_id : nat), ghost_var γ.(logger_txn_id_name) (1/2) logger_txn_id) ∗
  "Happender" ∷ is_circular_appender γ.(circ_name) circ_l.

(* TODO: also needs authoritative ownership of some other variables *)
(** installer_inv is the resources exclusively owned by the installer thread *)
Definition installer_inv γ: iProp Σ :=
  "HnotInstalling" ∷ thread_own γ.(start_avail_name) Available.
  (* XXX definitely missing stuff *)
  (* being_installed = ∅ *)
  (* need ownership of ghost var half for stating this.. *)

Global Instance is_installed_read_Timeless {d txns installed_lb diskEnd_txn_id} :
  Timeless (is_installed_read d txns installed_lb diskEnd_txn_id) := _.

(* this illustrates what crashes rely on; at crash time being_installed is
arbitrary, so we weaken to this *)
Theorem is_installed_weaken_read γ d txns installed_lb diskEnd_txn_id :
  is_installed γ d txns installed_lb diskEnd_txn_id -∗
  is_installed_read d txns installed_lb diskEnd_txn_id.
Proof.
  rewrite /is_installed /is_installed_read.
  iIntros "I".
  iNamed "I".
  iExists new_installed_txn_id.
  iSplit; [ done | ].
  iApply (big_sepM_mono with "Hdata").
  iIntros (a b0 Hlookup) "HI".
  iDestruct "HI" as (b' txn_id') "([% %] & Hb&%)".
  iExists b'; iFrame.
  iPureIntro.
  split; [|done].
  exists txn_id'. split; [|done].
  destruct (decide _); intuition; subst; auto.
Qed.

(* TODO: this isn't true, because [is_installed_read] is too weak, allowing
every address to be any txn_id in the right range; we can prove something
intermediate between these predicates that is true on crash but does guarantee
that every address is one of the two transactions, and that can be restored on
crash *)
Theorem is_installed_restore_read γ d txns installed_txn_id diskEnd_txn_id new_installed_txn_id :
  ghost_var γ.(installed_txn_name) (1/2) installed_txn_id -∗
  ghost_var γ.(being_installed_name) (1/2) (∅: gset Z) -∗
  ghost_var γ.(being_installed_txns_name) (1/2)
    (subslice (S installed_txn_id) (S new_installed_txn_id) txns) -∗
  is_installed_read d txns installed_txn_id diskEnd_txn_id -∗
  is_installed γ d txns installed_txn_id diskEnd_txn_id.
Proof.
  iIntros "Hinstalled_txn Hbeing_installed Hbeing_installed_txns Hinstalled_read".
  iDestruct "Hinstalled_read" as (new_installed_txn_id' Hbounds) "Hd".
  (* TODO: [new_installed_txn_id] is used in both ghost variable and in
   [is_installed_read], can't be in both; might get fixed by getting rid of
   [being_installed_txns_name] *)
Abort.

Theorem is_wal_read_mem l γ dinit : is_wal l γ dinit -∗ |={⊤}=> ▷ is_wal_mem l γ.
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

Theorem is_wal_open l wn dinit E :
  ↑innerN ⊆ E ->
  is_wal l wn dinit
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
  ghost_var γ.(cs_name) (1/2) cs -∗
  |NC={E}=> ⌜lb ≤ circΣ.diskEnd cs⌝ ∗ ghost_var γ.(cs_name) (1/2) cs.
Proof.
  rewrite /circular_pred.
  iIntros (Hsub) "#HdiskEnd_lb #Hcirc Hown".
  iInv "Hcirc" as ">Hinner" "Hclose".
  iDestruct "Hinner" as (σ) "(Hstate&Hγ)".
  unify_ghost_var γ.(cs_name).
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
  ghost_var γ.(cs_name) (1/2) cs -∗
  |NC={E}=> ⌜diskEnd = circΣ.diskEnd cs⌝ ∗
          diskEnd_is γ.(circ_name) q diskEnd ∗
          ghost_var γ.(cs_name) (1/2) cs.
Proof.
  rewrite /circular_pred.
  iIntros (Hsub) "HdiskEnd_is #Hcirc Hown".
  iInv "Hcirc" as ">Hinner" "Hclose".
  iDestruct "Hinner" as (σ) "(Hstate&Hγ)".
  unify_ghost_var γ.(cs_name).
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

Definition wal_names_dummy {hG:gen_heapPreG nat (u64 * list update.t) Σ} : wal_names.
  constructor; try exact inhabitant.
Defined.

Theorem alloc_txns_ctx E txns :
  ⊢ |={E}=> ∃ γtxns, txns_ctx (wal_names_dummy <|txns_ctx_name := γtxns|>) txns.
Proof.
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

Theorem is_wal_txns_lookup l γ σ dinit :
  is_wal_inner l γ σ dinit -∗
  (∃ txns, txns_ctx γ txns ∗ ghost_var γ.(txns_name) (1/2) txns ∗
             (txns_ctx γ txns ∗ ghost_var γ.(txns_name) (1/2) txns -∗
              is_wal_inner l γ σ dinit)).
Proof.
  iNamed 1.
  iExists _; iFrame.
  by iIntros "($ & $)".
Qed.

Theorem txn_pos_valid_locked l γ dinit txns txn_id pos :
  is_wal l γ dinit -∗
  txn_pos γ txn_id pos -∗
  ghost_var γ.(txns_name) (1/2) txns -∗
  |={⊤}=> ⌜is_txn txns txn_id pos⌝ ∗ ghost_var γ.(txns_name) (1/2) txns.
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

(** XXX THIS SEEMS IMPORTANT: *)
Definition txns_are γ (start: nat) (txns_sub: list (u64*list update.t)) : iProp Σ :=
  list_subseq γ.(txns_ctx_name) start txns_sub.

(** XXX THIS SEEMS IMPORTANT: *)
Global Instance txns_are_Persistent γ start txns_sub : Persistent (txns_are γ start txns_sub).
Proof. apply _. Qed.

(** XXX THIS SEEMS IMPORTANT: *)
Theorem txns_are_sound γ txns start txns_sub :
  txns_ctx γ txns -∗
  txns_are γ start txns_sub -∗
  ⌜subslice start (start + length txns_sub)%nat txns = txns_sub⌝.
Proof.
  iIntros "Hctx Htxns_are".
  iDestruct (alist_subseq_lookup with "Hctx Htxns_are") as "$".
Qed.

Theorem get_txns_are l γ dinit txns start till txns_sub :
  txns_sub = subslice start till txns →
  (start ≤ till ≤ length txns)%nat →
  ghost_var γ.(txns_name) (1/2) txns -∗
  is_wal l γ dinit -∗
  |={⊤}=> txns_are γ start txns_sub ∗ ghost_var γ.(txns_name) (1/2) txns.
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

Lemma is_txn_pos_unique txns tid pos pos' :
  is_txn txns tid pos ->
  is_txn txns tid pos' ->
  pos = pos'.
Proof.
  rewrite /is_txn. congruence.
Qed.

Lemma wal_wf_txns_mono_pos {σ txn_id1 pos1 txn_id2 pos2} :
  wal_wf σ ->
  is_txn σ.(log_state.txns) txn_id1 pos1 ->
  is_txn σ.(log_state.txns) txn_id2 pos2 ->
  int.val pos1 < int.val pos2 ->
  (txn_id1 < txn_id2)%nat.
Proof.
  destruct 1 as (_&Hmono&_).
  destruct (decide (txn_id1 = txn_id2)).
  { subst. intros.
    exfalso. pose proof (is_txn_pos_unique _ _ _ _ H H0). subst. lia. }
  rewrite /is_txn; intros.
  destruct (decide (txn_id1 ≤ txn_id2)%nat); first by lia.
  assert (txn_id2 < txn_id1)%nat as Hord by lia.
  rewrite -list_lookup_fmap in H.
  rewrite -list_lookup_fmap in H0.
  eapply (Hmono _ _) in Hord; eauto.
  word. (* contradiction from [pos1 = pos2] *)
Qed.

Lemma wal_wf_txns_mono_pos' {σ txn_id1 pos1 txn_id2 pos2} :
  wal_wf σ ->
  is_txn σ.(log_state.txns) txn_id1 pos1 ->
  is_txn σ.(log_state.txns) txn_id2 pos2 ->
  (txn_id1 ≤ txn_id2)%nat ->
  int.val pos1 ≤ int.val pos2.
Proof.
  clear P.
  rewrite /wal_wf /is_txn; intuition.
  destruct (decide (txn_id1 = txn_id2)); subst.
  { rewrite H0 in H1. replace pos1 with pos2 by congruence. lia. }
  eapply (H txn_id1 txn_id2); first by lia.
  { rewrite list_lookup_fmap; eauto. }
  { rewrite list_lookup_fmap; eauto. }
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
  - assert (txn_id1 < txn_id2)%nat; try lia.
    eapply wal_wf_txns_mono_pos; eauto.
    + eapply Htxn2.
    + assert (int.val pos1 ≠ int.val pos2).
      { intro H.
        assert (pos1 = pos2) by word; congruence. }
      lia.
Qed.

Lemma memLog_linv_pers_core_strengthen γ σ diskEnd diskEnd_txn_id nextDiskEnd_txn_id
      txns (logger_pos : u64) (logger_txn_id : nat):
  (memLog_linv_pers_core γ σ diskEnd diskEnd_txn_id nextDiskEnd_txn_id txns logger_pos logger_txn_id) -∗
  (ghost_var γ.(txns_name) (1/2) txns) -∗
  (ghost_var γ.(logger_pos_name) (1 / 2) logger_pos) -∗
  (ghost_var γ.(logger_txn_id_name) (1 / 2) logger_txn_id) -∗
  memLog_linv_nextDiskEnd_txn_id γ σ.(slidingM.mutable) nextDiskEnd_txn_id -∗
  memLog_linv γ σ diskEnd diskEnd_txn_id.
Proof.
  iNamed 1. iIntros "Ht Hlp Hlt Hnext". iExists _, _, _, _, _. iFrame "∗ # %".
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

Lemma is_wal_inner_base_disk γ σ dinit walptr :
  is_wal_inner walptr γ σ dinit -∗
  is_base_disk γ σ.(log_state.d).
Proof.
  iNamed 1.
  iNamed "Hdisk".
  iNamed "Hdisk".
  iFrame "#".
Qed.

End goose_lang.

Ltac destruct_is_wal :=
  iMod (is_wal_read_mem with "Hwal") as "#Hmem";
  wp_call;
  iNamed "Hmem"; iNamed "Hstfields".

Hint Unfold locked_wf : word.
