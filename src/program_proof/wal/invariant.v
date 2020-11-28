From Goose.github_com.mit_pdos.goose_nfsd Require Export wal.
From RecordUpdate Require Import RecordUpdate.
From iris.algebra Require Import gset.

From Perennial.Helpers Require Export Transitions List NamedProps PropRestore Map.

From Perennial.algebra Require Export deletable_heap append_list auth_map fmcounter.
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
    (* TODO: switch over to Iris mnat entirely *)
    wal_fmcounter    :> fmcounterG Σ;
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
    (* the range (being_installed_start, being_installed_end] is the range of txns that the installer is installing *)
    (* when not installing, we should have being_installed_start = being_installed_end = installed_txn *)
    (* TODO: being_installed_end_txn should always be the same as installer_txn, remove the redundancy *)
    (* TODO: rename being_installed_start_txn to installed_txn since they are now always the same *)
    being_installed_start_txn_name : gname;
    being_installed_end_txn_name : gname;
    already_installed_name : gname;
    diskEnd_avail_name : gname;
    start_avail_name : gname;
    stable_txn_ids_name : gname;
    logger_pos_name : gname;
    (* TODO: this is the logger's next transaction id? *)
    logger_txn_id_name : gname;
    (* this is the pos/txnid captured by the installer when it starts installing *)
    (* this is used for the lock invariant *)
    installer_pos_mem_name : gname;
    installer_txn_id_mem_name : gname;
    (* this is used for the wal invariant *)
    installer_pos_name : gname;
    installer_txn_id_name : gname;
    (* this is the in-memory diskEnd (not the on-disk diskEnd) *)
    (* it's used to break up has_updates for the circular queue so that the installer can Advance just to that point *)
    diskEnd_mem_name : gname;
    diskEnd_mem_txn_id_name : gname;
    installed_pos_mem_name : gname;
    installed_txn_id_mem_name : gname;
    base_disk_name : gname;
  }.

Global Instance _eta_wal_names : Settable _ :=
  settable! mkWalNames <circ_name; cs_name; txns_ctx_name; txns_name;
                        being_installed_start_txn_name; being_installed_end_txn_name; already_installed_name;
                        diskEnd_avail_name; start_avail_name;
                        stable_txn_ids_name;
                        logger_pos_name; logger_txn_id_name;
                        installer_pos_mem_name; installer_txn_id_mem_name;
                        installer_pos_name; installer_txn_id_name;
                        diskEnd_mem_name; diskEnd_mem_txn_id_name;
                        installed_pos_mem_name; installed_txn_id_mem_name;
                        base_disk_name>.

Implicit Types (γ: wal_names).
Implicit Types (s: log_state.t) (memLog: slidingM.t) (txns: list (u64 * list update.t)).
Implicit Types (pos: u64) (being_installed_start_txn_id diskEnd_txn_id nextDiskEnd_txn_id txn_id: nat).

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
  int.Z σ.(memLog).(slidingM.start) ≤ int.Z σ.(diskEnd) ≤ int.Z σ.(memLog).(slidingM.mutable) ∧
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

Lemma txns_ctx_app {γ} txns' txns : txns_ctx γ txns ==∗ txns_ctx γ (txns ++ txns').
Proof.
  rewrite /txns_ctx.
  iIntros "Hctx".
  by iMod (alist_app _ txns' with "Hctx") as "[$ _]".
Qed.

Global Instance txn_pos_timeless γ txn_id pos :
  Timeless (txn_pos γ txn_id pos) := _.

Global Instance txn_pos_persistent γ txn_id pos :
  Persistent (txn_pos γ txn_id pos) := _.

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

Lemma txns_are_nil γ start : ⊢ txns_are γ start [].
Proof.
  iApply list_subseq_nil.
Qed.

Definition memLog_linv_txns (σ: slidingM.t)
           (installer_pos_mem diskEnd logger_pos: u64) txns
           installed_txn_id_mem installer_txn_id_mem diskEnd_txn_id
           logger_txn_id nextDiskEnd_txn_id : iProp Σ :=
  "%His_installerEnd" ∷
    ⌜has_updates
      (take (slidingM.logIndex σ installer_pos_mem)
            σ.(slidingM.log))
      (subslice (S installed_txn_id_mem) (S installer_txn_id_mem) txns)⌝ ∗
  "%His_diskEnd" ∷
    ⌜has_updates
      (subslice (slidingM.logIndex σ installer_pos_mem)
                (slidingM.logIndex σ diskEnd)
                σ.(slidingM.log))
      (subslice (S installer_txn_id_mem) (S diskEnd_txn_id) txns)⌝ ∗
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
abstract state starting at the installed_txn_id_mem *)
Definition is_mem_memLog memLog txns installed_txn_id_mem : Prop :=
  has_updates memLog.(slidingM.log) (drop (S installed_txn_id_mem) txns) ∧
  (Forall (λ pos, int.Z pos ≤ slidingM.memEnd memLog) txns.*1).

Reserved Notation "x ≤ y ≤ z ≤ v ≤ w"
  (at level 70, y at next level, z at next level, v at next level).
Notation "x ≤ y ≤ z ≤ v ≤ w" := (x ≤ y ∧ y ≤ z ∧ z ≤ v ∧ v ≤ w)%nat : nat_scope.

Reserved Notation "x ≤ y ≤ z ≤ u ≤ v ≤ w"
  (at level 70, y at next level, z at next level, u at next level, v at next level).
Notation "x ≤ y ≤ z ≤ u ≤ v ≤ w" := (x ≤ y ∧ y ≤ z ∧ z ≤ u ∧ u ≤ v ∧ v ≤ w)%nat : nat_scope.

Reserved Notation "x ≤ y ≤ z ≤ v ≤ w"
  (at level 70, y at next level, z at next level, v at next level).
Notation "x ≤ y ≤ z ≤ v ≤ w" := (x ≤ y ∧ y ≤ z ∧ z ≤ v ∧ v ≤ w) : Z_scope.

Definition memLog_linv_pers_core γ (σ: slidingM.t)
  (diskEnd: u64) (diskEnd_txn_id installed_txn_id_mem nextDiskEnd_txn_id: nat)
  (txns: list (u64 * list update.t)) (logger_pos : u64) (logger_txn_id : nat)
  (installer_pos_mem : u64) (installer_txn_id_mem : nat) : iProp Σ :=
    "%Hlog_index_ordering" ∷ ⌜int.Z σ.(slidingM.start) ≤ int.Z installer_pos_mem ≤ int.Z diskEnd ≤ int.Z logger_pos ≤ int.Z σ.(slidingM.mutable)⌝ ∗
    "%Htxn_id_ordering" ∷ ⌜(installed_txn_id_mem ≤ installer_txn_id_mem ≤ diskEnd_txn_id ≤ logger_txn_id ≤ nextDiskEnd_txn_id)%nat⌝ ∗
    "#HmemStart_txn" ∷ txn_pos γ installed_txn_id_mem σ.(slidingM.start) ∗
    "%HdiskEnd_txn" ∷ ⌜is_txn txns diskEnd_txn_id diskEnd⌝ ∗
    "#HdiskEnd_stable" ∷ diskEnd_txn_id [[γ.(stable_txn_ids_name)]]↦ro tt ∗
    "#HmemEnd_txn" ∷ txn_pos γ (length txns - 1)%nat (slidingM.endPos σ) ∗
    (* being_installed_start being used as a proxy for on-disk installed_txn *)
    "#HinstalledTxn_lb" ∷ fmcounter_lb γ.(being_installed_start_txn_name) installed_txn_id_mem ∗
    (* Here we establish what the memLog contains, which is necessary for reads
    to work (they read through memLogMap, but the lock invariant establishes
    that this matches memLog). *)
    "#Htxns" ∷ memLog_linv_txns σ
      installer_pos_mem diskEnd logger_pos txns
      installed_txn_id_mem installer_txn_id_mem diskEnd_txn_id logger_txn_id nextDiskEnd_txn_id ∗
    (* this should be true from wal_wf_txns_mono_pos' and HmemEnd_txn *)
    "%Htxnpos_bound" ∷
      ⌜(Forall (λ pos, int.Z pos ≤ slidingM.memEnd σ) txns.*1)⌝
  .

Global Instance memLog_linv_pers_core_persistent γ σ diskEnd diskEnd_txn_id installed_txn_id_mem nextDiskEnd_txn_id txns logger_pos logger_txn_id installer_pos_mem installer_txn_id_mem :
  Persistent (memLog_linv_pers_core γ σ diskEnd diskEnd_txn_id installed_txn_id_mem nextDiskEnd_txn_id txns logger_pos logger_txn_id installer_pos_mem installer_txn_id_mem).
Proof. apply _. Qed.

Definition memLog_linv_nextDiskEnd_txn_id γ mutable nextDiskEnd_txn_id : iProp Σ :=
  ∃ (stable_txns: gmap nat unit),
      "HownStableSet" ∷ map_ctx γ.(stable_txn_ids_name) (1/2) stable_txns ∗
      "#HnextDiskEnd_stable" ∷ nextDiskEnd_txn_id [[γ.(stable_txn_ids_name)]]↦ro tt ∗
      "#HnextDiskEnd_txn" ∷ txn_pos γ nextDiskEnd_txn_id mutable ∗
      "%HnextDiskEnd_max_stable" ∷
        ⌜∀ txn_id, txn_id > nextDiskEnd_txn_id -> stable_txns !! txn_id = None⌝.

Definition memLog_linv_core γ (σ: slidingM.t) (diskEnd: u64) (diskEnd_txn_id: nat)
                            (installed_txn_id_mem: nat) (nextDiskEnd_txn_id: nat)
                            (txns: list (u64 * list update.t))
                            (logger_pos: u64) (logger_txn_id : nat)
                            (installer_pos_mem: u64) (installer_txn_id_mem : nat) : iProp Σ :=
    "#Hlinv_pers" ∷ memLog_linv_pers_core γ σ diskEnd diskEnd_txn_id installed_txn_id_mem nextDiskEnd_txn_id txns logger_pos logger_txn_id installer_pos_mem installer_txn_id_mem ∗
    "Howntxns" ∷ ghost_var γ.(txns_name) (1/2) txns ∗
    "HnextDiskEnd" ∷ memLog_linv_nextDiskEnd_txn_id γ σ.(slidingM.mutable) nextDiskEnd_txn_id ∗
    "HownLoggerPos_linv" ∷ ghost_var γ.(logger_pos_name) (1/2) logger_pos ∗
    "HownLoggerTxn_linv" ∷ ghost_var γ.(logger_txn_id_name) (1/2) logger_txn_id ∗
    "HownInstallerPosMem_linv" ∷ ghost_var γ.(installer_pos_mem_name) (1/2) installer_pos_mem ∗
    "HownInstallerTxnMem_linv" ∷ ghost_var γ.(installer_txn_id_mem_name) (1/2) installer_txn_id_mem ∗
    "HownDiskEndMem_linv" ∷ fmcounter γ.(diskEnd_mem_name) (1/2) (int.nat diskEnd) ∗
    "HownDiskEndMemTxn_linv" ∷ fmcounter γ.(diskEnd_mem_txn_id_name) (1/2) diskEnd_txn_id ∗
    "HownInstalledPosMem_linv" ∷ ghost_var γ.(installed_pos_mem_name) (1/2) σ.(slidingM.start) ∗
    "HownInstalledTxnMem_linv" ∷ ghost_var γ.(installed_txn_id_mem_name) (1/2) installed_txn_id_mem
  .

Definition memLog_linv γ (σ: slidingM.t) (diskEnd: u64) diskEnd_txn_id : iProp Σ :=
  (∃ (installed_txn_id_mem: nat) (nextDiskEnd_txn_id: nat)
     (txns: list (u64 * list update.t))
     (logger_pos: u64) (logger_txn_id : nat)
     (installer_pos_mem: u64) (installer_txn_id_mem : nat),
      memLog_linv_core γ σ diskEnd diskEnd_txn_id
        installed_txn_id_mem nextDiskEnd_txn_id
        txns logger_pos logger_txn_id
        installer_pos_mem installer_txn_id_mem
  ).

(* this is what witnesses the basic role of the memLog, which is to contain all
the updates (expressed in memLog_linv_txns in a finer-grained way for all the
subsets, which are needed by the logger/installer but not for reads) *)
Lemma memLog_linv_txns_combined_updates memLog diskEnd installer_pos_mem logger_pos txns installed_txn_id_mem diskEnd_txn_id installer_txn_id_mem logger_txn_id nextDiskEnd_txn_id :
    ∀ (Htxn_id_ordering: (installed_txn_id_mem ≤ installer_txn_id_mem ≤ diskEnd_txn_id ≤ logger_txn_id ≤ nextDiskEnd_txn_id)%nat)
      (Hlog_index_ordering: int.Z installer_pos_mem ≤ int.Z diskEnd ≤ int.Z logger_pos ≤ int.Z memLog.(slidingM.mutable)),
    memLog_linv_txns memLog installer_pos_mem diskEnd logger_pos txns installed_txn_id_mem installer_txn_id_mem diskEnd_txn_id logger_txn_id nextDiskEnd_txn_id -∗
    ⌜has_updates memLog.(slidingM.log) (drop (S installed_txn_id_mem) txns)⌝.
Proof.
  intros ??.
  iNamed 1.
  pose proof (has_updates_app _ _ _ _ His_installerEnd His_diskEnd) as Hhas_updates_mid.
  rewrite -subslice_from_start subslice_app_contig in Hhas_updates_mid.
  2: rewrite /slidingM.logIndex; lia.
  rewrite subslice_from_start subslice_app_contig in Hhas_updates_mid.
  2: rewrite /slidingM.logIndex; lia.
  pose proof (has_updates_app _ _ _ _ Hhas_updates_mid His_loggerEnd) as Hhas_updates_mid'.
  rewrite -subslice_from_start subslice_app_contig in Hhas_updates_mid'.
  2: rewrite /slidingM.logIndex; lia.
  rewrite subslice_from_start subslice_app_contig in Hhas_updates_mid'.
  2: rewrite /slidingM.logIndex; lia.
  pose proof (has_updates_app _ _ _ _ Hhas_updates_mid' His_nextDiskEnd) as Hhas_updates_mid''.
  rewrite -subslice_from_start subslice_app_contig in Hhas_updates_mid''.
  2: rewrite /slidingM.logIndex; lia.
  rewrite subslice_from_start subslice_app_contig in Hhas_updates_mid''.
  2: rewrite /slidingM.logIndex; lia.
  pose proof (has_updates_app _ _ _ _ Hhas_updates_mid'' His_nextTxn) as Hhas_updates.
  rewrite take_drop /subslice drop_take_drop in Hhas_updates; try lia.
  auto.
Qed.

(* NOTE(tej): this is only proven because it was there before; it's just like
the above but integrates Htxnpos_bound into the result *)
Lemma memLog_linv_txns_to_is_mem_memLog memLog installer_pos_mem diskEnd logger_pos txns installed_txn_id_mem installer_txn_id_mem diskEnd_txn_id logger_txn_id nextDiskEnd_txn_id :
    ∀ (Htxn_id_ordering: (installed_txn_id_mem ≤ installer_txn_id_mem ≤ diskEnd_txn_id ≤ logger_txn_id ≤ nextDiskEnd_txn_id)%nat)
      (Hlog_index_ordering: int.Z installer_pos_mem ≤ int.Z diskEnd ≤ int.Z logger_pos ≤ int.Z memLog.(slidingM.mutable))
      (Htxnpos_bound: Forall (λ pos, int.Z pos ≤ slidingM.memEnd memLog) txns.*1),
    memLog_linv_txns memLog installer_pos_mem diskEnd logger_pos txns installed_txn_id_mem installer_txn_id_mem diskEnd_txn_id logger_txn_id nextDiskEnd_txn_id -∗
    ⌜is_mem_memLog memLog txns installed_txn_id_mem⌝.
Proof.
  iIntros (???) "Htxns".
  iDestruct (memLog_linv_txns_combined_updates with "Htxns") as %Hupds; auto.
Qed.

Definition wal_linv_fields st σ: iProp Σ :=
  (∃ σₗ,
      "Hfield_ptsto" ∷
         ("HmemLog" ∷ st ↦[WalogState.S :: "memLog"] #σₗ.(memLogPtr) ∗
          "HdiskEnd" ∷ st ↦[WalogState.S :: "diskEnd"] #σ.(diskEnd) ∗
          "Hshutdown" ∷ st ↦[WalogState.S :: "shutdown"] #σₗ.(shutdown) ∗
          "Hnthread" ∷ st ↦[WalogState.S :: "nthread"] #σₗ.(nthread)) ∗
  "%Hlocked_wf" ∷ ⌜locked_wf σ⌝ ∗
  "His_memLog" ∷ is_sliding σₗ.(memLogPtr) 1 σ.(memLog)
  )%I.

Definition diskEnd_linv γ (diskEnd: u64) : iProp Σ :=
  "#HdiskEnd_at_least" ∷ diskEnd_at_least γ.(circ_name) (int.Z diskEnd) ∗
  "HdiskEnd_exactly" ∷ thread_own_ctx γ.(diskEnd_avail_name)
                         ("HdiskEnd_is" ∷ diskEnd_is γ.(circ_name) (1/2) (int.Z diskEnd)).

Definition diskStart_linv γ (start: u64): iProp Σ :=
  "#Hstart_at_least" ∷ start_at_least γ.(circ_name) start ∗
  "Hstart_exactly" ∷ thread_own_ctx γ.(start_avail_name)
                       ("Hstart_is" ∷ start_is γ.(circ_name) (1/2) start).

(** the lock invariant protecting the WalogState, corresponding to l.memLock *)
Definition wal_linv (st: loc) γ : iProp Σ :=
  ∃ σ,
    "Hfields" ∷ wal_linv_fields st σ ∗
    "HdiskEnd_circ" ∷ diskEnd_linv γ σ.(diskEnd) ∗
    "Hstart_circ" ∷ diskStart_linv γ σ.(memLog).(slidingM.start) ∗
    "HmemLog_linv" ∷ memLog_linv γ σ.(memLog) σ.(diskEnd) σ.(locked_diskEnd_txn_id).

(* TODO: when possible, refactor wal_linv to use this directly *)
Definition wal_linv_durable γ cs : iProp Σ :=
  ∃ σls,
    ⌜ int.Z σls.(diskEnd) = circΣ.diskEnd cs ⌝ ∗
    ⌜ σls.(memLog) = {| slidingM.log := cs.(circΣ.upds);
                              slidingM.start := cs.(circΣ.start);
                              slidingM.mutable := U64 (circΣ.diskEnd cs);
                     |} ⌝ ∗
    ⌜ locked_wf σls ⌝ ∗
    "HdiskEnd_circ" ∷ diskEnd_linv γ σls.(diskEnd) ∗
    "Hstart_circ" ∷ diskStart_linv γ σls.(memLog).(slidingM.start) ∗
    "HmemLog_linv" ∷ memLog_linv γ σls.(memLog) σls.(diskEnd) σls.(locked_diskEnd_txn_id).

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

Global Instance is_wal_mem_persistent l γ : Persistent (is_wal_mem l γ) := _.

Definition is_dblock_with_txns d txns (being_installed_start_txn_id: nat) (being_installed_end_txn_id: nat) (already_installed: gset Z) a : iProp Σ :=
  ∃ (b: Block) (txn_id': nat),
     (* every disk block has at least up to (being_installed_start_txn_id - 1)
     (most have exactly, but some blocks may be in the process of being installed) *)
     ⌜being_installed_start_txn_id ≤ txn_id' ≤ being_installed_end_txn_id ∧
      ( a ∈ already_installed → txn_id' = being_installed_end_txn_id ) ∧
      let subtxns := take (S txn_id') txns in
      apply_upds (txn_upds subtxns) d !! a = Some b⌝ ∗
     a d↦ b ∗ ⌜2 + LogSz ≤ a⌝.

(* this part of the invariant holds the installed disk blocks from the data
region of the disk and relates them to the logical installed disk, computed via
the updates through some installed transaction. *)
Definition is_installed_core γ d txns (installed_txn_id being_installed_end_txn_id diskEnd_txn_id: nat) (already_installed: gset Z) : iProp Σ :=
  (* TODO(tej): the other half of these are owned by the installer, giving it full
   knowledge of in-progress installations and exclusive update rights; need to
   write down what it maintains as part of its loop invariant *)
  "Howninstalled" ∷ (
    (* why do these need to be fmcounters? *)
    "HownBeingInstalledStartTxn_walinv" ∷ fmcounter γ.(being_installed_start_txn_name) (1/2) installed_txn_id ∗
    "HownBeingInstalledEndTxn_walinv" ∷ ghost_var γ.(being_installed_end_txn_name) (1/2) being_installed_end_txn_id ∗
    "Halready_installed" ∷ ghost_var γ.(already_installed_name) (1/2) already_installed) ∗
  (* TODO: ⌜diskEnd_txn_id < length txns⌝ shouldn't be necessary, follows from Hend_txn in is_durable *)
  "%Hinstalled_bounds" ∷ ⌜(installed_txn_id ≤ installed_txn_id ≤ being_installed_end_txn_id ≤ diskEnd_txn_id ∧ diskEnd_txn_id < length txns)%nat⌝ ∗
  "#Hbeing_installed_txns" ∷ txns_are γ (S installed_txn_id)
    (subslice (S installed_txn_id) (S being_installed_end_txn_id) txns) ∗
  "Hdata" ∷ ([∗ map] a ↦ _ ∈ d, is_dblock_with_txns d txns installed_txn_id being_installed_end_txn_id already_installed a).

Global Instance is_installed_core_Timeless γ d txns installed_txn_id being_installed_end_txn_id diskEnd_txn_id already_installed :
  Timeless (is_installed_core γ d txns installed_txn_id being_installed_end_txn_id diskEnd_txn_id already_installed) := _.

Definition is_installed γ d txns (installed_txn_id: nat) (diskEnd_txn_id: nat) : iProp Σ :=
  ∃ being_installed_end_txn_id already_installed,
    is_installed_core γ d txns installed_txn_id being_installed_end_txn_id diskEnd_txn_id already_installed.

(* weakening of [is_installed] at crash time *)
(* TODO(tej): remove "read" from the name, reading actually uses an accessor
theorem rather than this weakening *)
Definition is_installed_read d txns installed_lb diskEnd_txn_id being_installed_end_txn_id : iProp Σ :=
  ∃ γ already_installed,
    is_installed_core γ d txns installed_lb diskEnd_txn_id being_installed_end_txn_id already_installed.

Definition circular_pred γ (cs : circΣ.t) : iProp Σ :=
  ghost_var γ.(cs_name) (1/2) cs.

Definition circ_matches_txns (cs:circΣ.t) txns
           installed_txn_id installer_pos installer_txn_id
           diskEnd_mem diskEnd_mem_txn_id diskEnd_txn_id :=
  has_updates (take (installer_pos - int.nat cs.(circΣ.start)) cs.(circΣ.upds))
    (subslice (S installed_txn_id) (S installer_txn_id) txns) ∧
  has_updates (subslice (installer_pos - int.nat cs.(circΣ.start)) (diskEnd_mem - int.nat cs.(circΣ.start)) cs.(circΣ.upds))
    (subslice (S installer_txn_id) (S diskEnd_mem_txn_id) txns) ∧
  has_updates (drop (diskEnd_mem - int.nat cs.(circΣ.start)) cs.(circΣ.upds))
    (subslice (S diskEnd_mem_txn_id) (S diskEnd_txn_id) txns) ∧
  (int.nat cs.(circΣ.start) ≤ installer_pos ≤ diskEnd_mem ≤ Z.to_nat (circΣ.diskEnd cs))%nat ∧
  (installed_txn_id ≤ installer_txn_id ≤ diskEnd_mem_txn_id ≤ diskEnd_txn_id)%nat.

Lemma circ_matches_txns_combine cs txns
      installed_txn_id installer_pos installer_txn_id
      diskEnd_mem diskEnd_mem_txn_id diskEnd_txn_id :
  circ_matches_txns cs txns installed_txn_id installer_pos installer_txn_id
                    diskEnd_mem diskEnd_mem_txn_id diskEnd_txn_id →
  has_updates cs.(circΣ.upds) (subslice (S installed_txn_id) (S diskEnd_txn_id) txns).
Proof.
  destruct 1 as (Hupds1 & Hupds2 & Hupds3 & ?&?).
  rewrite /circΣ.diskEnd in H.
  pose proof (has_updates_app _ _ _ _ Hupds1 Hupds2) as Hupds12.
  pose proof (has_updates_app _ _ _ _ Hupds12 Hupds3) as Hupds123.
  match type of Hupds123 with
  | has_updates ?us ?txns =>
    lazymatch goal with
    | |- has_updates ?us' ?txns' =>
      replace us' with us;
        [ replace txns' with txns;
          [ assumption | ]
        | ]
    end
  end.
  - rewrite -> subslice_app_contig by lia.
    rewrite -> subslice_app_contig by lia.
    auto.
  - rewrite subslice_from_take.
    rewrite subslice_from_drop.
    rewrite -> subslice_app_contig by lia.
    rewrite -> subslice_app_contig by lia.
    rewrite -subslice_complete //.
Qed.

(** an invariant governing the data logged for crash recovery of (a prefix of)
memLog. *)
Definition is_durable γ cs txns installed_txn_id diskEnd_txn_id : iProp Σ :=
  ∃ (installer_pos installer_txn_id diskEnd_mem diskEnd_mem_txn_id: nat),
    "HownInstallerPos_walinv" ∷ ghost_var γ.(installer_pos_name) (1/2) installer_pos ∗
    "HownInstallerTxn_walinv" ∷ ghost_var γ.(installer_txn_id_name) (1/2) installer_txn_id ∗
    "HownDiskEndMem_walinv" ∷ fmcounter γ.(diskEnd_mem_name) (1/2) diskEnd_mem ∗
    "HownDiskEndMemTxn_walinv" ∷ fmcounter γ.(diskEnd_mem_txn_id_name) (1/2) diskEnd_mem_txn_id ∗
    "%Hcirc_matches" ∷ ⌜circ_matches_txns cs txns installed_txn_id installer_pos installer_txn_id diskEnd_mem diskEnd_mem_txn_id diskEnd_txn_id⌝.

Definition is_installed_txn γ cs txns installed_txn_id installed_lb: iProp Σ :=
    "%Hinstalled_bound" ∷ ⌜(installed_lb ≤ installed_txn_id)%nat⌝ ∗
    "%Hstart_txn" ∷ ⌜is_txn txns installed_txn_id (circΣ.start cs)⌝ ∗
    "#Hstart_txn_stable" ∷ installed_txn_id [[γ.(stable_txn_ids_name)]]↦ro tt.

Definition is_durable_txn γ cs txns diskEnd_txn_id durable_lb: iProp Σ :=
  ∃ (diskEnd: u64),
    "%Hdurable_lb" ∷ ⌜(durable_lb ≤ diskEnd_txn_id)%nat⌝ ∗
    "%HdiskEnd_val" ∷ ⌜int.Z diskEnd = circΣ.diskEnd cs⌝ ∗
    "%Hend_txn" ∷ ⌜is_txn txns diskEnd_txn_id diskEnd⌝ ∗
    "#Hend_txn_stable" ∷ diskEnd_txn_id [[γ.(stable_txn_ids_name)]]↦ro tt.

Definition is_base_disk γ (d : disk) : iProp Σ :=
  own γ.(base_disk_name) (to_agree d : agreeR diskO).

Global Instance is_base_disk_persistent γ d : Persistent (is_base_disk γ d) := _.
Global Instance is_base_disk_timeless γ d : Timeless (is_base_disk γ d) := _.

Theorem is_base_disk_agree γ d0 d1 :
  is_base_disk γ d0 -∗ is_base_disk γ d1 -∗ ⌜d0=d1⌝.
Proof.
  rewrite /is_base_disk.
  iIntros "H0 H1".
  iDestruct (own_valid_2 with "H0 H1") as %->%to_agree_op_inv_L.
  auto.
Qed.

Definition disk_inv γ s (cs: circΣ.t) (dinit: disk) : iProp Σ :=
  ∃ installed_txn_id diskEnd_txn_id,
      "Hinstalled" ∷ is_installed γ s.(log_state.d) s.(log_state.txns) installed_txn_id diskEnd_txn_id ∗
      "Hdurable"   ∷ is_durable γ cs s.(log_state.txns) installed_txn_id diskEnd_txn_id ∗
      "#circ.start" ∷ is_installed_txn γ cs s.(log_state.txns) installed_txn_id s.(log_state.installed_lb) ∗
      "#circ.end"   ∷ is_durable_txn γ cs s.(log_state.txns) diskEnd_txn_id s.(log_state.durable_lb) ∗
      "%Hdaddrs_init" ∷ ⌜ ∀ a, is_Some (s.(log_state.d) !! a) ↔ is_Some (dinit !! a) ⌝ ∗
      "#Hbasedisk"  ∷ is_base_disk γ s.(log_state.d).

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
    "Hdisk" ∷ ∃ cs, "Howncs" ∷ ghost_var γ.(cs_name) (1/2) cs ∗ "Hdisk" ∷ disk_inv γ s cs dinit.

(* holds for log states which are possible after a crash (essentially these have
no mutable state) *)
Definition wal_post_crash σ: Prop :=
  S (σ.(log_state.durable_lb)) = length σ.(log_state.txns).

Definition is_wal_inner_durable γ s dinit : iProp Σ :=
    "%Hwf" ∷ ⌜wal_wf s⌝ ∗
    "%Hpostcrash" ∷ ⌜wal_post_crash s⌝ ∗
    "Htxns_ctx" ∷ txns_ctx γ s.(log_state.txns) ∗
    "γtxns"  ∷ ghost_var γ.(txns_name) (1/2) s.(log_state.txns) ∗
    "HnextDiskEnd_inv" ∷ nextDiskEnd_inv γ s.(log_state.txns) ∗
    "Hdisk" ∷ ∃ cs, "Hwal_linv" ∷ wal_linv_durable γ cs ∗
                    "Hdiskinv" ∷ disk_inv γ s cs dinit ∗
                    "Howncs" ∷ ghost_var γ.(cs_name) 1 cs ∗
                    "Hcirc" ∷ is_circular_state γ.(circ_name) cs
.

Definition is_wal (l : loc) γ (dinit : disk) : iProp Σ :=
  ncinv innerN (∃ σ, is_wal_inner l γ σ dinit ∗ P σ) ∗
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
  ∃ (installed_txn_id_mem being_installed_end_txn_id: nat),
    "HnotInstalling" ∷ thread_own γ.(start_avail_name) Available ∗
    "HownInstallerPos_installer" ∷ (∃ (installer_pos : nat), ghost_var γ.(installer_pos_name) (1/2) installer_pos) ∗
    "HownInstallerTxn_installer" ∷ (∃ (installer_txn_id : nat), ghost_var γ.(installer_txn_id_name) (1/2) installer_txn_id) ∗
    "HownInstallerPosMem_installer" ∷ (∃ (installer_pos_mem : u64), ghost_var γ.(installer_pos_mem_name) (1/2) installer_pos_mem) ∗
    "HownInstallerTxnMem_installer" ∷ (∃ (installer_txn_id_mem : nat), ghost_var γ.(installer_txn_id_mem_name) (1/2) installer_txn_id_mem) ∗
    "Halready_installed_installer" ∷ ghost_var γ.(already_installed_name) (1/2) (∅: gset Z) ∗
    "HownBeingInstalledStartTxn_installer" ∷ fmcounter γ.(being_installed_start_txn_name) (1/2) installed_txn_id_mem ∗
    "HownBeingInstalledEndTxn_installer" ∷ ghost_var γ.(being_installed_end_txn_name) (1/2) being_installed_end_txn_id ∗
    "#HdiskEndMem_lb_installer" ∷ fmcounter_lb γ.(diskEnd_mem_txn_id_name) being_installed_end_txn_id ∗
    "HownInstalledPosMem_installer" ∷ (∃ (installed_pos_mem : u64), ghost_var γ.(installed_pos_mem_name) (1/2) installed_pos_mem) ∗
    "HownInstalledTxnMem_installer" ∷ ghost_var γ.(installed_txn_id_mem_name) (1/2) installed_txn_id_mem
.

Global Instance is_installed_read_Timeless {d txns installed_lb diskEnd_txn_id being_installed_end_txn_id} :
  Timeless (is_installed_read d txns installed_lb diskEnd_txn_id being_installed_end_txn_id) := _.

(* this illustrates what crashes rely on; at crash time being_installed is
arbitrary, so we weaken to this *)
Theorem is_installed_weaken_read γ d txns installed_lb diskEnd_txn_id :
  is_installed γ d txns installed_lb diskEnd_txn_id -∗
  ∃ being_installed_end_txn_id,
    is_installed_read d txns installed_lb being_installed_end_txn_id diskEnd_txn_id.
Proof.
  rewrite /is_installed_read /is_installed.
  iIntros "I". iDestruct "I" as (??) "I". iExists _, _, _. iFrame.
Qed.

Theorem is_installed_restore_read γ d txns installed_txn_id diskEnd_txn_id being_installed_end_txn_id :
  fmcounter γ.(being_installed_start_txn_name) (1/2) installed_txn_id -∗
  ghost_var γ.(being_installed_end_txn_name) (1/2) being_installed_end_txn_id -∗
  ghost_var γ.(already_installed_name) (1/2) (∅: gset Z) -∗
  txns_are γ (S installed_txn_id) (subslice (S installed_txn_id) (S being_installed_end_txn_id) txns) -∗
  is_installed_read d txns installed_txn_id being_installed_end_txn_id diskEnd_txn_id -∗
  is_installed γ d txns installed_txn_id diskEnd_txn_id.
Proof.
  iIntros "HownBeingInstalledStartTxn HownBeingInstalledEndTxn Halready_installed Htxns Hinstalled_read".
  iNamed "Hinstalled_read".
  iExists _, _.
  iFrame "Halready_installed HownBeingInstalledStartTxn HownBeingInstalledEndTxn Htxns".
  iSplit.
  { iPureIntro. lia. }
  iApply (big_sepM_mono with "Hdata").
  iIntros (k x Hkx) "H".
  iDestruct "H" as (b txn_id') "(% & H & %)".
  iExists _, txn_id'. iFrame. iSplit; try done.
  iPureIntro. intuition eauto.
  set_solver.
Qed.

Theorem is_wal_read_mem l γ dinit : is_wal l γ dinit -∗ |NC={⊤}=> ▷ is_wal_mem l γ.
Proof.
  iIntros "#Hwal".
  iDestruct "Hwal" as "[Hinv _]".
  iApply (ncinv_dup_acc with "Hinv"); first by set_solver.
  iIntros "HinvI".
  iDestruct "HinvI" as (σ) "[HinvI HP]".
  iDestruct "HinvI" as "(%Hwf&#Hmem&Hrest)".
  iSplitL; last by auto.
  iExists _; iFrame.
  by iFrame "∗ Hmem".
Qed.

Theorem is_wal_open l wn dinit E :
  ↑innerN ⊆ E ->
  is_wal l wn dinit -∗
  |NC={E, E ∖ ↑innerN}=>
    ∃ σ, ▷ P σ ∗
    ( ▷ P σ -∗ |NC={E ∖ ↑innerN, E}=> emp ).
Proof.
  iIntros (HN) "[#? _]".
  iInv innerN as (σ) "[Hwalinner HP]" "Hclose".
  iModIntro.
  iExists _. iFrame.
  iIntros "HP".
  iApply "Hclose". iNext.
  iExists _. iFrame.
Qed.

Theorem is_circular_start_lb_agree E γ lb cs :
  ↑circN ⊆ E ->
  start_at_least γ.(circ_name) lb -∗
  is_circular circN (circular_pred γ) γ.(circ_name) -∗
  ghost_var γ.(cs_name) (1/2) cs -∗
  |NC={E}=> ⌜int.Z lb ≤ int.Z (circΣ.start cs)⌝ ∗ ghost_var γ.(cs_name) (1/2) cs.
Proof.
  rewrite /circular_pred.
  iIntros (Hsub) "#Hstart_lb #Hcirc Hown".
  iInv "Hcirc" as ">Hinner" "Hclose".
  iDestruct "Hinner" as (σ) "(Hstate&Hγ)".
  unify_ghost_var γ.(cs_name).
  iFrame "Hown".
  iDestruct (is_circular_state_pos_acc with "Hstate") as "([HdiskStart HdiskEnd]&Hstate)".
  iDestruct (start_is_agree_2 with "HdiskStart Hstart_lb") as %Hlb.
  iFrame (Hlb).
  iSpecialize ("Hstate" with "[$HdiskStart $HdiskEnd]").
  iApply "Hclose".
  iNext.
  iExists _; iFrame.
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
  |NC={⊤}=> ⌜is_txn txns txn_id pos⌝ ∗ ghost_var γ.(txns_name) (1/2) txns.
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

Theorem get_txns_are l γ dinit txns start till txns_sub :
  txns_sub = subslice start till txns →
  (start ≤ till ≤ length txns)%nat →
  ghost_var γ.(txns_name) (1/2) txns -∗
  is_wal l γ dinit -∗
  |NC={⊤}=> txns_are γ start txns_sub ∗ ghost_var γ.(txns_name) (1/2) txns.
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
  (* TODO(tej): this is a good example of bad [iFrame] performance: this iFrame
  needs to attempt to frame every hypothesis with the unfolded [wal_linv] in the goal, even though that never works;
  we'd like the wand to just not be subject to framing, but we also don't want to manually split the hypotheses.

  For example, wrapping the wand in [tc_opaque] makes this fast.
   *)
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
  int.Z pos1 < int.Z pos2 ->
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
  int.Z pos1 ≤ int.Z pos2.
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
  int.Z pos1 ≤ int.Z pos2 ->
  (txn_id1 ≤ txn_id2)%nat.
Proof.
  intros Hwf Htxn1 Htxn2 Hle.
  destruct (decide (pos1 = pos2)); subst.
  - apply Htxn2 in Htxn1; lia.
  - assert (txn_id1 < txn_id2)%nat; try lia.
    eapply wal_wf_txns_mono_pos; eauto.
    + eapply Htxn2.
    + assert (int.Z pos1 ≠ int.Z pos2).
      { intro H.
        assert (pos1 = pos2) by word; congruence. }
      lia.
Qed.

Lemma memLog_linv_pers_core_strengthen γ σ diskEnd diskEnd_txn_id nextDiskEnd_txn_id
      txns (logger_pos : u64) (logger_txn_id : nat) (installer_pos_mem : u64) (installer_txn_id_mem : nat) installed_txn_id_mem :
  int.Z installer_pos_mem ≤ int.Z diskEnd →
  memLog_linv_pers_core γ σ diskEnd diskEnd_txn_id installed_txn_id_mem nextDiskEnd_txn_id txns logger_pos logger_txn_id installer_pos_mem installer_txn_id_mem -∗
  ("Hsame_txns" ∷ ghost_var γ.(txns_name) (1/2) txns ∗
    "Hlp" ∷ ghost_var γ.(logger_pos_name) (1 / 2) logger_pos ∗
    "Hlt" ∷ ghost_var γ.(logger_txn_id_name) (1 / 2) logger_txn_id ∗
    "HownDiskEndMem" ∷ fmcounter γ.(diskEnd_mem_name) (1 / 2) (int.nat diskEnd) ∗
    "HownDiskEndMemTxn" ∷ fmcounter γ.(diskEnd_mem_txn_id_name) (1 / 2) diskEnd_txn_id ∗
    "Hip" ∷ ghost_var γ.(installer_pos_mem_name) (1 / 2) installer_pos_mem ∗
    "Hit" ∷ ghost_var γ.(installer_txn_id_mem_name) (1 / 2) installer_txn_id_mem ∗
    "HownInstalledPosMem" ∷ ghost_var γ.(installed_pos_mem_name) (1/2) σ.(slidingM.start) ∗
    "HownInstalledTxnMem" ∷ ghost_var γ.(installed_txn_id_mem_name) (1/2) installed_txn_id_mem ∗
    "Hnext" ∷ memLog_linv_nextDiskEnd_txn_id γ σ.(slidingM.mutable) nextDiskEnd_txn_id) -∗
  memLog_linv γ σ diskEnd diskEnd_txn_id.
Proof.
  intros Hinstall_diskEnd_order.
  iIntros "Hlinv_pers".
  iNamed 1.
  repeat iExists _.
  iFrame "Hlinv_pers".
  iFrame "∗ # %".
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

Lemma is_wal_alter `{!heapG Σ, !walG Σ} (P1 P2: log_state.t → iProp Σ) l γ dinit :
  is_wal P1 l γ dinit -∗
  □(∀ σ, P1 σ -∗ P2 σ ∗ (∀ σ', P2 σ' -∗ P1 σ')) -∗
  is_wal P2 l γ dinit.
Proof.
  iIntros "#Hwal #Himpl".
  iDestruct "Hwal" as "[Hinv $]".
  iApply (ncinv_alter with "Hinv").
  do 2 iModIntro.
  iDestruct 1 as (σ) "[Hinner HP]".
  iDestruct ("Himpl" with "HP") as "[HP2 HP1]".
  iSplitL "Hinner HP2"; first by eauto with iFrame.
  iDestruct 1 as (σ') "[Hinner HP2]".
  iExists _; iFrame.
  iApply ("HP1" with "[$]").
Qed.

Ltac destruct_is_wal :=
  iMod (is_wal_read_mem with "Hwal") as "#Hmem";
  wp_call;
  iNamed "Hmem"; iNamed "Hstfields".

Hint Unfold locked_wf : word.

Typeclasses Opaque is_base_disk.
