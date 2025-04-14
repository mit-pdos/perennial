From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.invariance Require Import prepare unprepare.
(* import for [local_gid_token] *)
From Perennial.program_proof.tulip.program.txn Require Import res.
(* for common definitions; TODO: factoring them out *)
From Perennial.program_proof.tulip.program.gcoord Require Import gpreparer_repr.

Inductive bgppphase :=
| BGPPInquiring
| BGPPValidating
| BGPPPreparing
| BGPPUnpreparing
| BGPPPrepared
| BGPPCommitted
| BGPPAborted
| BGPPStopped.

Definition bgppphase_to_u64 phase :=
  match phase with
  | BGPPInquiring => (W64 0)
  | BGPPValidating => (W64 1)
  | BGPPPreparing => (W64 2)
  | BGPPUnpreparing => (W64 3)
  | BGPPPrepared => (W64 4)
  | BGPPCommitted => (W64 5)
  | BGPPAborted => (W64 6)
  | BGPPStopped => (W64 7)
  end.

#[global]
Instance bgppphase_to_u64_inj :
  Inj eq eq bgppphase_to_u64.
Proof. intros x y H. by destruct x, y. Defined.

Definition bgpp_ready phase :=
  match phase with
  | BGPPInquiring => False
  | BGPPValidating => False
  | BGPPPreparing => False
  | BGPPUnpreparing => False
  | BGPPPrepared => True
  | BGPPCommitted => True
  | BGPPAborted => True
  | BGPPStopped => True
  end.

#[global]
Instance bgpp_ready_decision phase :
  Decision (bgpp_ready phase).
Proof. destruct phase; apply _. Defined.

Inductive bgppaction :=
| BGPPInquire
| BGPPValidate
| BGPPPrepare
| BGPPUnprepare
| BGPPRefresh.

Definition bgppaction_to_u64 action :=
  match action with
  | BGPPInquire => (W64 0)
  | BGPPValidate => (W64 1)
  | BGPPPrepare => (W64 2)
  | BGPPUnprepare => (W64 3)
  | BGPPRefresh => (W64 4)
  end.

#[global]
Instance bgppaction_to_u64_inj :
  Inj eq eq bgppaction_to_u64.
Proof. intros x y H. by destruct x, y. Defined.

Section bgpp_repr.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Definition safe_backup_gpreparer_phase γ ts gid rk phase : iProp Σ :=
    match phase with
    | BGPPInquiring => True
    | BGPPValidating => True
    | BGPPPreparing =>
        quorum_validated γ gid ts ∗ is_group_prepare_proposal γ gid ts rk true
    | BGPPUnpreparing => is_group_prepare_proposal γ gid ts rk false
    | BGPPPrepared =>
        quorum_prepared γ gid ts ∗ quorum_validated γ gid ts
    | BGPPCommitted => (∃ wrs, is_txn_committed γ ts wrs)
    | BGPPAborted => is_txn_aborted γ ts ∨ quorum_unprepared γ gid ts
    | BGPPStopped => True
    end.

  #[global]
  Instance safe_backup_gpreparer_phase_persistent γ ts gid rk phase :
    Persistent (safe_backup_gpreparer_phase γ ts gid rk phase).
  Proof. destruct phase; apply _. Defined.

  Definition safe_backup_gpreparer_action γ ts gid rk action : iProp Σ :=
    match action with
    | BGPPInquire => True
    | BGPPValidate => True
    | BGPPPrepare => is_group_prepare_proposal γ gid ts rk true
    | BGPPUnprepare => is_group_prepare_proposal γ gid ts rk false
    | BGPPRefresh => True
    end.

  #[global]
  Instance safe_backup_gpreparer_action_persistent γ ts gid rk action :
    Persistent (safe_backup_gpreparer_action γ ts gid rk action).
  Proof. destruct action; apply _. Defined.

  (*@ type BackupGroupPreparer struct {                                       @*)
  (*@     // Number of replicas. Read-only.                                   @*)
  (*@     nrps   uint64                                                       @*)
  (*@     // Control phase.                                                   @*)
  (*@     phase  uint64                                                       @*)
  (*@     // Buffered writes ready.                                           @*)
  (*@     pwrsok bool                                                         @*)
  (*@     // Buffered writes to this group.                                   @*)
  (*@     pwrs   map[string]tulip.Value                                       @*)
  (*@     // Latest prepare proposal on each replica.                         @*)
  (*@     pps    map[uint64]tulip.PrepareProposal                             @*)
  (*@     // Replicas that have validated.                                    @*)
  (*@     vdm    map[uint64]bool                                              @*)
  (*@     // Replicas that prepared/unprepared (depending on @phase).         @*)
  (*@     srespm map[uint64]bool                                              @*)
  (*@     //                                                                  @*)
  (*@     // TODO: Merge @vdm and @srespm.                                    @*)
  (*@     // @phase = INQUIRING / VALIDATING => records validated;            @*)
  (*@     // @phase = PREPARING / UNPREPARING => records prepared / unprepared. @*)
  (*@     // NB: The range doesn't need to be bool, unit would suffice.       @*)
  (*@     //                                                                  @*)
  (*@ }                                                                       @*)
  Definition own_backup_gpreparer_nrps (gpp : loc) : iProp Σ :=
    ∃ (nrps : u64),
      "Hnrps"   ∷ gpp ↦[BackupGroupPreparer :: "nrps"] #nrps ∗
      "%Hnrps"  ∷ ⌜uint.nat nrps = size rids_all⌝.

  Definition own_backup_gpreparer_phase (gpp : loc) (phase : bgppphase) : iProp Σ :=
    ∃ (phaseW : u64),
      "HphaseP" ∷ gpp ↦[BackupGroupPreparer :: "phase"] #phaseW ∗
      "%Hphase" ∷ ⌜bgppphase_to_u64 phase = phaseW⌝.

  Definition own_backup_gpreparer_pwrs (gpp : loc) ts gid γ : iProp Σ :=
    ∃ (pwrsok : bool) (pwrsP : loc) (pwrs : dbmap),
      "HpwrsokP"   ∷ gpp ↦[BackupGroupPreparer :: "pwrsok"] #pwrsok ∗
      "HpwrsP"     ∷ gpp ↦[BackupGroupPreparer :: "pwrs"] #pwrsP ∗
      "#Hpwrs"     ∷ (if pwrsok then own_map pwrsP DfracDiscarded pwrs else True) ∗
      "#Hsafepwrs" ∷ (if pwrsok then safe_txn_pwrs γ gid ts pwrs else True).

  Definition own_backup_gpreparer_pps (gpp : loc) : iProp Σ :=
    ∃ (ppsP : loc) (pps : gmap u64 ppsl),
      "HppsP" ∷ gpp ↦[BackupGroupPreparer :: "pps"] #ppsP ∗
      "Hpps"  ∷ own_map ppsP (DfracOwn 1) pps.

  Definition own_backup_gpreparer_vdm (gpp : loc) ts gid γ : iProp Σ :=
    ∃ (vdmP : loc) (vdm : gmap u64 bool),
      "HvdmP"   ∷ gpp ↦[BackupGroupPreparer :: "vdm"] #vdmP ∗
      "Hvdm"    ∷ own_map vdmP (DfracOwn 1) vdm ∗
      "#Hvds"   ∷ validation_responses γ ts gid vdm ∗
      "%Hvincl" ∷ ⌜dom vdm ⊆ rids_all⌝.

  Definition prepare_responses γ ts gid phase (srespm : gmap u64 bool) : iProp Σ :=
    match phase with
    | BGPPPreparing =>
        ([∗ set] rid ∈ dom srespm, is_replica_pdec_at_rank γ gid rid ts 1%nat true)
    | BGPPUnpreparing =>
        ([∗ set] rid ∈ dom srespm, is_replica_pdec_at_rank γ gid rid ts 1%nat false)
    | _ => True
    end.

  #[global]
  Instance prepare_responses_persistent γ ts gid phase srespm :
    Persistent (prepare_responses γ ts gid phase srespm).
  Proof. destruct phase; apply _. Defined.

  Definition own_backup_gpreparer_srespm
    (gpp : loc) (phase : bgppphase) ts gid γ : iProp Σ :=
    ∃ (srespmP : loc) (srespm : gmap u64 bool),
      "HsrespmP" ∷ gpp ↦[BackupGroupPreparer :: "srespm"] #srespmP ∗
      "Hsrespm"  ∷ own_map srespmP (DfracOwn 1) srespm ∗
      "#Hpreps"  ∷ prepare_responses γ ts gid phase srespm ∗
      "%Hsincl"  ∷ ⌜dom srespm ⊆ rids_all⌝.

  Definition own_backup_gpreparer_with_phase gpp phase rk ts gid γ : iProp Σ :=
    "Hnrps"   ∷ own_backup_gpreparer_nrps gpp ∗
    "Hphase"  ∷ own_backup_gpreparer_phase gpp phase ∗
    "Hpwrs"   ∷ own_backup_gpreparer_pwrs gpp ts gid γ ∗
    "Hpps"    ∷ own_backup_gpreparer_pps gpp ∗
    "Hvdm"    ∷ own_backup_gpreparer_vdm gpp ts gid γ ∗
    "Hsrespm" ∷ own_backup_gpreparer_srespm gpp phase ts gid γ ∗
    "#Hsafe"  ∷ safe_backup_gpreparer_phase γ ts gid rk phase.

  Definition own_backup_gpreparer gpp rk ts gid γ : iProp Σ :=
    ∃ (phase : bgppphase),
      "Hgpp" ∷ own_backup_gpreparer_with_phase gpp phase rk ts gid γ.

End bgpp_repr.

Section bgcoord_repr.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  (*@ type BackupGroupCoordinator struct {                                    @*)
  (*@     // Replica IDs in this group.                                       @*)
  (*@     rps       []uint64                                                  @*)
  (*@     // Replica addresses. Read-only.                                    @*)
  (*@     addrm     map[uint64]grove_ffi.Address                              @*)
  (*@     // Mutex protecting fields below.                                   @*)
  (*@     mu        *sync.Mutex                                               @*)
  (*@     // Condition variable used to notify arrival of responses.          @*)
  (*@     cv        *sync.Cond                                                @*)
  (*@     // The replica believed to be the leader of this group.             @*)
  (*@     idxleader uint64                                                    @*)
  (*@     // Group preparer.                                                  @*)
  (*@     gpp       *BackupGroupPreparer                                      @*)
  (*@     // Connections to replicas.                                         @*)
  (*@     conns     map[uint64]grove_ffi.Connection                           @*)
  (*@ }                                                                       @*)
  Definition own_backup_gcoord_gpreparer gcoord rk ts gid γ : iProp Σ :=
    ∃ (gppP : loc),
      "HgppP" ∷ gcoord ↦[BackupGroupCoordinator :: "gpp"] #gppP ∗
      "Hgpp"  ∷ own_backup_gpreparer gppP rk ts gid γ.

  Definition own_backup_gcoord_comm gcoord (addrm : gmap u64 chan) gid γ : iProp Σ :=
    ∃ (connsP : loc) (conns : gmap u64 (chan * chan)),
      let connsV := fmap (λ x, connection_socket x.1 x.2) conns in
      "HconnsP" ∷ gcoord ↦[BackupGroupCoordinator :: "conns"] #connsP ∗
      "Hconns"  ∷ map.own_map connsP (DfracOwn 1) (connsV, #()) ∗
      "#Htrmls" ∷ ([∗ map] x ∈ conns, is_terminal γ gid x.1) ∗
      "%Haddrm" ∷ ⌜map_Forall (λ rid x, addrm !! rid = Some x.2) conns⌝.

  Definition own_backup_gcoord gcoord addrm rk ts gid γ : iProp Σ :=
    "Hgpp"  ∷ own_backup_gcoord_gpreparer gcoord rk ts gid γ ∗
    "Hcomm" ∷ own_backup_gcoord_comm gcoord addrm gid γ.

  Definition is_backup_gcoord_addrm gcoord (addrm : gmap u64 chan) : iProp Σ :=
    ∃ (addrmP : loc) (rpsP : Slice.t) (rps : list u64),
      "#HaddrmP"   ∷ readonly (gcoord ↦[BackupGroupCoordinator :: "addrm"] #addrmP) ∗
      "#Haddrm"    ∷ own_map addrmP DfracDiscarded addrm ∗
      "#HrpsP"     ∷ readonly (gcoord ↦[BackupGroupCoordinator :: "rps"] (to_val rpsP)) ∗
      "#Hrps"      ∷ readonly (own_slice_small rpsP uint64T (DfracOwn 1) rps) ∗
      "%Hdomaddrm" ∷ ⌜dom addrm = list_to_set rps⌝ ∗
      (* right now [rps] is redundant since the set of replicas are fixed up
      front, but keeping it makes it easier to remove this constraint *)
      "%Hrps"      ∷ ⌜list_to_set rps = rids_all⌝ ∗
      "%Hnodup"    ∷ ⌜NoDup rps⌝.

  Definition is_backup_gcoord_with_addrm gcoord (addrm : gmap u64 chan) rk ts gid γ : iProp Σ :=
    ∃ (muP : loc) (cvP : loc),
      "#HmuP"    ∷ readonly (gcoord ↦[BackupGroupCoordinator :: "mu"] #muP) ∗
      "#Hlock"   ∷ is_lock tulipNS #muP (own_backup_gcoord gcoord addrm rk ts gid γ) ∗
      "#HcvP"    ∷ readonly (gcoord ↦[BackupGroupCoordinator :: "cv"] #cvP) ∗
      "#Hcv"     ∷ is_cond cvP #muP ∗
      "#Hinv"    ∷ know_tulip_inv γ ∗
      "#Hinvnet" ∷ know_tulip_network_inv γ gid addrm ∗
      "#Haddrm"  ∷ is_backup_gcoord_addrm gcoord addrm ∗
      "%Hgid"    ∷ ⌜gid ∈ gids_all⌝.

  Definition is_backup_gcoord gcoord rk ts gid γ : iProp Σ :=
    ∃ addrm, "Hgcoord" ∷ is_backup_gcoord_with_addrm gcoord addrm rk ts gid γ.

End bgcoord_repr.

Section btcoord_repr.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  (*@ type BackupTxnCoordinator struct {                                      @*)
  (*@     // Timestamp of the transaction this backup coordinator tries to finalize. @*)
  (*@     ts      uint64                                                      @*)
  (*@     // Ranks of this backup coordinator.                                @*)
  (*@     rank    uint64                                                      @*)
  (*@     // Participant groups.                                              @*)
  (*@     ptgs    []uint64                                                    @*)
  (*@     // Group coordinators, one for each participant group.              @*)
  (*@     gcoords map[uint64]*BackupGroupCoordinator                          @*)
  (*@     // Global prophecy variable (for verification purpose).             @*)
  (*@     proph   primitive.ProphId                                           @*)
  (*@ }                                                                       @*)
  Definition own_backup_tcoord_ts tcoord (ts : nat) : iProp Σ :=
    ∃ (tsW : u64),
      "HtsP"  ∷ tcoord ↦[BackupTxnCoordinator :: "ts"] #tsW ∗
      "%HtsW" ∷ ⌜uint.nat tsW = ts⌝.

  Definition own_backup_tcoord_rank tcoord (rk : nat) : iProp Σ :=
    ∃ (rkW : u64),
      "HrankP"  ∷ tcoord ↦[BackupTxnCoordinator :: "rank"] #rkW ∗
      "%HrkW" ∷ ⌜uint.nat rkW = rk⌝.

  Definition own_backup_tcoord_ptgs tcoord (ptgs : txnptgs) : iProp Σ :=
    ∃ (ptgsS : Slice.t) (ptgsL : list u64),
      "HptgsS"  ∷ tcoord ↦[BackupTxnCoordinator :: "ptgs"] (to_val ptgsS) ∗
      "#HptgsL" ∷ readonly (own_slice_small ptgsS uint64T (DfracOwn 1) ptgsL) ∗
      "%HptgsL" ∷ ⌜list_to_set ptgsL = ptgs⌝ ∗
      "%Hnd"    ∷ ⌜NoDup ptgsL⌝.

  Definition own_backup_tcoord_gcoords tcoord (ptgs : txnptgs) rk ts γ : iProp Σ :=
    ∃ (gcoordsP : loc) (gcoords : gmap u64 loc),
      "HgcoordsP"    ∷ tcoord ↦[BackupTxnCoordinator :: "gcoords"] #gcoordsP ∗
      "Hgcoords"     ∷ own_map gcoordsP (DfracOwn 1) gcoords ∗
      "#Hgcoordsabs" ∷ ([∗ map] gid ↦ gcoord ∈ gcoords, is_backup_gcoord gcoord rk ts gid γ) ∗
      "%Hdomgcoords" ∷ ⌜dom gcoords = ptgs⌝.

  Definition own_backup_tcoord (tcoord : loc) (ts : nat) (γ : tulip_names) : iProp Σ :=
    ∃ (rk : nat) (ptgs : txnptgs) (wrs : dbmap) (proph : proph_id),
      "Hts"      ∷ own_backup_tcoord_ts tcoord ts ∗
      "Hrank"    ∷ own_backup_tcoord_rank tcoord rk ∗
      "Hptgs"    ∷ own_backup_tcoord_ptgs tcoord ptgs ∗
      "Hgcoords" ∷ own_backup_tcoord_gcoords tcoord ptgs rk ts γ ∗
      "Hproph"   ∷ tcoord ↦[BackupTxnCoordinator :: "proph"] #proph ∗
      "#Hwrs"    ∷ is_txn_wrs γ ts wrs ∗
      "#Hinv"    ∷ know_tulip_inv_with_proph γ proph ∗
      "%Hvts"    ∷ ⌜valid_ts ts⌝ ∗
      "%Hvw"     ∷ ⌜valid_wrs wrs⌝ ∗
      "%Hptgs"   ∷ ⌜ptgs = ptgroups (dom wrs)⌝.

End btcoord_repr.

Section bgpreparer.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__ready (gpp : loc) phase :
    {{{ own_backup_gpreparer_phase gpp phase }}}
      BackupGroupPreparer__ready #gpp
    {{{ RET #(bool_decide (bgpp_ready phase)); own_backup_gpreparer_phase gpp phase }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) ready() bool {                          @*)
    (*@     return BGPP_PREPARED <= gpp.phase                                   @*)
    (*@ }                                                                       @*)
    iNamed "Hgpp".
    wp_loadField.
    wp_pures.
    rewrite /bgppphase_to_u64 in Hphase.
    rewrite /bgpp_ready.
    case_bool_decide as Hcond.
    { case_bool_decide as Hret.
      { iApply "HΦ". by iFrame. }
      destruct phase; word.
    }
    { case_bool_decide as Hret; last first.
      { iApply "HΦ". by iFrame. }
      destruct phase; word.
    }
  Qed.

  Theorem wp_BackupGroupPreparer__ready_external (gpp : loc) phase rk ts gid γ :
    {{{ own_backup_gpreparer_with_phase gpp phase rk ts gid γ }}}
      BackupGroupPreparer__ready #gpp
    {{{ RET #(bool_decide (bgpp_ready phase)); 
        own_backup_gpreparer_with_phase gpp phase rk ts gid γ
    }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    iNamed "Hgpp".
    wp_apply (wp_BackupGroupPreparer__ready with "Hphase").
    iIntros "Hphase".
    iApply "HΦ".
    by iFrame "∗ #".
  Qed.

  Theorem wp_BackupGroupPreparer__getPhase (gpp : loc) phase rk ts gid γ :
    {{{ own_backup_gpreparer_with_phase gpp phase rk ts gid γ }}}
      BackupGroupPreparer__getPhase #gpp
    {{{ RET #(bgppphase_to_u64 phase); 
        own_backup_gpreparer_with_phase gpp phase rk ts gid γ ∗
        safe_backup_gpreparer_phase γ ts gid rk phase
    }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) getPhase() uint64 {                     @*)
    (*@     return gpp.phase                                                    @*)
    (*@ }                                                                       @*)
    iNamed "Hgpp". iNamed "Hphase".
    wp_loadField.
    rewrite Hphase.
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

  (* A weak spec since its use is not related to safety *)
  Theorem wp_BackupGroupPreparer__finalized gpp rk ts gid γ :
    {{{ own_backup_gpreparer gpp rk ts gid γ }}}
      BackupGroupPreparer__finalized #gpp
    {{{ (finalized : bool), RET #finalized; own_backup_gpreparer gpp rk ts gid γ }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) finalized() bool {                      @*)
    (*@     return BGPP_COMMITTED <= gpp.phase                                  @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hgpp". iNamed "Hphase".
    wp_loadField.
    wp_pures.
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

  Theorem wp_BackupGroupPreparer__action (gpp : loc) (rid : u64) rk ts gid γ :
    {{{ own_backup_gpreparer gpp rk ts gid γ }}}
      BackupGroupPreparer__action #gpp #rid
    {{{ (action : bgppaction), RET #(bgppaction_to_u64 action); 
        own_backup_gpreparer gpp rk ts gid γ ∗
        safe_backup_gpreparer_action γ ts gid rk action
    }}}.
  Proof.
    (*@ func (gpp *BackupGroupPreparer) action(rid uint64) uint64 {             @*)
    (*@     // Inquire the transaction status on replica @rid.                  @*)
    (*@     if gpp.phase == BGPP_INQUIRING {                                    @*)
    (*@         // Check if the inquire response (i.e., latest proposal + validation @*)
    (*@         // status) for replica @rid is available.                       @*)
    (*@         _, inquired := gpp.pps[rid]                                     @*)
    (*@         if !inquired {                                                  @*)
    (*@             // Have not received the inquire response.                  @*)
    (*@             return BGPP_INQUIRE                                         @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    (*@         return BGPP_REFRESH                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     // Validate the transaction.                                        @*)
    (*@     if gpp.phase == BGPP_VALIDATING {                                   @*)
    (*@         // Check if the inquire response (i.e., latest proposal + validation @*)
    (*@         // status) for replica @rid is available.                       @*)
    (*@         _, inquired := gpp.pps[rid]                                     @*)
    (*@         if !inquired {                                                  @*)
    (*@             // Have not received inquire response.                      @*)
    (*@             return BGPP_INQUIRE                                         @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    (*@         // The inquire response is available. Now check if the transaction has @*)
    (*@         // been validated on replica @rid.                              @*)
    (*@         _, validated := gpp.vdm[rid]                                    @*)
    (*@         if !validated {                                                 @*)
    (*@             return BGPP_VALIDATE                                        @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    (*@         return BGPP_REFRESH                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     // Prepare the transaction.                                         @*)
    (*@     if gpp.phase == BGPP_PREPARING {                                    @*)
    (*@         _, prepared := gpp.srespm[rid]                                  @*)
    (*@         if !prepared {                                                  @*)
    (*@             return BGPP_PREPARE                                         @*)
    (*@         }                                                               @*)
    (*@         return BGPP_REFRESH                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     // Unprepare the transaction.                                       @*)
    (*@     if gpp.phase == BGPP_UNPREPARING {                                  @*)
    (*@         _, unprepared := gpp.srespm[rid]                                @*)
    (*@         if !unprepared {                                                @*)
    (*@             return BGPP_UNPREPARE                                       @*)
    (*@         }                                                               @*)
    (*@         return BGPP_REFRESH                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     return BGPP_REFRESH                                                 @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_BackupGroupPreparer__getPwrs (gpp : loc) rk ts gid γ :
    {{{ own_backup_gpreparer gpp rk ts gid γ }}}
      BackupGroupPreparer__getPwrs #gpp
    {{{ (pwrsP : loc) (pwrsok : bool), RET (#pwrsP, #pwrsok);
        own_backup_gpreparer gpp rk ts gid γ ∗
        if pwrsok
        then ∃ pwrs, own_map pwrsP DfracDiscarded pwrs ∗ safe_txn_pwrs γ gid ts pwrs
        else True
    }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) getPwrs() (tulip.KVMap, bool) {         @*)
    (*@     return gpp.pwrs, gpp.pwrsok                                         @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hgpp". iNamed "Hpwrs".
    do 2 wp_loadField.
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iFrame "∗ # %".
    destruct pwrsok; last done.
    by eauto.
  Qed.

End bgpreparer.

Section bgcoord.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupCoordinator__Finalized gcoord rk ts gid γ :
    is_backup_gcoord gcoord rk ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__Finalized #gcoord
    {{{ (finalized : bool), RET #finalized; True }}}.
  Proof.
    iIntros "#Hgcoord" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *BackupGroupCoordinator) Finalized() bool {                @*)
    (*@     gcoord.mu.Lock()                                                    @*)
    (*@     done := gcoord.gpp.finalized()                                      @*)
    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@     return done                                                         @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    iNamed "Hgcoord". iNamed "Hgpp".
    wp_loadField.
    wp_apply (wp_BackupGroupPreparer__finalized with "Hgpp").
    iIntros (finalized) "Hgpp".
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { by iFrame "Hlock Hlocked ∗". }
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_BackupGroupCoordinator__GetPwrs (gcoord : loc) rk ts gid γ :
    is_backup_gcoord gcoord rk ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__GetPwrs #gcoord
    {{{ (pwrsP : loc) (ok : bool), RET (#pwrsP, #ok); 
        if ok 
        then ∃ pwrs, own_map pwrsP DfracDiscarded pwrs ∗ safe_txn_pwrs γ gid ts pwrs
        else True
    }}}.
  Proof.
    iIntros "#Hgcoord" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *BackupGroupCoordinator) GetPwrs() (tulip.KVMap, bool) {   @*)
    (*@     gcoord.mu.Lock()                                                    @*)
    (*@     pwrs, ok := gcoord.gpp.getPwrs()                                    @*)
    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@     return pwrs, ok                                                     @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    iNamed "Hgcoord". iNamed "Hgpp".
    wp_loadField.
    wp_apply (wp_BackupGroupPreparer__getPwrs with "Hgpp").
    iIntros (pwrsP pwrsok) "[Hgpp #Hpwrs]".
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { by iFrame "Hlock Hlocked ∗". }
    wp_pures.
    iModIntro.
    by iApply "HΦ".
  Qed.

  Theorem wp_BackupGroupCoordinator__SendInquire
    (gcoord : loc) (rid : u64) (tsW : u64) (rankW : u64) addrm gid γ :
    let ts := uint.nat tsW in
    let rank := uint.nat rankW in
    rid ∈ dom addrm ->
    is_backup_gcoord_with_addrm gcoord addrm rank ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__SendInquire #gcoord #rid #tsW #rankW
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *BackupGroupCoordinator) SendInquire(rid, ts, rank uint64) { @*)
    (*@     data := message.EncodeTxnInquireRequest(ts, rank)                   @*)
    (*@     gcoord.Send(rid, data)                                              @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_BackupGroupCoordinator__SendValidate
    (gcoord : loc) (rid : u64) (tsW : u64) (rankW : u64) (pwrsP : loc) (ptgsP : Slice.t)
    q (pwrs : dbmap) (ptgs : txnptgs) addrm gid γ :
    let ts := uint.nat tsW in
    let rank := uint.nat rankW in
    rid ∈ dom addrm ->
    safe_txn_pwrs γ gid ts pwrs -∗
    is_txnptgs_in_slice ptgsP ptgs -∗
    is_backup_gcoord_with_addrm gcoord addrm rank ts gid γ -∗
    {{{ own_map pwrsP q pwrs }}}
      BackupGroupCoordinator__SendValidate #gcoord #rid #tsW #rankW #pwrsP (to_val ptgsP)
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *BackupGroupCoordinator) SendValidate(rid, ts, rank uint64, pwrs tulip.KVMap, ptgs []uint64) { @*)
    (*@     data := message.EncodeTxnValidateRequest(ts, rank, pwrs, ptgs)      @*)
    (*@     gcoord.Send(rid, data)                                              @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_BackupGroupCoordinator__SendPrepare
    (gcoord : loc) (rid : u64) (tsW : u64) (rankW : u64) addrm gid γ :
    let ts := uint.nat tsW in
    let rank := uint.nat rankW in
    rid ∈ dom addrm ->
    is_group_prepare_proposal γ gid ts rank true -∗
    is_backup_gcoord_with_addrm gcoord addrm rank ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__SendPrepare #gcoord #rid #tsW #rankW
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *BackupGroupCoordinator) SendPrepare(rid, ts, rank uint64) { @*)
    (*@     data := message.EncodeTxnPrepareRequest(ts, rank)                   @*)
    (*@     gcoord.Send(rid, data)                                              @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_BackupGroupCoordinator__SendUnprepare
    (gcoord : loc) (rid : u64) (tsW : u64) (rankW : u64) addrm gid γ :
    let ts := uint.nat tsW in
    let rank := uint.nat rankW in
    rid ∈ dom addrm ->
    is_group_prepare_proposal γ gid ts rank false -∗
    is_backup_gcoord_with_addrm gcoord addrm rank ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__SendUnprepare #gcoord #rid #tsW #rankW
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *BackupGroupCoordinator) SendUnprepare(rid, ts, rank uint64) { @*)
    (*@     data := message.EncodeTxnUnprepareRequest(ts, rank)                 @*)
    (*@     gcoord.Send(rid, data)                                              @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_BackupGroupCoordinator__SendRefresh
    (gcoord : loc) (rid : u64) (tsW : u64) (rankW : u64) addrm gid γ :
    let ts := uint.nat tsW in
    let rank := uint.nat rankW in
    rid ∈ dom addrm ->
    is_backup_gcoord_with_addrm gcoord addrm rank ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__SendRefresh #gcoord #rid #tsW #rankW
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (gcoord *BackupGroupCoordinator) SendRefresh(rid, ts, rank uint64) { @*)
    (*@     data := message.EncodeTxnRefreshRequest(ts, rank)                   @*)
    (*@     gcoord.Send(rid, data)                                              @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_BackupGroupCoordinator__NextPrepareAction gcoord (rid : u64) rk ts gid γ :
    is_backup_gcoord gcoord rk ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__NextPrepareAction #gcoord #rid
    {{{ (action : bgppaction), RET #(bgppaction_to_u64 action);
        safe_backup_gpreparer_action γ ts gid rk action
    }}}.
  Proof.
    iIntros "#Hgcoord" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *BackupGroupCoordinator) NextPrepareAction(rid uint64) uint64 { @*)
    (*@     gcoord.mu.Lock()                                                    @*)
    (*@     a := gcoord.gpp.action(rid)                                         @*)
    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@     return a                                                            @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    iNamed "Hgcoord". iNamed "Hgpp".
    wp_loadField.
    wp_apply (wp_BackupGroupPreparer__action with "Hgpp").
    iIntros (action) "[Hgpp #Hsafea]".
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { by iFrame "Hlock Hlocked ∗". }
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_BackupGroupCoordinator__PrepareSession
    (gcoord : loc) (rid : u64) (tsW : u64) (rkW : u64) (ptgsP : Slice.t)
    (ptgs : txnptgs) addrm gid γ :
    let ts := uint.nat tsW in
    let rk := uint.nat rkW in
    rid ∈ dom addrm ->
    is_txnptgs_in_slice ptgsP ptgs -∗
    is_backup_gcoord_with_addrm gcoord addrm rk ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__PrepareSession #gcoord #rid #tsW #rkW (to_val ptgsP)
    {{{ RET #(); True }}}.
  Proof.
    iIntros (ts rank Hrid) "#Hptgs #Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *BackupGroupCoordinator) PrepareSession(rid, ts, rank uint64, ptgs []uint64) { @*)
    (*@     for !gcoord.Finalized() {                                           @*)
    (*@                                                                         @*)
    wp_apply (wp_forBreak_cond (λ _, True)%I with "[] []"); last first; first 1 last.
    { done. }
    { clear Φ.
      iIntros (Φ) "!> _ HΦ".
      wp_apply (wp_BackupGroupCoordinator__Finalized with "[$Hgcoord]").
      iIntros (finalized) "_".
      destruct finalized eqn:Hfinalized; wp_pures.
      { by iApply "HΦ". }

      (*@         act := gcoord.NextPrepareAction(rid)                            @*)
      (*@                                                                         @*)
      wp_apply (wp_BackupGroupCoordinator__NextPrepareAction with "[$Hgcoord]").
      iIntros (act) "#Hsafea".
      wp_pures.

      (*@         if act == BGPP_INQUIRE {                                        @*)
      (*@             gcoord.SendInquire(rid, ts, rank)                           @*)
      (*@                                                                         @*)
      case_bool_decide as Hinquire; wp_pures.
      { wp_apply (wp_BackupGroupCoordinator__SendInquire with "Hgcoord").
        { apply Hrid. }
        wp_pures.
        by case_bool_decide; wp_pures; wp_apply wp_Sleep; wp_pures; iApply "HΦ".
      }

      (*@         } else if act == BGPP_VALIDATE {                                @*)
      (*@             pwrs, ok := gcoord.GetPwrs()                                @*)
      (*@             // The write set should be available in the VALIDATING phase; it @*)
      (*@             // should not require the check.                            @*)
      (*@             if ok {                                                     @*)
      (*@                 gcoord.SendValidate(rid, ts, rank, pwrs, ptgs)          @*)
      (*@             }                                                           @*)
      (*@                                                                         @*)
      case_bool_decide as Hvalidate; wp_pures.
      { wp_apply (wp_BackupGroupCoordinator__GetPwrs with "[$Hgcoord]").
        iIntros (pwrsP ok) "Hpwrs".
        wp_pures.
        destruct ok; wp_pures.
        { iDestruct "Hpwrs" as (pwrs) "[#Hpwrs #Hsafepwrs]".
          wp_apply (wp_BackupGroupCoordinator__SendValidate with "Hsafepwrs Hptgs Hgcoord Hpwrs").
          { apply Hrid. }
          wp_pures.
          by case_bool_decide; wp_pures; wp_apply wp_Sleep; wp_pures; iApply "HΦ".
        }
        by case_bool_decide; wp_pures; wp_apply wp_Sleep; wp_pures; iApply "HΦ".
      }

      (*@         } else if act == BGPP_PREPARE {                                 @*)
      (*@             gcoord.SendPrepare(rid, ts, rank)                           @*)
      (*@                                                                         @*)
      case_bool_decide as Hprepare; wp_pures.
      { destruct act; try done. simpl.
        wp_apply (wp_BackupGroupCoordinator__SendPrepare with "Hsafea Hgcoord").
        { apply Hrid. }
        wp_apply wp_Sleep.
        wp_pures.
        by iApply "HΦ".
      }

      (*@         } else if act == BGPP_UNPREPARE {                               @*)
      (*@             gcoord.SendUnprepare(rid, ts, rank)                         @*)
      (*@                                                                         @*)
      case_bool_decide as Hunprepare; wp_pures.
      { destruct act; try done. simpl.
        wp_apply (wp_BackupGroupCoordinator__SendUnprepare with "Hsafea Hgcoord").
        { apply Hrid. }
        wp_apply wp_Sleep.
        wp_pures.
        by iApply "HΦ".
      }

      (*@         } else if act == BGPP_REFRESH {                                 @*)
      (*@             gcoord.SendRefresh(rid, ts, rank)                           @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      case_bool_decide as Hrefresh; wp_pures.
      { wp_apply (wp_BackupGroupCoordinator__SendRefresh with "Hgcoord").
        { apply Hrid. }
        wp_pures.
        by case_bool_decide; wp_pures; wp_apply wp_Sleep; wp_pures; iApply "HΦ".
      }

      (*@         if act == BGPP_REFRESH {                                        @*)
      (*@             primitive.Sleep(params.NS_SEND_REFRESH)                     @*)
      (*@         } else {                                                        @*)
      (*@             // The optimal time to sleep is the time required to arrive at a @*)
      (*@             // prepare decision. Waking up too frequently means sending @*)
      (*@             // unnecessary messages, too infrequently means longer latency when @*)
      (*@             // messages are lost.                                       @*)
      (*@             //                                                          @*)
      (*@             // This might not be optimal for slow-path prepare. Consider @*)
      (*@             // optimize this with CV wait and timeout.                  @*)
      (*@             primitive.Sleep(params.NS_RESEND_PREPARE)                   @*)
      (*@         }                                                               @*)
      (*@     }                                                                   @*)
      (*@ }                                                                       @*)
      by case_bool_decide; wp_pures; wp_apply wp_Sleep; wp_pures; iApply "HΦ".
    }
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_BackupGroupCoordinator__WaitUntilPrepareDone gcoord rk ts gid γ :
    is_backup_gcoord gcoord rk ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__WaitUntilPrepareDone #gcoord
    {{{ (tphase : txnphase) (valid : bool), RET (#(txnphase_to_u64 tphase), #valid); 
        if valid then safe_group_txnphase γ ts gid tphase else True
    }}}.
  Proof.
    iIntros "#Hgcoord" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *BackupGroupCoordinator) WaitUntilPrepareDone() (uint64, bool) { @*)
    (*@     gcoord.mu.Lock()                                                    @*)
    (*@                                                                         @*)
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    wp_pures.
    iNamed "Hgcoord". do 2 iNamed "Hgpp".

    (*@     for !gcoord.gpp.ready() {                                           @*)
    (*@         gcoord.cv.Wait()                                                @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    set P := (λ (cont : bool), ∃ (phase' : bgppphase) (gppP' : loc),
                 "HgppP"   ∷ gcoord ↦[BackupGroupCoordinator::"gpp"] #gppP' ∗
                 "Hgpp"    ∷ own_backup_gpreparer_with_phase gppP' phase' rk ts gid γ ∗
                 "Hcomm"   ∷ own_backup_gcoord_comm gcoord addrm gid γ ∗
                 "Hlocked" ∷ locked #muP ∗
                 "%Hready" ∷ ⌜if cont then True else bgpp_ready phase'⌝)%I.
    wp_apply (wp_forBreak_cond P with "[] [HgppP Hgpp Hcomm Hlocked]"); last first; first 1 last.
    { by iFrame. }
    { clear Φ.
      iIntros (Φ) "!> HP HΦ".
      iNamed "HP".
      wp_loadField.
      wp_apply (wp_BackupGroupPreparer__ready_external with "Hgpp").
      iIntros "Hgpp".
      case_bool_decide as Hready'; wp_pures.
      { iApply "HΦ". by iFrame "∗ %". }
      wp_loadField.
      wp_apply (wp_Cond__Wait with "[-HΦ]").
      { by iFrame "Hlock Hcv ∗". }
      iIntros "[Hlocked Hgcoord]".
      wp_pures.
      iApply "HΦ".
      iNamed "Hgcoord". do 2 iNamed "Hgpp".
      by iFrame.
    }
    iNamed 1.
    clear phase gppP.
    rename phase' into phase. rename gppP' into gppP.

    (*@     phase := gcoord.gpp.getPhase()                                      @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_BackupGroupPreparer__getPhase with "Hgpp").
    iIntros "[Hgpp #Hsafep]".
    wp_pures.
    
    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { by iFrame "Hlock Hlocked ∗". }
    wp_pures.

    (*@     if phase == BGPP_STOPPED {                                          @*)
    (*@         // TXN_PREPARED here is just a placeholder.                     @*)
    (*@         return tulip.TXN_PREPARED, false                                @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Hstopped; wp_pures.
    { by iApply ("HΦ" $! TxnPrepared). }

    (*@     if phase == BGPP_COMMITTED {                                        @*)
    (*@         return tulip.TXN_COMMITTED, true                                @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Hcommitted; wp_pures.
    { iApply ("HΦ" $! TxnCommitted).
      by destruct phase.
    }

    (*@     if phase == BGPP_ABORTED {                                          @*)
    (*@         return tulip.TXN_ABORTED, true                                  @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Haborted; wp_pures.
    { iApply ("HΦ" $! TxnAborted).
      by destruct phase.
    }

    (*@     return tulip.TXN_PREPARED, true                                     @*)
    (*@ }                                                                       @*)
    iApply ("HΦ" $! TxnPrepared).
    by destruct phase.
  Qed.

  Theorem wp_BackupGroupCoordinator__Prepare
    (gcoord : loc) (tsW : u64) (rkW : u64) (ptgsP : Slice.t)
    (ptgs : txnptgs) gid γ :
    let ts := uint.nat tsW in
    let rk := uint.nat rkW in
    is_txnptgs_in_slice ptgsP ptgs -∗
    is_backup_gcoord gcoord rk ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__Prepare #gcoord #tsW #rkW (to_val ptgsP)
    {{{ (phase : txnphase) (valid : bool), RET (#(txnphase_to_u64 phase), #valid); 
        if valid then safe_group_txnphase γ ts gid phase else True
    }}}.
  Proof.
    iIntros (ts rk) "#Hptgs #Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *BackupGroupCoordinator) Prepare(ts, rank uint64, ptgs []uint64) (uint64, bool) { @*)
    (*@     // Spawn a session with each replica.                               @*)
    (*@     for ridloop := range(gcoord.addrm) {                                @*)
    (*@         rid := ridloop                                                  @*)
    (*@         go func() {                                                     @*)
    (*@             gcoord.PrepareSession(rid, ts, rank, ptgs)                  @*)
    (*@         }()                                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    do 2 iNamed "Hgcoord". iNamed "Haddrm".
    wp_loadField.
    wp_apply (wp_MapIter_fold _ _ _ (λ _, True)%I with "Haddrm []").
    { done. }
    { clear Φ.
      iIntros (mx rid c Φ) "!> [_ %Hrid] HΦ".
      destruct Hrid as [_ Hrid].
      wp_pures.
      iAssert (is_backup_gcoord_with_addrm gcoord addrm rk ts gid γ)%I as "#Hgcoord".
      { by iFrame "# %". }
      wp_apply wp_fork.
      { wp_apply (wp_BackupGroupCoordinator__PrepareSession with "Hptgs Hgcoord").
        { by apply elem_of_dom_2 in Hrid. }
        done.
      }
      by iApply "HΦ".
    }
    iIntros "_".

    (*@     status, valid := gcoord.WaitUntilPrepareDone()                      @*)
    (*@     return status, valid                                                @*)
    (*@ }                                                                       @*)
    wp_apply wp_BackupGroupCoordinator__WaitUntilPrepareDone.
    { by iFrame "# %". }
    iIntros (status valid) "#Hsafep".
    wp_pures.
    by iApply "HΦ".
  Qed.

End bgcoord.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupTxnCoordinator__stabilize tcoord ts γ :
    {{{ own_backup_tcoord tcoord ts γ }}}
      BackupTxnCoordinator__stabilize #tcoord
    {{{ (status : txnphase) (valid : bool), RET (#(txnphase_to_u64 status), #valid); 
        own_backup_tcoord tcoord ts γ ∗
        if valid then safe_txnphase γ ts status else True
    }}}.
  Proof.
    iIntros (Φ) "Htcoord HΦ".
    wp_rec.

    (*@ func (tcoord *BackupTxnCoordinator) stabilize() (uint64, bool) {        @*)
    (*@     ts := tcoord.ts                                                     @*)
    (*@     rank := tcoord.rank                                                 @*)
    (*@     ptgs := tcoord.ptgs                                                 @*)
    (*@                                                                         @*)
    iNamed "Htcoord". iNamed "Hts". iNamed "Hrank". iNamed "Hptgs".
    do 3 wp_loadField.

    (*@     mu := new(sync.Mutex)                                               @*)
    (*@     cv := sync.NewCond(mu)                                              @*)
    (*@     // Number of groups that have responded (i.e., groups whose prepare status @*)
    (*@     // is determined).                                                  @*)
    (*@     var nr uint64 = 0                                                   @*)
    (*@     // Number of groups that have prepared.                             @*)
    (*@     var np uint64 = 0                                                   @*)
    (*@     var st uint64 = tulip.TXN_PREPARED                                  @*)
    (*@     var vd bool = true                                                  @*)
    (*@                                                                         @*)
    wp_apply wp_new_free_lock.
    iIntros (muP) "Hfree".
    wp_apply (wp_newCond' with "Hfree").
    iIntros (cvP) "[Hfree #Hcv]".
    wp_apply wp_ref_to; first by auto.
    iIntros (nrP) "HnrP".
    wp_apply wp_ref_to; first by auto.
    iIntros (npP) "HnpP".
    wp_apply wp_ref_to; first by auto.
    iIntros (stP) "HstP".
    wp_apply wp_ref_to; first by auto.
    iIntros (vdP) "HvdP".
    wp_pures.
    (* Allocate exclusive tokens to prove freshness of response. *)
    iApply fupd_wp.
    iMod (local_gid_tokens_alloc ptgs) as (α) "Htks".
    iModIntro.
    (* Establish the lock invariant. *)
    set I := (∃ (np nr : u64) (st : txnphase) (vd : bool) (gids : gset u64),
                 let allprep := vd && bool_decide (st = TxnPrepared) in
                 "HnpP" ∷ npP ↦[uint64T] #np ∗
                 "HnrP" ∷ nrP ↦[uint64T] #nr ∗
                 "HstP" ∷ stP ↦[uint64T] #(txnphase_to_u64 st) ∗
                 "HvdP" ∷ vdP ↦[boolT] #vd ∗
                 "Htks" ∷ ([∗ set] gid ∈ gids, local_gid_token α gid) ∗
                 "#Hst" ∷ (match st with
                           | TxnPrepared => [∗ set] gid ∈ gids, is_group_prepared γ gid ts
                           | TxnCommitted => (∃ wrs, is_txn_committed γ ts wrs)
                           | TxnAborted => is_txn_aborted γ ts
                           end) ∗
                 "%Hgidsincl" ∷ ⌜gids ⊆ ptgs⌝ ∗
                 "%Hsizegids" ∷ ⌜size gids = uint.nat np⌝ ∗
                 "%Hnpnr"     ∷ ⌜if allprep then np = nr else True⌝)%I.
    iApply fupd_wp.
    iMod (alloc_lock tulipNS _ _ I with "Hfree [HnpP HnrP HstP HvdP]") as "#Hmu".
    { iModIntro.
      iExists (W64 0), (W64 0), TxnPrepared, true, ∅.
      iFrame.
      iSplit; first by iApply big_sepS_empty.
      iSplit; first by iApply big_sepS_empty.
      iPureIntro.
      case_bool_decide; done.
    }
    iModIntro.

    (*@     for _, gid := range(ptgs) {                                         @*)
    (*@                                                                         @*)
    set P := (λ (i : u64),
                "Hgcoords" ∷ own_backup_tcoord_gcoords tcoord ptgs rk ts γ ∗
                "Htks" ∷ [∗ set] gid ∈ list_to_set (drop (uint.nat i) ptgsL), local_gid_token α gid)%I.
    iMod (readonly_load with "HptgsL") as (q) "HptgsL'".
    iDestruct (own_slice_small_sz with "HptgsL'") as %Hlenptgs.
    wp_apply (wp_forSlice P with "[] [$HptgsL' $Hgcoords Htks]"); last first; first 1 last.
    { by rewrite uint_nat_W64_0 drop_0 HptgsL. }
    { clear Φ.

      (*@         gcoord := tcoord.gcoords[gid]                                   @*)
      (*@                                                                         @*)
      iIntros (i gid Φ) "!> (HP & %Hinbound & %Hgid) HΦ".
      iNamed "HP". iNamed "Hgcoords".
      wp_loadField.
      assert (Hinptgs : gid ∈ ptgs).
      { apply elem_of_list_lookup_2 in Hgid.
        clear -Hgid HptgsL.
        set_solver.
      }
      assert (Hin : gid ∈ gids_all).
      { pose proof (subseteq_ptgroups (dom wrs)) as Hdom.
        clear -Hdom Hinptgs Hptgs.
        set_solver.
      }
      wp_apply (wp_MapGet with "Hgcoords").
      iIntros (gcoordP ok) "[%Hgetgcoords Hgcoords]".
      destruct ok; last first.
      { apply map_get_false in Hgetgcoords as [Hnone _].
        by rewrite -not_elem_of_dom Hdomgcoords in Hnone.
      }
      apply map_get_true in Hgetgcoords.

      (*@         go func() {                                                     @*)
      (*@                                                                         @*)
      iDestruct (big_sepM_lookup with "Hgcoordsabs") as "Hgcoordabs"; first apply Hgetgcoords.
      rewrite (drop_S _ _ _ Hgid) list_to_set_cons big_sepS_insert; last first.
      { rewrite not_elem_of_list_to_set. intros Hgidin.
        clear -Hgid Hgidin Hnd.
        rewrite -(take_drop_middle _ _ _ Hgid) in Hnd.
        apply NoDup_app in Hnd as (_ & _ & Hnd).
        by apply NoDup_cons in Hnd as [? _].
      }
      iDestruct "Htks" as "[Htk Htks]".
      wp_apply (wp_fork with "[Htk]").
      { (* Forked thread. *)

        (*@             stg, vdg := gcoord.Prepare(ts, rank, ptgs)                  @*)
        (*@                                                                         @*)
        iModIntro.
        wp_apply (wp_BackupGroupCoordinator__Prepare).
        { by iFrame "# %". }
        { by rewrite HtsW HrkW. }
        iIntros (stg vdg) "#Hsafe".
        wp_pures.
        iAssert (∃ pwrs, safe_txn_pwrs γ gid ts pwrs)%I as "#Hsafepwrs".
        { iExists (wrs_group gid wrs).
          iFrame "Hwrs".
          iPureIntro.
          unshelve epose proof (elem_of_ptgroups_non_empty gid wrs _) as Hne.
          { by rewrite -Hptgs. }
          done.
        }

        (*@             mu.Lock()                                                   @*)
        (*@             nr += 1                                                     @*)
        (*@             if !vdg {                                                   @*)
        (*@                 vd = false                                              @*)
        (*@             } else if stg == tulip.TXN_PREPARED {                       @*)
        (*@                 np += 1                                                 @*)
        (*@             } else {                                                    @*)
        (*@                 st = stg                                                @*)
        (*@             }                                                           @*)
        (*@             mu.Unlock()                                                 @*)
        (*@             cv.Signal()                                                 @*)
        (*@         }()                                                             @*)
        (*@     }                                                                   @*)
        (*@                                                                         @*)
        wp_apply (wp_Mutex__Lock with "Hmu").
        iIntros "[Hlocked HI]".
        iNamed "HI".
        wp_load. wp_store.
        destruct vdg; wp_pures; last first.
        { (* Case: [vdg = false]. *)
          wp_store.
          wp_apply (wp_Mutex__Unlock with "[-]").
          { iFrame "Hmu Hlocked HnpP HnrP HstP HvdP".
            iModIntro.
            iFrame "∗ # %".
          }
          wp_pures.
          by wp_apply (wp_Cond__Signal with "Hcv").
        }
        rewrite HtsW.
        destruct stg eqn:Hstg; wp_pures.
        { (* Case: [TxnPrepared] *)
          wp_load. wp_store.
          iAssert (|={⊤}=> is_group_prepared γ gid ts)%I as "Hprepared".
          { iInv "Hinv" as "> HinvO" "HinvC".
            iNamed "HinvO".
            iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]".
            { apply Hin. }
            iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]".
            { apply Hin. }
            iDestruct "Hsafe" as "[Hqp Hqv]".
            iDestruct "Hsafepwrs" as (pwrs) "Hsafepwrs".
            iMod (group_inv_prepare with "Hqv Hqp Hsafepwrs Htxnsys Hkeys Hrg Hgroup")
              as "(Htxnsys & Hkeys & Hrg & Hgroup & #Hprepared)".
            iDestruct ("HrgsC" with "Hrg") as "Hrgs".
            iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
            by iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
          }
          iMod "Hprepared" as "#Hprepared".
          wp_apply (wp_Mutex__Unlock with "[-]").
          { iFrame "Hmu Hlocked HnpP HnrP HstP HvdP".
            iModIntro.
            iAssert (⌜gid ∉ gids⌝)%I as %Hnotin.
            { iIntros (Hgidin).
              iDestruct (big_sepS_elem_of with "Htks") as "Htk'"; first apply Hgidin.
              by iDestruct (local_gid_token_ne with "Htk Htk'") as %?.
            }
            iExists ({[gid]} ∪ gids).
            iSplitL "Htk Htks".
            { iApply (big_sepS_insert_2 with "Htk Htks"). }
            iSplit.
            { destruct st; [| done | done].
              by iApply big_sepS_insert_2.
            }
            iPureIntro.
            { split.
              { clear -Hgidsincl Hinptgs. set_solver. }
              split.
              { rewrite size_union; last set_solver.
                rewrite size_singleton Hsizegids.
                assert (Hszgids : (size gids ≤ size gids_all)%nat).
                { apply subseteq_size. etrans; first apply Hgidsincl.
                  rewrite Hptgs.
                  apply subseteq_ptgroups.
                }
                pose proof size_gids_all as Hszgidsall.
                clear -Hszgids Hszgidsall Hsizegids. word.
              }
              set b := _ && _ in Hnpnr *.
              by destruct b; first rewrite Hnpnr.
            }
          }
          by wp_apply (wp_Cond__Signal with "Hcv").
        }
        { (* Case [TxnCommitted]. *)
          wp_store.
          wp_apply (wp_Mutex__Unlock with "[-]").
          { iFrame "Hmu Hlocked ∗".
            iModIntro.
            iExists TxnCommitted.
            iFrame "∗ #".
            iPureIntro.
            do 2 (split; first done).
            by rewrite bool_decide_eq_false_2; [rewrite andb_false_r |].
          }
          by wp_apply (wp_Cond__Signal with "Hcv").
        }
        { (* Case [TxnAborted]. *)
          wp_store.
          iAssert (|={⊤}=> is_txn_aborted γ ts)%I as "Habted".
          { iDestruct "Hsafe" as "[? | Hsafe]"; first done.
            iInv "Hinv" as "> HinvO" "HinvC".
            iNamed "HinvO".
            iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]".
            { apply Hin. }
            iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]".
            { apply Hin. }
            iDestruct "Hsafepwrs" as (pwrs) "Hsafepwrs".
            iMod (txnsys_group_inv_unprepare with "Hsafe Hsafepwrs Hrg Hgroup Htxnsys")
              as "(Hrg & Hgroup & Htxnsys & #Habted)".
            iDestruct ("HrgsC" with "Hrg") as "Hrgs".
            iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
            iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
            done.
          }
          iMod "Habted" as "#Habted".
          wp_apply (wp_Mutex__Unlock with "[-]").
          { iFrame "Hmu Hlocked ∗".
            iModIntro.
            iExists TxnAborted.
            iFrame "∗ #".
            iPureIntro.
            do 2 (split; first done).
            by rewrite bool_decide_eq_false_2; [rewrite andb_false_r |].
          }
          by wp_apply (wp_Cond__Signal with "Hcv").
        }
      }
      iApply "HΦ".
      iFrame "∗ # %".
      rewrite uint_nat_word_add_S; last first.
      { clear -Hinbound. word. }
      done.
    }
    iIntros "[HP _]".
    subst P. iNamed "HP".

    (*@     // Wait until either a higher-ranked coordinator is found (i.e., as @*)
    (*@     // indicated by @valid = false), or all participant groups have responded. @*)
    (*@     //                                                                  @*)
    (*@     // A note on the difference between this method and @txn.preapre. Unlike @*)
    (*@     // @txn.prepare() where it's OK (and good for performance) to terminate this @*)
    (*@     // phase once the transaction status is determined, the backup txn  @*)
    (*@     // coordinator should wait until it finds out the status of all participant @*)
    (*@     // groups to finalize the transaction outcome for every group.      @*)
    (*@     mu.Lock()                                                           @*)
    (*@                                                                         @*)
    wp_apply (wp_Mutex__Lock with "Hmu").
    iIntros "[Hlocked HI]".
    wp_pures.

    (*@     for vd && nr != uint64(len(ptgs)) {                                 @*)
    (*@         cv.Wait()                                                       @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (* Different from [I] in [Hlocked] and [Hcond]. *)
    set P := (λ cont : bool,
                ∃ (np nr : u64) (st : txnphase) (vd : bool) (gids : gset u64),
                  let allprep := vd && bool_decide (st = TxnPrepared) in
                  "HnpP" ∷ npP ↦[uint64T] #np ∗
                  "HnrP" ∷ nrP ↦[uint64T] #nr ∗
                  "HstP" ∷ stP ↦[uint64T] #(txnphase_to_u64 st) ∗
                  "HvdP" ∷ vdP ↦[boolT] #vd ∗
                  "Htks" ∷ ([∗ set] gid ∈ gids, local_gid_token α gid) ∗
                  "Hlocked" ∷ locked #muP ∗
                  "#Hst" ∷ (match st with
                            | TxnPrepared => [∗ set] gid ∈ gids, is_group_prepared γ gid ts
                            | TxnCommitted => (∃ wrs, is_txn_committed γ ts wrs)
                            | TxnAborted => is_txn_aborted γ ts
                            end) ∗
                  "%Hgidsincl" ∷ ⌜gids ⊆ ptgs⌝ ∗
                  "%Hsizegids" ∷ ⌜size gids = uint.nat np⌝ ∗
                  "%Hnpnr"     ∷ ⌜(if allprep then np = nr else True)⌝ ∗
                  "%Hcond"     ∷ ⌜(if cont
                                   then True
                                   else vd = false ∨ uint.nat nr = length ptgsL)⌝)%I.
    wp_apply (wp_forBreak_cond P with "[] [Hlocked HI]"); last first; first 1 last.
    { iNamed "HI". iFrame "∗ # %". }
    { clear Φ.
      iIntros (Φ) "!> HP HΦ".
      iNamed "HP".
      wp_load.
      destruct vd eqn:Hvd; wp_pures.
      { wp_load.
        wp_apply wp_slice_len.
        wp_pures.
        set c := bool_decide _.
        destruct c eqn:Hsize; wp_pures.
        { iApply "HΦ".
          iFrame "∗ # %".
          iPureIntro.
          right.
          rewrite bool_decide_eq_true in Hsize.
          inv Hsize.
          clear -Hlenptgs. done.
        }
        wp_apply (wp_Cond__Wait with "[-HΦ]").
        { by iFrame "Hcv Hmu Hlocked ∗ # %". }
        iIntros "[Hlocked HI]".
        wp_pures.
        iApply "HΦ".
        iClear "Hst".
        iNamed "HI".
        by iFrame "∗ # %".
      }
      iApply "HΦ".
      iFrame "∗ # %".
      iPureIntro.
      by left.
    }
    iClear "Htks".
    iNamed 1.

    (*@     // Use the invariant saying that "if @st = TXN_PREPARED, then @np = @nr" to @*)
    (*@     // establish the postcondition.                                     @*)
    (*@                                                                         @*)
    (*@     status := st                                                        @*)
    (*@     valid := vd                                                         @*)
    (*@     mu.Unlock()                                                         @*)
    (*@                                                                         @*)
    do 2 wp_load.
    wp_apply (wp_Mutex__Unlock with "[Hlocked HnpP HnrP HstP HvdP Htks]").
    { by iFrame "Hmu Hlocked ∗ # %". }

    (*@     return status, valid                                                @*)
    (*@ }                                                                       @*)
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iFrame "∗ # %".
    destruct vd; last done.
    destruct st; [| done | done].
    iFrame "Hwrs".
    assert (gids = ptgroups (dom wrs)) as ->; last done.
    destruct Hcond as [Hcontra | Hnr]; first done.
    rewrite /= bool_decide_eq_true_2 in Hnpnr; last done. subst nr.
    rewrite -Hptgs.
    apply set_subseteq_size_eq; first apply Hgidsincl.
    rewrite -HptgsL size_list_to_set; last apply Hnd.
    clear -Hsizegids Hnr. lia.
  Qed.

  Theorem wp_BackupTxnCoordinator__abort tcoord ts γ :
    is_txn_aborted γ ts -∗
    {{{ own_backup_tcoord tcoord ts γ }}}
      BackupTxnCoordinator__abort #tcoord
    {{{ RET #(); own_backup_tcoord tcoord ts γ }}}.
  Proof.
    (*@ func (tcoord *BackupTxnCoordinator) abort() {                           @*)
    (*@     for _, gcoordloop := range(tcoord.gcoords) {                        @*)
    (*@         gcoord := gcoordloop                                            @*)
    (*@         go func() {                                                     @*)
    (*@             gcoord.Abort(tcoord.ts)                                     @*)
    (*@         }()                                                             @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_BackupTxnCoordinator__resolve tcoord status ts γ :
    status ≠ TxnAborted ->
    {{{ own_backup_tcoord tcoord ts γ }}}
      BackupTxnCoordinator__resolve #tcoord #(txnphase_to_u64 status)
    {{{ RET #(); own_backup_tcoord tcoord ts γ ∗ is_txn_committed_ex γ ts }}}.
  Proof.
    (*@ func (tcoord *BackupTxnCoordinator) resolve(status uint64) {            @*)
    (*@     if status == tulip.TXN_PREPARED {                                   @*)
    (*@         // Logical action: Commit.                                      @*)
    (*@         trusted_proph.ResolveCommit(tcoord.proph, tcoord.ts, tcoord.mergeWrites()) @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_BackupTxnCoordinator__commit tcoord ts γ :
    is_txn_committed_ex γ ts -∗
    {{{ own_backup_tcoord tcoord ts γ }}}
      BackupTxnCoordinator__commit #tcoord
    {{{ RET #(); own_backup_tcoord tcoord ts γ }}}.
  Proof.
    (*@ func (tcoord *BackupTxnCoordinator) commit() {                          @*)
    (*@     for _, gcoordloop := range(tcoord.gcoords) {                        @*)
    (*@         gcoord := gcoordloop                                            @*)
    (*@         go func() {                                                     @*)
    (*@             gcoord.Commit(tcoord.ts)                                    @*)
    (*@         }()                                                             @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_BackupTxnCoordinator__Finalize tcoord ts γ :
    {{{ own_backup_tcoord tcoord ts γ }}}
      BackupTxnCoordinator__Finalize #tcoord
    {{{ RET #(); own_backup_tcoord tcoord ts γ }}}.
  Proof.
    iIntros (Φ) "Htcoord HΦ".
    wp_rec.

    (*@ func (tcoord *BackupTxnCoordinator) Finalize() {                        @*)
    (*@     status, valid := tcoord.stabilize()                                 @*)
    (*@                                                                         @*)
    wp_apply (wp_BackupTxnCoordinator__stabilize with "Htcoord").
    iIntros (status valid) "[Htcoord Hphase]".
    wp_pures.

    (*@     if !valid {                                                         @*)
    (*@         // Skip since a more recent backup txn coordinator is found.    @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    destruct valid eqn:Hvalid; wp_pures; last first.
    { by iApply "HΦ". }

    (*@     if status == tulip.TXN_ABORTED {                                    @*)
    (*@         tcoord.abort()                                                  @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Hcond; wp_pures.
    { destruct status eqn:Hstatus; [done | done | ].
      simpl.
      wp_apply (wp_BackupTxnCoordinator__abort with "Hphase Htcoord").
      iIntros "Htcoord".
      wp_pures.
      by iApply "HΦ".
    }

    (*@     // Possible @status: TXN_PREPARED and TXN_COMMITTED. Resolve the prophecy @*)
    (*@     // variable if @status == TXN_PREPARED.                             @*)
    (*@     tcoord.resolve(status)                                              @*)
    (*@                                                                         @*)
    wp_apply (wp_BackupTxnCoordinator__resolve with "Htcoord").
    { by destruct status. }
    iIntros "[Htcoord #Hcmted]".

    (*@     tcoord.commit()                                                     @*)
    (*@ }                                                                       @*)
    wp_apply (wp_BackupTxnCoordinator__commit with "Hcmted Htcoord").
    iIntros "Htcoord".
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
