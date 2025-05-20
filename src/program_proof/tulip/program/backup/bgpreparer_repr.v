(* for common definitions; TODO: factoring them out *)
From Perennial.program_proof.tulip.program.gcoord Require Import gpreparer_repr.
From Perennial.program_proof.tulip.program Require Import prelude.

Inductive bgppphase :=
| BGPPInquiring
| BGPPValidating
| BGPPPreparing
| BGPPUnpreparing
| BGPPPrepared
| BGPPCommitted
| BGPPAborted
| BGPPStopped.

#[global]
Instance bgppphase_eq_decision :
  EqDecision bgppphase.
Proof. solve_decision. Qed.

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

Section repr.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Definition safe_backup_gpreparer_phase γ ts cid gid rk phase : iProp Σ :=
    match phase with
    | BGPPInquiring => True
    | BGPPValidating =>
        safe_proposal γ gid ts rk true ∗ quorum_voted γ gid ts rk cid
    | BGPPPreparing => is_group_prepare_proposal γ gid ts rk true
    | BGPPUnpreparing => is_group_prepare_proposal γ gid ts rk false
    | BGPPPrepared =>
        quorum_prepared γ gid ts ∗ quorum_validated γ gid ts
    | BGPPCommitted => (∃ wrs, is_txn_committed γ ts wrs)
    | BGPPAborted => is_txn_aborted γ ts ∨ quorum_unprepared γ gid ts
    | BGPPStopped => True
    end.

  #[global]
  Instance safe_backup_gpreparer_phase_persistent γ ts cid gid rk phase :
    Persistent (safe_backup_gpreparer_phase γ ts cid gid rk phase).
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

  Definition own_backup_gpreparer_pps
    (gpp : loc) (pps : gmap u64 ppsl) rk ts cid gid γ : iProp Σ :=
    ∃ (ppsP : loc) (blts : gmap u64 ballot),
      let n := latest_before_quorum rk blts in
      "HppsP"    ∷ gpp ↦[BackupGroupPreparer :: "pps"] #ppsP ∗
      "Hpps"     ∷ own_map ppsP (DfracOwn 1) pps ∗
      "#Hblts"   ∷ ([∗ map] rid ↦ blt ∈ blts, is_replica_ballot_lb γ gid rid ts blt) ∗
      "#Hpsl"    ∷ ([∗ map] pp ∈ pps,
                      is_group_prepare_proposal_if_classic γ gid ts (uint.nat pp.1) pp.2) ∗
      "#Hvotes"  ∷ ([∗ set] rid ∈ dom pps, is_replica_backup_vote γ gid rid ts rk cid) ∗
      "%Hdompps" ∷ ⌜dom pps ⊆ rids_all⌝ ∗
      "%Hlen"    ∷ ⌜map_Forall (λ _ l, (rk = length l)%nat) blts⌝ ∗
      "%Hblts"   ∷ ⌜map_Forall2 (λ k pp blt, latest_term blt = uint.nat pp.1 ∧
                                             blt !! uint.nat pp.1 = Some (Accept pp.2)) pps blts⌝.

  Definition own_backup_gpreparer_vdm (gpp : loc) ts gid γ : iProp Σ :=
    ∃ (vdmP : loc) (vdm : gmap u64 bool),
      "HvdmP"   ∷ gpp ↦[BackupGroupPreparer :: "vdm"] #vdmP ∗
      "Hvdm"    ∷ own_map vdmP (DfracOwn 1) vdm ∗
      "#Hvds"   ∷ validation_responses γ ts gid vdm ∗
      "%Hvincl" ∷ ⌜dom vdm ⊆ rids_all⌝.

  Definition prepare_responses γ rk ts gid phase (srespm : gmap u64 bool) : iProp Σ :=
    match phase with
    | BGPPPreparing =>
        ([∗ set] rid ∈ dom srespm, is_replica_pdec_at_rank γ gid rid ts rk true)
    | BGPPUnpreparing =>
        ([∗ set] rid ∈ dom srespm, is_replica_pdec_at_rank γ gid rid ts rk false)
    | _ => True
    end.

  #[global]
  Instance prepare_responses_persistent γ rk ts gid phase srespm :
    Persistent (prepare_responses γ rk ts gid phase srespm).
  Proof. destruct phase; apply _. Defined.

  Definition own_backup_gpreparer_srespm
    (gpp : loc) (phase : bgppphase) rk ts gid γ : iProp Σ :=
    ∃ (srespmP : loc) (srespm : gmap u64 bool),
      "HsrespmP" ∷ gpp ↦[BackupGroupPreparer :: "srespm"] #srespmP ∗
      "Hsrespm"  ∷ own_map srespmP (DfracOwn 1) srespm ∗
      "#Hpreps"  ∷ prepare_responses γ rk ts gid phase srespm ∗
      "%Hsincl"  ∷ ⌜dom srespm ⊆ rids_all⌝.

  Definition accepting_phase phase :=
    match phase with
    | BGPPPreparing => True
    | BGPPUnpreparing => True
    | _ => False
    end.

  Lemma own_backup_gpreparer_srespm_non_accepting_phase gpp phase phase' rk ts gid γ :
    not (accepting_phase phase')  ->
    own_backup_gpreparer_srespm gpp phase rk ts gid γ -∗
    own_backup_gpreparer_srespm gpp phase' rk ts gid γ.
  Proof.
    iIntros (Hna) "Hgpp".
    iNamed "Hgpp".
    iFrame "∗ %".
    by destruct phase'.
  Qed.

  Definition own_replica_backup_token_cond phase rk ts cid gid γ : iProp Σ :=
    match phase with
    | BGPPInquiring => own_replica_backup_token γ cid.1 cid.2 ts rk gid
    | BGPPValidating => own_replica_backup_token γ cid.1 cid.2 ts rk gid
    | _ => True
    end.

  Definition own_backup_gpreparer_with_phase gpp phase rk ts cid gid γ : iProp Σ :=
    ∃ (pps : gmap u64 ppsl),
      "Hnrps"   ∷ own_backup_gpreparer_nrps gpp ∗
      "Hphase"  ∷ own_backup_gpreparer_phase gpp phase ∗
      "Hpwrs"   ∷ own_backup_gpreparer_pwrs gpp ts gid γ ∗
      "Hpps"    ∷ own_backup_gpreparer_pps gpp pps rk ts cid gid γ ∗
      "Hvdm"    ∷ own_backup_gpreparer_vdm gpp ts gid γ ∗
      "Hsrespm" ∷ own_backup_gpreparer_srespm gpp phase rk ts gid γ ∗
      "Htoken"  ∷ own_replica_backup_token_cond phase rk ts cid gid γ ∗
      "#Hsafe"  ∷ safe_backup_gpreparer_phase γ ts cid gid rk phase.

  Definition own_backup_gpreparer gpp rk ts cid gid γ : iProp Σ :=
    ∃ (phase : bgppphase),
      "Hgpp" ∷ own_backup_gpreparer_with_phase gpp phase rk ts cid gid γ.

End repr.
