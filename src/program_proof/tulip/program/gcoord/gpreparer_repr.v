From Perennial.program_proof.tulip.program Require Import prelude.

Inductive gppphase :=
| GPPValidating
| GPPPreparing
| GPPUnpreparing
| GPPWaiting
| GPPPrepared
| GPPCommitted
| GPPAborted.

Definition gppphase_to_u64 phase :=
  match phase with
  | GPPValidating => (W64 0)
  | GPPPreparing => (W64 1)
  | GPPUnpreparing => (W64 2)
  | GPPWaiting => (W64 3)
  | GPPPrepared => (W64 4)
  | GPPCommitted => (W64 5)
  | GPPAborted => (W64 6)
  end.

#[global]
Instance gppphase_to_u64_inj :
  Inj eq eq gppphase_to_u64.
Proof. intros x y H. by destruct x, y. Defined.

Inductive gppaction :=
| GPPFastPrepare
| GPPValidate
| GPPPrepare
| GPPUnprepare
| GPPQuery
| GPPRefresh.

Definition gppaction_to_u64 action :=
  match action with
  | GPPFastPrepare => (W64 0)
  | GPPValidate => (W64 1)
  | GPPPrepare => (W64 2)
  | GPPUnprepare => (W64 3)
  | GPPQuery => (W64 4)
  | GPPRefresh => (W64 5)
  end.

#[global]
Instance gppaction_to_u64_inj :
  Inj eq eq gppaction_to_u64.
Proof. intros x y H. by destruct x, y. Defined.

Definition gpp_ready phase :=
  match phase with
  | GPPValidating => False
  | GPPPreparing => False
  | GPPUnpreparing => False
  | GPPWaiting => False
  | GPPPrepared => True
  | GPPCommitted => True
  | GPPAborted => True
  end.

#[global]
Instance gpp_ready_decision phase :
  Decision (gpp_ready phase).
Proof. destruct phase; apply _. Defined.

Section repr.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  (*@ type GroupPreparer struct {                                             @*)
  (*@     // Number of replicas. Read-only.                                   @*)
  (*@     nrps   uint64                                                       @*)
  (*@     // Control phase.                                                   @*)
  (*@     phase  uint64                                                       @*)
  (*@     // Fast-path replica responses.                                     @*)
  (*@     frespm map[uint64]bool                                              @*)
  (*@     // Replicas validated.                                              @*)
  (*@     vdm    map[uint64]bool                                              @*)
  (*@     // Slow-path replica responses.                                     @*)
  (*@     // NB: The range doesn't need to be bool, unit would suffice.       @*)
  (*@     srespm map[uint64]bool                                              @*)
  (*@     //                                                                  @*)
  (*@     // TODO: Merge @validated and @sresps                               @*)
  (*@     // @phase = VALIDATING => records whether a certain replica is validated; @*)
  (*@     // @phase = PREPARING / UNPREPARING => records prepared/unprepared. @*)
  (*@     //                                                                  @*)
  (*@ }                                                                       @*)
  Definition own_gpreparer_nrps (gpp : loc) : iProp Σ :=
    ∃ (nrps : u64),
      "Hnrps"   ∷ gpp ↦[GroupPreparer :: "nrps"] #nrps ∗
      "%Hnrps"  ∷ ⌜uint.nat nrps = size rids_all⌝.

  Definition own_gpreparer_phase (gpp : loc) (phase : gppphase) : iProp Σ :=
    ∃ (phaseW : u64),
      "HphaseP" ∷ gpp ↦[GroupPreparer :: "phase"] #phaseW ∗
      "%Hphase" ∷ ⌜gppphase_to_u64 phase = phaseW⌝.

  Definition fast_prepare_responses γ ts gid (frespm : gmap u64 bool) : iProp Σ :=
    [∗ map] rid ↦ p ∈ frespm,
      is_replica_pdec_at_rank γ gid rid ts O p ∗
      (if p then is_replica_validated_ts γ gid rid ts else True).

  Definition validation_responses γ ts gid (vdm : gmap u64 bool) : iProp Σ :=
    ([∗ set] rid ∈ dom vdm, is_replica_validated_ts γ gid rid ts).

  Definition slow_prepare_responses γ ts gid phase (srespm : gmap u64 bool) : iProp Σ :=
    match phase with
    | GPPValidating => True
    | GPPPreparing =>
        ([∗ set] rid ∈ dom srespm, is_replica_pdec_at_rank γ gid rid ts 1%nat true)
    | GPPUnpreparing =>
        ([∗ set] rid ∈ dom srespm, is_replica_pdec_at_rank γ gid rid ts 1%nat false)
    | GPPWaiting => True
    | GPPPrepared => True
    | GPPCommitted => True
    | GPPAborted => True
    end.

  #[global]
  Instance slow_prepare_responses_persistent γ ts gid phase srespm :
    Persistent (slow_prepare_responses γ ts gid phase srespm).
  Proof. destruct phase; apply _. Defined.

  Definition safe_gpreparer_phase γ ts gid phase : iProp Σ :=
    match phase with
    | GPPValidating => True
    | GPPPreparing =>
        quorum_validated γ gid ts ∗ is_group_prepare_proposal γ gid ts 1%nat true
    | GPPUnpreparing => is_group_prepare_proposal γ gid ts 1%nat false
    | GPPWaiting => True
    | GPPPrepared =>
        quorum_prepared γ gid ts ∗ quorum_validated γ gid ts
    | GPPCommitted => ∃ wrs, is_txn_committed γ ts wrs
    | GPPAborted => is_txn_aborted γ ts ∨ quorum_unprepared γ gid ts
    end.

  #[global]
  Instance safe_gpreparer_phase_persistent γ ts gid phase :
    Persistent (safe_gpreparer_phase γ ts gid phase).
  Proof. destruct phase; apply _. Defined.

  Definition slow_path_permission γ ts gid phase : iProp Σ :=
    match phase with
    | GPPValidating => own_txn_client_token γ ts gid
    | GPPPreparing => True
    | GPPUnpreparing => True
    | GPPWaiting => True
    | GPPPrepared => True
    | GPPCommitted => True
    | GPPAborted => True
    end.

  Definition own_gpreparer_frespm (gpp : loc) ts gid γ : iProp Σ :=
    ∃ (frespmP : loc) (frespm : gmap u64 bool),
      "HfrespmP" ∷ gpp ↦[GroupPreparer :: "frespm"] #frespmP ∗
      "Hfrespm"  ∷ own_map frespmP (DfracOwn 1) frespm ∗
      "#Hfast"   ∷ fast_prepare_responses γ ts gid frespm ∗
      "%Hfincl"  ∷ ⌜dom frespm ⊆ rids_all⌝.

  Definition own_gpreparer_vdm (gpp : loc) ts gid γ : iProp Σ :=
    ∃ (vdmP : loc) (vdm : gmap u64 bool),
      "HvdmP"        ∷ gpp ↦[GroupPreparer :: "vdm"] #vdmP ∗
      "Hvdm"         ∷ own_map vdmP (DfracOwn 1) vdm ∗
      "#Hvalidation" ∷ validation_responses γ ts gid vdm ∗
      "%Hvincl"      ∷ ⌜dom vdm ⊆ rids_all⌝.

  Definition own_srespm_map_conditional
    phase srespmP (srespm : gmap u64 bool) : iProp Σ :=
    match phase with
    | GPPValidating => True
    | GPPPreparing => own_map srespmP (DfracOwn 1) srespm
    | GPPUnpreparing => own_map srespmP (DfracOwn 1) srespm
    | GPPWaiting => True
    | GPPPrepared => True
    | GPPCommitted => True
    | GPPAborted => True
    end.

  Definition own_gpreparer_srespm (gpp : loc) (phase : gppphase) ts gid γ : iProp Σ :=
    ∃ (srespmP : loc) (srespm : gmap u64 bool),
      "HsrespmP" ∷ gpp ↦[GroupPreparer :: "srespm"] #srespmP ∗
      "Hsrespm"  ∷ own_srespm_map_conditional phase srespmP srespm ∗
      "#Hslow"   ∷ slow_prepare_responses γ ts gid phase srespm ∗
      "%Hsincl"  ∷ ⌜dom srespm ⊆ rids_all⌝.

  Definition own_gpreparer_with_phase
    (gpp : loc) (phase : gppphase) ts gid γ : iProp Σ :=
      "Hnrps"   ∷ own_gpreparer_nrps gpp ∗
      "Hphase"  ∷ own_gpreparer_phase gpp phase ∗
      "Hfrespm" ∷ own_gpreparer_frespm gpp ts gid γ ∗
      "Hvdm"    ∷ own_gpreparer_vdm gpp ts gid γ ∗
      "Hsrespm" ∷ own_gpreparer_srespm gpp phase ts gid γ ∗
      "Htxncli" ∷ slow_path_permission γ ts gid phase ∗
      "#Hsafe"  ∷ safe_gpreparer_phase γ ts gid phase.

  Definition own_gpreparer (gpp : loc) ts gid γ : iProp Σ :=
    ∃ (phase : gppphase),
      "Hgpp" ∷ own_gpreparer_with_phase gpp phase ts gid γ.

  Definition own_gpreparer_uninit (gpp : loc) : iProp Σ :=
    ∃ (phase : u64) (frespmP : loc) (vdmP : loc) (srespmP : loc),
      "HphaseP"  ∷ gpp ↦[GroupPreparer :: "phase"] #phase ∗
      "HfrespmP" ∷ gpp ↦[GroupPreparer :: "frespm"] #frespmP ∗
      "HvdmP"    ∷ gpp ↦[GroupPreparer :: "vdm"] #vdmP ∗
      "HsrespmP" ∷ gpp ↦[GroupPreparer :: "srespm"] #srespmP ∗
      "Hnrps"    ∷ own_gpreparer_nrps gpp.

End repr.
