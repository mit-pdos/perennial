From Perennial.program_proof.tulip.invariance Require Import propose.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program Require Import quorum count_bool_map.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

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

End repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupPreparer__cquorum (gpp : loc) (n : u64) :
    {{{ own_gpreparer_nrps gpp }}}
      GroupPreparer__cquorum #gpp #n
    {{{ RET #(bool_decide (size rids_all / 2 < uint.Z n)); own_gpreparer_nrps gpp }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) cquorum(n uint64) bool {                      @*)
    (*@     return quorum.ClassicQuorum(gpp.nrps) <= n                          @*)
    (*@ }                                                                       @*)
    iNamed "Hgpp".
    wp_loadField.
    wp_apply wp_ClassicQuorum.
    iIntros (x Hx).
    wp_pures.
    case_bool_decide as Hc1.
    { case_bool_decide as Hc2; last word.
      iApply "HΦ". by iFrame "∗ %".
    }
    { case_bool_decide as Hc2; first word.
      iApply "HΦ". by iFrame "∗ %".
    }
  Qed.

  Theorem wp_GroupPreparer__fquorum (gpp : loc) (n : u64) :
    {{{ own_gpreparer_nrps gpp }}}
      GroupPreparer__fquorum #gpp #n
    {{{ RET #(bool_decide (((3 * size rids_all + 3) / 4 ≤ uint.Z n) ∧ size rids_all ≠ O));
        own_gpreparer_nrps gpp
    }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) fquorum(n uint64) bool {                      @*)
    (*@     return quorum.FastQuorum(gpp.nrps) <= n                             @*)
    (*@ }                                                                       @*)
    iNamed "Hgpp".
    wp_loadField.
    wp_apply wp_FastQuorum.
    { rewrite size_rids_all in Hnrps. word. }
    iIntros (x Hx).
    wp_pures.
    case_bool_decide as Hc1.
    { case_bool_decide as Hc2; last word.
      iApply "HΦ". by iFrame "∗ %".
    }
    { case_bool_decide as Hc2.
      { exfalso.
        apply Classical_Prop.not_and_or in Hc1.
        destruct Hc1 as [Hc1 | Hz]; last first.
        { rewrite size_rids_all in Hz. lia. }
        word.
      }
      iApply "HΦ". by iFrame "∗ %".
    }
  Qed.

  Theorem wp_GroupPreparer__hcquorum (gpp : loc) (n : u64) :
    {{{ own_gpreparer_nrps gpp }}}
      GroupPreparer__hcquorum #gpp #n
    {{{ RET #(bool_decide (size rids_all / 4 + 1 ≤ uint.Z n));
        own_gpreparer_nrps gpp
    }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) hcquorum(n uint64) bool {                     @*)
    (*@     return quorum.Half(quorum.ClassicQuorum(gpp.nrps)) <= n             @*)
    (*@ }                                                                       @*)
    iNamed "Hgpp".
    wp_loadField.
    wp_apply wp_ClassicQuorum.
    iIntros (x Hx).
    wp_apply wp_Half.
    { clear -Hx. word. }
    iIntros (y Hy).
    wp_pures.
    case_bool_decide as Hc1.
    { case_bool_decide as Hc2; last first.
      { exfalso. clear -Hnrps Hx Hy Hc1 Hc2. word. }
      iApply "HΦ". by iFrame "∗ %".
    }
    { case_bool_decide as Hc2.
      { exfalso. clear -Hnrps Hx Hy Hc1 Hc2. word. }
      iApply "HΦ". by iFrame "∗ %".
    }
  Qed.

  Theorem wp_GroupPreparer__ready (gpp : loc) phase :
    {{{ own_gpreparer_phase gpp phase }}}
      GroupPreparer__ready #gpp
    {{{ RET #(bool_decide (gpp_ready phase)); own_gpreparer_phase gpp phase }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) ready() bool {                                @*)
    (*@     return GPP_PREPARED <= gpp.phase                                    @*)
    (*@ }                                                                       @*)
    iNamed "Hgpp".
    wp_loadField.
    wp_pures.
    rewrite /gppphase_to_u64 in Hphase.
    rewrite /gpp_ready.
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

  Theorem wp_GroupPreparer__ready_external (gpp : loc) phase ts gid γ :
    {{{ own_gpreparer_with_phase gpp phase ts gid γ }}}
      GroupPreparer__ready #gpp
    {{{ RET #(bool_decide (gpp_ready phase)); own_gpreparer_with_phase gpp phase ts gid γ }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    iNamed "Hgpp".
    wp_apply (wp_GroupPreparer__ready with "Hphase").
    iIntros "Hphase".
    iApply "HΦ".
    by iFrame "∗ #".
  Qed.

  Definition try_resign_requirement γ ts (res : rpres) : iProp Σ :=
    match res with
    | ReplicaOK => True
    | ReplicaCommittedTxn => (∃ wrs, is_txn_committed γ ts wrs)
    | ReplicaAbortedTxn => is_txn_aborted γ ts
    | ReplicaStaleCoordinator => True
    | ReplicaFailedValidation => True
    | ReplicaInvalidRank => True
    | ReplicaWrongLeader => True
    end.

  #[global]
  Instance try_resign_requirement_persistent γ ts res :
    Persistent (try_resign_requirement γ ts res).
  Proof. destruct res; apply _. Defined.

  Definition not_finalizing_rpres (res : rpres) :=
    match res with
    | ReplicaOK => True
    | ReplicaCommittedTxn => False
    | ReplicaAbortedTxn => False
    | ReplicaStaleCoordinator => False
    | ReplicaFailedValidation => True
    | ReplicaInvalidRank => True
    | ReplicaWrongLeader => True
    end.

  Theorem wp_GroupPreparer__tryResign (gpp : loc) (res : rpres) ts gid γ :
    try_resign_requirement γ ts res -∗
    {{{ own_gpreparer gpp ts gid γ }}}
      GroupPreparer__tryResign #gpp #(rpres_to_u64 res)
    {{{ (resigned : bool), RET #resigned; 
        own_gpreparer gpp ts gid γ ∗
        ⌜if resigned then True else not_finalizing_rpres res⌝
    }}}.
  Proof.
    iIntros "#Hreq" (Φ) "!> Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) tryResign(res uint64) bool {                  @*)
    (*@     if gpp.ready() {                                                    @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    do 2 iNamed "Hgpp".
    wp_apply (wp_GroupPreparer__ready with "Hphase").
    iIntros "Hphase".
    case_bool_decide as Hready; wp_pures.
    { iApply "HΦ". by iFrame. }

    (*@     if res == tulip.REPLICA_COMMITTED_TXN {                             @*)
    (*@         gpp.phase = GPP_COMMITTED                                       @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Hcmted; wp_pures.
    { iNamed "Hphase".
      destruct res; try done.
      wp_storeField.
      iApply "HΦ".
      iModIntro.
      iSplit; last done.
      iExists GPPCommitted.
      iFrame "∗ # %".
      iSplit; first done.
      iNamed "Hsrespm".
      by iFrame "∗ %".
    }

    (*@     if res == tulip.REPLICA_ABORTED_TXN {                               @*)
    (*@         gpp.phase = GPP_ABORTED                                         @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Habted; wp_pures.
    { iNamed "Hphase".
      destruct res; try done.
      wp_storeField.
      iApply "HΦ".
      iModIntro.
      iSplit; last done.
      iExists GPPAborted.
      iFrame "∗ # %".
      iSplit; first done.
      iNamed "Hsrespm".
      by iFrame "∗ %".
    }

    (*@     if res == tulip.REPLICA_STALE_COORDINATOR {                         @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Hstale; wp_pures.
    { iApply "HΦ". by iFrame. }

    (*@     return false                                                        @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    iFrame "∗ # %".
    iPureIntro.
    by destruct res.
  Qed.

  Theorem wp_GroupPreparer__tryFastAbort (gpp : loc) ts gid γ :
    {{{ own_gpreparer gpp ts gid γ }}}
      GroupPreparer__tryFastAbort #gpp
    {{{ (aborted : bool), RET #aborted; own_gpreparer gpp ts gid γ }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) tryFastAbort() bool {                         @*)
    (*@     // Count how many replicas have fast unprepared.                    @*)
    (*@     n := util.CountBoolMap(gpp.frespm, false)                           @*)
    (*@                                                                         @*)
    do 2 iNamed "Hgpp". iNamed "Hfrespm".
    wp_loadField.
    wp_apply (wp_CountBoolMap with "Hfrespm").
    iIntros (n) "[Hfrespm %Hn]".
    iAssert (own_gpreparer_frespm gpp ts gid γ)%I
      with "[HfrespmP Hfrespm]" as "Hfrespm".
    { by iFrame "∗ # %". }

    (*@     // Move to the ABORTED phase if obtaining a fast quorum of fast unprepares. @*)
    (*@     if gpp.fquorum(n) {                                                 @*)
    (*@         gpp.phase = GPP_ABORTED                                         @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@     return false                                                        @*)
    (*@ }                                                                       @*)
    wp_apply (wp_GroupPreparer__fquorum with "Hnrps").
    iIntros "Hnrps".
    case_bool_decide as Hfq; wp_pures.
    { iNamed "Hphase".
      wp_storeField.
      iApply "HΦ".
      iModIntro.
      iExists GPPAborted.
      iFrame "∗ #".
      iSplit; first done.
      iSplitL "Hsrespm".
      { iNamed "Hsrespm". by iFrame "∗ %". }
      iSplit; first done.
      iRight.
      iExists O.
      rewrite /quorum_pdec_at_rank.
      case_decide; last done.
      set frespmq := filter _ _ in Hn.
      iExists (dom frespmq).
      iSplit; last first.
      { iPureIntro.
        split.
        { etrans; last apply Hfincl. apply dom_filter_subseteq. }
        { destruct Hfq as [Hfq Hnz].
          split; last done.
          rewrite size_dom.
          clear -Hfq Hn. word.
        }
      }
      rewrite /fast_prepare_responses.
      iDestruct (big_sepM_subseteq _ _ frespmq with "Hfast") as "Hfastq".
      { apply map_filter_subseteq. }
      rewrite big_sepS_big_sepM.
      iApply (big_sepM_mono with "Hfastq").
      iIntros (rid b Hb) "[Hpdec _]".
      apply map_lookup_filter_Some in Hb as [_ Hb]. simpl in Hb.
      by subst b.
    }
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

  Theorem wp_GroupPreparer__tryFastPrepare (gpp : loc) ts gid γ :
    {{{ own_gpreparer gpp ts gid γ }}}
      GroupPreparer__tryFastPrepare #gpp
    {{{ (prepared : bool), RET #prepared; own_gpreparer gpp ts gid γ }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) tryFastPrepare() bool {                       @*)
    (*@     // Count how many replicas have fast prepared.                      @*)
    (*@     n := util.CountBoolMap(gpp.frespm, true)                            @*)
    (*@                                                                         @*)
    do 2 iNamed "Hgpp". iNamed "Hfrespm".
    wp_loadField.
    wp_apply (wp_CountBoolMap with "Hfrespm").
    iIntros (n) "[Hfrespm %Hn]".
    iAssert (own_gpreparer_frespm gpp ts gid γ)%I
      with "[HfrespmP Hfrespm]" as "Hfrespm".
    { by iFrame "∗ # %". }

    (*@     // Move to the PREPARED phase if obtaining a fast quorum of fast prepares. @*)
    (*@     if gpp.fquorum(n) {                                                 @*)
    (*@         gpp.phase = GPP_PREPARED                                        @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@     return false                                                        @*)
    (*@ }                                                                       @*)
    wp_apply (wp_GroupPreparer__fquorum with "Hnrps").
    iIntros "Hnrps".
    case_bool_decide as Hfq; wp_pures.
    { iNamed "Hphase".
      wp_storeField.
      iApply "HΦ".
      iModIntro.
      iExists GPPPrepared.
      iFrame "∗ #".
      iSplit; first done.
      iSplitL "Hsrespm".
      { iNamed "Hsrespm". by iFrame "∗ %". }
      iSplit; first done.
      set frespmq := filter _ _ in Hn.
      iSplit.
      { (* Prove [quorum_prepared]. *)
        iExists O.
        rewrite /quorum_pdec_at_rank.
        case_decide; last done.
        iExists (dom frespmq).
        iSplit; last first.
        { iPureIntro.
          split.
          { etrans; last apply Hfincl. apply dom_filter_subseteq. }
          { destruct Hfq as [Hfq Hnz].
            split; last done.
            rewrite size_dom.
            clear -Hfq Hn. word.
          }
        }
        rewrite /fast_prepare_responses.
        iDestruct (big_sepM_subseteq _ _ frespmq with "Hfast") as "Hfastq".
        { apply map_filter_subseteq. }
        rewrite big_sepS_big_sepM.
        iApply (big_sepM_mono with "Hfastq").
        iIntros (rid b Hb) "[Hpdec _]".
        apply map_lookup_filter_Some in Hb as [_ Hb]. simpl in Hb.
        by subst b.
      }
      { (* Prove [quorum_validated]. *)
        iExists (dom frespmq).
        iSplit; last first.
        { iPureIntro.
          split.
          { etrans; last apply Hfincl. apply dom_filter_subseteq. }
          { destruct Hfq as [Hfq Hnz].
            rewrite /cquorum_size size_dom.
            clear -Hfq Hn Hnz. word.
          }
        }
        rewrite /fast_prepare_responses.
        iDestruct (big_sepM_subseteq _ _ frespmq with "Hfast") as "Hfastq".
        { apply map_filter_subseteq. }
        iDestruct (big_sepM_sep with "Hfastq") as "[_ Hvdq]".
        rewrite big_sepS_big_sepM.
        iApply (big_sepM_mono with "Hvdq").
        iIntros (rid b Hb) "Hvd".
        apply map_lookup_filter_Some in Hb as [_ Hb]. simpl in Hb.
        by subst b.
      }
    }
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

  Theorem wp_GroupPreparer__tryBecomePreparing (gpp : loc) ts gid γ :
    gid ∈ gids_all ->
    know_tulip_inv γ -∗
    {{{ own_gpreparer_with_phase gpp GPPValidating ts gid γ }}}
      GroupPreparer__tryBecomePreparing #gpp
    {{{ RET #(); own_gpreparer gpp ts gid γ }}}.
  Proof.
    iIntros (Hgid) "#Hinv".
    iIntros (Φ) "!> Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) tryBecomePreparing() {                        @*)
    (*@     // Count how many replicas have validated.                          @*)
    (*@     nvd := uint64(len(gpp.vdm))                                         @*)
    (*@     if !gpp.cquorum(nvd) {                                              @*)
    (*@         // Cannot move to the PREPARING phase unless some classic quorum of @*)
    (*@         // replicas successfully validate.                              @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hgpp". iNamed "Hvdm".
    wp_loadField.
    wp_apply (wp_MapLen with "Hvdm").
    iIntros "[%Hnvdmnoof Hvdm]".
    iAssert (own_gpreparer_vdm gpp ts gid γ)%I with "[HvdmP Hvdm]" as "Hvdm".
    { iFrame "∗ # %". }
    wp_apply (wp_GroupPreparer__cquorum with "Hnrps").
    iIntros "Hnrps".
    case_bool_decide as Hnvd; wp_pures; last first.
    { iApply "HΦ". by iFrame "∗ #". }

    (*@     // Count how many replicas have responded in the fast path.         @*)
    (*@     nresp := uint64(len(gpp.frespm))                                    @*)
    (*@     if !gpp.cquorum(nresp) {                                            @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hfrespm".
    wp_loadField.
    wp_apply (wp_MapLen with "Hfrespm").
    iIntros "[%Hnrespmnoof Hfrespm]".
    wp_apply (wp_GroupPreparer__cquorum with "Hnrps").
    iIntros "Hnrps".
    case_bool_decide as Hnresp; wp_pures; last first.
    { iApply "HΦ". by iFrame "∗ # %". }

    (*@     // Count how many replicas have prepared.                           @*)
    (*@     nfp := util.CountBoolMap(gpp.frespm, true)                          @*)
    (*@     if !gpp.hcquorum(nfp) {                                             @*)
    (*@         // Cannot move to the PREPARING phase unless half (i.e., celing(n / 2)) @*)
    (*@         // of replicas in some classic quorum agrees to prepare.        @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_CountBoolMap with "Hfrespm").
    iIntros (nfp) "[Hfrespm %Hnfp]".
    wp_apply (wp_GroupPreparer__hcquorum with "Hnrps").
    iIntros "Hnrps".
    case_bool_decide as Hhcq; wp_pures; last first.
    { iApply "HΦ". by iFrame "∗ # %". }
    (* Prove [safe_proposal γ gid ts 1%nat true] to propose [true] at rank 1 for [ts]. *)
    iAssert (safe_proposal γ gid ts 1%nat true)%I as "#Hsafepsl".
    { simpl.
      iDestruct (big_sepM_sep with "Hfast") as "[Hpdecx _]".
      rewrite /is_replica_pdec_at_rank.
      iDestruct (big_sepM_exists_sepM2 with "Hpdecx") as (bm) "Hpdecy".
      iDestruct (big_sepM2_and with "Hpdecy") as "[Hpdec Hacpt]".
      iDestruct (big_sepM2_pure with "Hacpt") as %[_ Hacpt].
      iDestruct (big_sepM2_dom with "Hpdec") as %Hdombm.
      assert (Hcq : cquorum rids_all (dom bm)).
      { rewrite -Hdombm.
        split; first apply Hfincl.
        rewrite /cquorum_size size_dom.
        clear -Hnresp. word.
      }
      iExists bm.
      set sc := size rids_all.
      simpl.
      assert (latest_before_quorum 1 bm = O) as ->.
      { unshelve epose proof (latest_before_quorum_lt bm 1%nat _ _) as Hltone.
        { rewrite -dom_empty_iff_L. by eapply cquorum_non_empty_q. }
        { done. }
        lia.
      }
      iSplit.
      { iApply (big_sepM2_sepM_impl with "Hpdec"); first done.
        iIntros (rid b l1 l2 Hb Hl1 Hl2) "!> #Hlb".
        rewrite Hl1 in Hl2. by inv Hl2.
      }
      iSplit; first done.
      iPureIntro.
      split; first apply Hcq.
      split.
      { intros k l Hl.
        assert (is_Some (frespm !! k)) as [b Hb].
        { by rewrite -elem_of_dom Hdombm elem_of_dom. }
        specialize (Hacpt _ _ _ Hb Hl).
        apply lookup_lt_Some in Hacpt.
        clear -Hacpt. lia.
      }
      simpl.
      assert (Heq : (uint.nat nfp ≤ nfast bm true)%nat).
      { rewrite Hnfp /nfast -2!size_dom.
        apply subseteq_size.
        intros x Hx.
        apply elem_of_dom in Hx as [b Hb].
        apply map_lookup_filter_Some in Hb as [Hb Heq].
        simpl in Heq. subst b.
        assert (is_Some (bm !! x)) as [l Hl].
        { by rewrite -elem_of_dom -Hdombm elem_of_dom. }
        specialize (Hacpt _ _ _ Hb Hl).
        apply elem_of_dom.
        exists l.
        by apply map_lookup_filter_Some.
      }
      clear -Hhcq Heq. word.
    }

    (*@     gpp.srespm = make(map[uint64]bool)                                  @*)
    (*@     gpp.phase = GPP_PREPARING                                           @*)
    (*@                                                                         @*)
    iNamed "Hsrespm".
    wp_apply wp_NewMap.
    iClear "Hsrespm".
    iIntros (srespmP') "Hsrespm".
    wp_storeField.
    iNamed "Hphase".
    simpl.
    wp_storeField.
    iAssert (own_gpreparer_frespm gpp ts gid γ)%I
      with "[HfrespmP Hfrespm]" as "Hfrespm".
    { iFrame "∗ # %". }
    iAssert (own_gpreparer_phase gpp GPPPreparing)%I
      with "[HphaseP]" as "Hphase".
    { by iFrame. }
    iAssert (own_gpreparer_srespm gpp GPPPreparing ts gid γ)%I
      with "[HsrespmP Hsrespm]" as "Hsrespm".
    { iFrame. by rewrite /= dom_empty_L big_sepS_empty. }

    (*@     // Logical action: Propose.                                         @*)
    (*@ }                                                                       @*)
    iInv "Hinv" as "> HinvO" "HinvC".
    iNamed "HinvO".
    simpl.
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]".
    { apply Hgid. }
    iMod (group_inv_propose with "Hsafepsl [Htxncli] Hgroup") as "[Hgroup #Hppsl]".
    { done. }
    { by rewrite /exclusive_proposal /=. }
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
    iApply "HΦ".
    iFrame "∗ #".
    iPureIntro.
    split; first apply Hvincl.
    rewrite /cquorum_size size_dom.
    clear -Hnvd. word.
  Qed.

  Theorem wp_GroupPreparer__tryBecomeUnpreparing (gpp : loc) ts gid γ :
    gid ∈ gids_all ->
    know_tulip_inv γ -∗
    {{{ own_gpreparer_with_phase gpp GPPValidating ts gid γ }}}
      GroupPreparer__tryBecomeUnpreparing #gpp
    {{{ RET #(); own_gpreparer gpp ts gid γ }}}.
  Proof.
    iIntros (Hgid) "#Hinv".
    iIntros (Φ) "!> Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) tryBecomeUnpreparing() {                      @*)
    (*@     // Count how many replicas have responded in the fast path.         @*)
    (*@     nresp := uint64(len(gpp.frespm))                                    @*)
    (*@     if !gpp.cquorum(nresp) {                                            @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hgpp".
    iNamed "Hfrespm".
    wp_loadField.
    wp_apply (wp_MapLen with "Hfrespm").
    iIntros "[%Hnrespmnoof Hfrespm]".
    wp_apply (wp_GroupPreparer__cquorum with "Hnrps").
    iIntros "Hnrps".
    case_bool_decide as Hnresp; wp_pures; last first.
    { iApply "HΦ". by iFrame "∗ # %". }

    (*@     // Count how many replicas have unprepared.                         @*)
    (*@     nfu := util.CountBoolMap(gpp.frespm, false)                         @*)
    (*@     if !gpp.hcquorum(nfu) {                                             @*)
    (*@         // Cannot move to the UNPREPARING phase unless half of replicas in some @*)
    (*@         // classic quorum agrees to unprepare.                          @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_CountBoolMap with "Hfrespm").
    iIntros (nfp) "[Hfrespm %Hnfp]".
    wp_apply (wp_GroupPreparer__hcquorum with "Hnrps").
    iIntros "Hnrps".
    case_bool_decide as Hhcq; wp_pures; last first.
    { iApply "HΦ". by iFrame "∗ # %". }
    (* Prove [safe_proposal γ gid ts 1%nat true] to propose [true] at rank 1 for [ts]. *)
    iAssert (safe_proposal γ gid ts 1%nat false)%I as "#Hsafepsl".
    { simpl.
      iDestruct (big_sepM_sep with "Hfast") as "[Hpdecx _]".
      rewrite /is_replica_pdec_at_rank.
      iDestruct (big_sepM_exists_sepM2 with "Hpdecx") as (bm) "Hpdecy".
      iDestruct (big_sepM2_and with "Hpdecy") as "[Hpdec Hacpt]".
      iDestruct (big_sepM2_pure with "Hacpt") as %[_ Hacpt].
      iDestruct (big_sepM2_dom with "Hpdec") as %Hdombm.
      assert (Hcq : cquorum rids_all (dom bm)).
      { rewrite -Hdombm.
        split; first apply Hfincl.
        rewrite /cquorum_size size_dom.
        clear -Hnresp. word.
      }
      iExists bm.
      set sc := size rids_all.
      simpl.
      assert (latest_before_quorum 1 bm = O) as ->.
      { unshelve epose proof (latest_before_quorum_lt bm 1%nat _ _) as Hltone.
        { rewrite -dom_empty_iff_L. by eapply cquorum_non_empty_q. }
        { done. }
        lia.
      }
      iSplit.
      { iApply (big_sepM2_sepM_impl with "Hpdec"); first done.
        iIntros (rid b l1 l2 Hb Hl1 Hl2) "!> #Hlb".
        rewrite Hl1 in Hl2. by inv Hl2.
      }
      iSplit; first done.
      iPureIntro.
      split; first apply Hcq.
      split.
      { intros k l Hl.
        assert (is_Some (frespm !! k)) as [b Hb].
        { by rewrite -elem_of_dom Hdombm elem_of_dom. }
        specialize (Hacpt _ _ _ Hb Hl).
        apply lookup_lt_Some in Hacpt.
        clear -Hacpt. lia.
      }
      simpl.
      assert (Heq : (uint.nat nfp ≤ nfast bm false)%nat).
      { rewrite Hnfp /nfast -2!size_dom.
        apply subseteq_size.
        intros x Hx.
        apply elem_of_dom in Hx as [b Hb].
        apply map_lookup_filter_Some in Hb as [Hb Heq].
        simpl in Heq. subst b.
        assert (is_Some (bm !! x)) as [l Hl].
        { by rewrite -elem_of_dom -Hdombm elem_of_dom. }
        specialize (Hacpt _ _ _ Hb Hl).
        apply elem_of_dom.
        exists l.
        by apply map_lookup_filter_Some.
      }
      clear -Hhcq Heq. word.
    }

    (*@     gpp.srespm = make(map[uint64]bool)                                  @*)
    (*@     gpp.phase = GPP_UNPREPARING                                         @*)
    (*@                                                                         @*)
    iNamed "Hsrespm".
    wp_apply wp_NewMap.
    iClear "Hsrespm".
    iIntros (srespmP') "Hsrespm".
    wp_storeField.
    iNamed "Hphase".
    simpl.
    wp_storeField.
    iAssert (own_gpreparer_frespm gpp ts gid γ)%I
      with "[HfrespmP Hfrespm]" as "Hfrespm".
    { iFrame "∗ # %". }
    iAssert (own_gpreparer_phase gpp GPPUnpreparing)%I
      with "[HphaseP]" as "Hphase".
    { by iFrame. }
    iAssert (own_gpreparer_srespm gpp GPPUnpreparing ts gid γ)%I
      with "[HsrespmP Hsrespm]" as "Hsrespm".
    { iFrame. by rewrite /= dom_empty_L big_sepS_empty. }

    (*@     // Logical action: Propose.                                         @*)
    (*@ }                                                                       @*)
    iInv "Hinv" as "> HinvO" "HinvC".
    iNamed "HinvO".
    simpl.
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]".
    { apply Hgid. }
    iMod (group_inv_propose with "Hsafepsl [Htxncli] Hgroup") as "[Hgroup #Hppsl]".
    { done. }
    { by rewrite /exclusive_proposal /=. }
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
    iApply "HΦ".
    by iFrame "∗ #".
  Qed.

  Theorem wp_GroupPreparer__collectFastDecision
    (gpp : loc) (rid : u64) (b : bool) ts gid γ :
    rid ∈ rids_all ->
    is_replica_pdec_at_rank γ gid rid ts O b -∗
    (if b then is_replica_validated_ts γ gid rid ts else True) -∗
    {{{ own_gpreparer gpp ts gid γ }}}
      GroupPreparer__collectFastDecision #gpp #rid #b
    {{{ RET #(); own_gpreparer gpp ts gid γ }}}.
  Proof.
    iIntros (Hrid) "#Hpdec #Hvd".
    iIntros (Φ) "!> Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) collectFastDecision(rid uint64, b bool) {     @*)
    (*@     gpp.frespm[rid] = b                                                 @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hgpp". iNamed "Hfrespm".
    wp_loadField.
    wp_apply (wp_MapInsert with "Hfrespm"); first done.
    iIntros "Hfrespm".
    wp_pures.
    iApply "HΦ".
    iFrame "∗ # %".
    iModIntro.
    iSplit.
    { iApply (big_sepM_insert_2 with "[] Hfast"). iFrame "#". }
    iPureIntro.
    rewrite dom_insert_L.
    set_solver.
  Qed.

  Theorem wp_GroupPreparer__collectValidation (gpp : loc) (rid : u64) phase ts gid γ :
    rid ∈ rids_all ->
    is_replica_validated_ts γ gid rid ts -∗
    {{{ own_gpreparer_with_phase gpp phase ts gid γ }}}
      GroupPreparer__collectValidation #gpp #rid
    {{{ RET #(); own_gpreparer_with_phase gpp phase ts gid γ }}}.
  Proof.
    iIntros (Hrid) "#Hvd".
    iIntros (Φ) "!> Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) collectValidation(rid uint64) {               @*)
    (*@     gpp.vdm[rid] = true                                                 @*)
    (*@ }                                                                       @*)
    iNamed "Hgpp". iNamed "Hvdm".
    wp_loadField.
    wp_apply (wp_MapInsert with "Hvdm"); first done.
    iIntros "Hvdm".
    wp_pures.
    iApply "HΦ".
    iFrame "Hfrespm ∗ # %".
    iModIntro.
    iSplit.
    { rewrite /validation_responses dom_insert_L.
      by iApply (big_sepS_insert_2 with "[] Hvalidation").
    }
    iPureIntro.
    rewrite dom_insert_L.
    set_solver.
  Qed.

  Theorem wp_GroupPreparer__in (gpp : loc) (phase : gppphase) ts gid γ :
    {{{ own_gpreparer gpp ts gid γ }}}
      GroupPreparer__in #gpp #(gppphase_to_u64 phase)
    {{{ (ok : bool), RET #ok; 
        if ok
        then own_gpreparer_with_phase gpp phase ts gid γ
        else own_gpreparer gpp ts gid γ
    }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) in(phase uint64) bool {                       @*)
    (*@     return gpp.phase == phase                                           @*)
    (*@ }                                                                       @*)
    rename phase into phasearg.
    do 2 iNamed "Hgpp". iNamed "Hphase".
    wp_loadField.
    wp_pures.
    iApply "HΦ".
    case_bool_decide as Hok; last first.
    { by iFrame "∗ # %". }
    symmetry in Hok. inv Hok.
    by iFrame "∗ # %".
  Qed.

  Theorem wp_GroupPreparer__processFastPrepareResult
    (gpp : loc) (rid : u64) (res : rpres) ts gid γ :
    gid ∈ gids_all ->
    rid ∈ rids_all ->
    fast_prepare_outcome γ gid rid ts res -∗
    know_tulip_inv γ -∗
    {{{ own_gpreparer gpp ts gid γ }}}
      GroupPreparer__processFastPrepareResult #gpp #rid #(rpres_to_u64 res)
    {{{ RET #(); own_gpreparer gpp ts gid γ }}}.
  Proof.
    iIntros (Hgid Hrid) "#Hfp #Hinv".
    iIntros (Φ) "!> Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) processFastPrepareResult(rid uint64, res uint64) { @*)
    (*@     // Result is ready or a backup coordinator has become live.         @*)
    (*@     if gpp.tryResign(res) {                                             @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_GroupPreparer__tryResign with "[] Hgpp").
    { by destruct res. }
    iIntros (resigned) "[Hgpp %Hresigned]".
    destruct resigned; wp_pures.
    { by iApply "HΦ". }

    (*@     // Fast-prepare fails; fast abort if possible.                      @*)
    (*@     if res == tulip.REPLICA_FAILED_VALIDATION {                         @*)
    (*@         gpp.collectFastDecision(rid, false)                             @*)
    (*@                                                                         @*)
    case_bool_decide as Hres; wp_pures.
    { destruct res; try done. simpl.
      wp_apply (wp_GroupPreparer__collectFastDecision with "Hfp [] Hgpp").
      { apply Hrid. }
      { done. }
      iIntros "Hgpp".

      (*@         aborted := gpp.tryFastAbort()                                   @*)
      (*@         if aborted {                                                    @*)
      (*@             return                                                      @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      wp_apply (wp_GroupPreparer__tryFastAbort with "Hgpp").
      iIntros (aborted) "Hgpp".
      wp_pures.
      destruct aborted; wp_pures.
      { by iApply "HΦ". }

      (*@         if !gpp.in(GPP_VALIDATING) {                                    @*)
      (*@             return                                                      @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      wp_apply (wp_GroupPreparer__in _ GPPValidating with "Hgpp").
      iIntros (validating) "Hgpp".
      destruct validating; wp_pures; last first.
      { by iApply "HΦ". }

      (*@         gpp.tryBecomeUnpreparing()                                      @*)
      (*@         return                                                          @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      wp_apply (wp_GroupPreparer__tryBecomeUnpreparing with "Hinv Hgpp").
      { apply Hgid. }
      iIntros "Hgpp".
      wp_pures.
      iApply "HΦ".
      by iFrame.
    }
    (* Prove [res = ReplicaOK]. *)
    destruct res; try done.

    (*@     // Fast-prepare succeeds; fast prepare if possible.                 @*)
    (*@     gpp.collectFastDecision(rid, true)                                  @*)
    (*@     if gpp.tryFastPrepare() {                                           @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iDestruct "Hfp" as "[Hvd Hpdec]".
    wp_apply (wp_GroupPreparer__collectFastDecision with "Hpdec Hvd Hgpp").
    { apply Hrid. }
    iIntros "Hgpp".
    wp_apply (wp_GroupPreparer__tryFastPrepare with "Hgpp").
    iIntros (prepared) "Hgpp".
    destruct prepared; wp_pures.
    { by iApply "HΦ". }

    (*@     // Ignore the result if it's not in the validating phase. At this point, the @*)
    (*@     // other possible phases are preparing and unpreparing.             @*)
    (*@     if !gpp.in(GPP_VALIDATING) {                                        @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_GroupPreparer__in _ GPPValidating with "Hgpp").
    iIntros (validating) "Hgpp".
    destruct validating; wp_pures; last first.
    { by iApply "HΦ". }

    (*@     // Record success of validation and try to move to the preparing phase. @*)
    (*@     gpp.collectValidation(rid)                                          @*)
    (*@     gpp.tryBecomePreparing()                                            @*)
    (*@ }                                                                       @*)
    wp_apply (wp_GroupPreparer__collectValidation with "Hvd Hgpp").
    { apply Hrid. }
    iIntros "Hgpp".
    wp_apply (wp_GroupPreparer__tryBecomePreparing with "Hinv Hgpp").
    { apply Hgid. }
    iIntros "Hgpp".
    wp_pures.
    iApply "HΦ".
    by iFrame.
  Qed.

  Theorem wp_GroupPreparer__processValidateResult
    (gpp : loc) (rid : u64) (res : rpres) ts gid γ :
    gid ∈ gids_all ->
    rid ∈ rids_all ->
    validate_outcome γ gid rid ts res -∗
    know_tulip_inv γ -∗
    {{{ own_gpreparer gpp ts gid γ }}}
      GroupPreparer__processValidateResult #gpp #rid #(rpres_to_u64 res)
    {{{ RET #(); own_gpreparer gpp ts gid γ }}}.
  Proof.
    iIntros (Hgid Hrid) "#Hvd #Hinv".
    iIntros (Φ) "!> Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) processValidateResult(rid uint64, res uint64) { @*)
    (*@     // Result is ready or a backup coordinator has become live.         @*)
    (*@     if gpp.tryResign(res) {                                             @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_GroupPreparer__tryResign with "[] Hgpp").
    { by destruct res. }
    iIntros (resigned) "[Hgpp %Hresigned]".
    destruct resigned; wp_pures.
    { by iApply "HΦ". }

    (*@     // Validation fails; nothing to record.                             @*)
    (*@     if res == tulip.REPLICA_FAILED_VALIDATION {                         @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Hres; wp_pures.
    { by iApply "HΦ". }
    (* Prove [res = ReplicaOK]. *)
    destruct res; try done.

    (*@     // Skip if the coordiantor is not in the validating phase. At this point, @*)
    (*@     // the other possible phases are preparing and unpreparing.         @*)
    (*@     if !gpp.in(GPP_VALIDATING) {                                        @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_GroupPreparer__in _ GPPValidating with "Hgpp").
    iIntros (validating) "Hgpp".
    destruct validating; wp_pures; last first.
    { by iApply "HΦ". }

    (*@     // Record success of validation and try to move to the preparing phase. @*)
    (*@     gpp.collectValidation(rid)                                          @*)
    (*@     gpp.tryBecomePreparing()                                            @*)
    (*@ }                                                                       @*)
    wp_apply (wp_GroupPreparer__collectValidation with "Hvd Hgpp").
    { apply Hrid. }
    iIntros "Hgpp".
    wp_apply (wp_GroupPreparer__tryBecomePreparing with "Hinv Hgpp").
    { apply Hgid. }
    iIntros "Hgpp".
    wp_pures.
    iApply "HΦ".
    by iFrame.
  Qed.

  Theorem wp_GroupPreparer__processPrepareResult
    (gpp : loc) (rid : u64) (res : rpres) ts gid γ :
    rid ∈ rids_all ->
    accept_outcome γ gid rid ts 1%nat true res -∗
    {{{ own_gpreparer gpp ts gid γ }}}
      GroupPreparer__processPrepareResult #gpp #rid #(rpres_to_u64 res)
    {{{ RET #(); own_gpreparer gpp ts gid γ }}}.
  Proof.
    iIntros (Hrid) "#Hvd".
    iIntros (Φ) "!> Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) processPrepareResult(rid uint64, res uint64) { @*)
    (*@     // Result is ready or a backup coordinator has become live.         @*)
    (*@     if gpp.tryResign(res) {                                             @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_GroupPreparer__tryResign with "[] Hgpp").
    { by destruct res. }
    iIntros (resigned) "[Hgpp %Hresigned]".
    destruct resigned; wp_pures.
    { by iApply "HΦ". }
    (* Prove [res = ReplicaOK]. *)
    destruct res; try done. simpl.

    (*@     // We might be able to prove this without an additional check.      @*)
    (*@     if !gpp.in(GPP_PREPARING) {                                         @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_GroupPreparer__in _ GPPPreparing with "Hgpp").
    iIntros (preparing) "Hgpp".
    destruct preparing; wp_pures; last first.
    { by iApply "HΦ". }

    (*@     // Record success of preparing the replica and try to move to prepared. @*)
    (*@     gpp.srespm[rid] = true                                              @*)
    (*@                                                                         @*)
    iNamed "Hgpp". iNamed "Hsrespm".
    wp_loadField.
    wp_apply (wp_MapInsert with "Hsrespm"); first done.
    iIntros "Hsrespm".

    (*@     // Count how many replicas have prepared.                           @*)
    (*@     n := uint64(len(gpp.srespm))                                        @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_MapLen with "Hsrespm").
    iIntros "[%Hn Hsrespm]".
    wp_pures.

    (*@     // Go to prepared phase if successful prepares reaches a classic quorum. @*)
    (*@     if gpp.cquorum(n) {                                                 @*)
    (*@         gpp.phase = GPP_PREPARED                                        @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_apply (wp_GroupPreparer__cquorum with "Hnrps").
    iIntros "Hnrps".
    case_bool_decide as Hq; wp_pures.
    { iNamed "Hphase".
      wp_storeField.
      iApply "HΦ".
      iAssert (own_gpreparer_phase gpp GPPPrepared)%I with "[HphaseP]" as "Hphase".
      { by iFrame. }
      simpl.
      iDestruct (big_sepS_insert_2 rid with "[] Hslow") as "Hslow'".
      { iFrame "Hvd". }
      iAssert (own_gpreparer_srespm gpp GPPPrepared ts gid γ)%I
        with "[HsrespmP Hsrespm]" as "Hsrespm".
      { iFrame. simpl.
        iExists ∅. (* just a placeholder *)
        do 2 (iSplit; first done).
        iPureIntro.
        (* rewrite dom_insert_L. *)
        clear -Hrid Hsincl. set_solver.
      }
      iModIntro.
      iFrame "∗ # %".
      simpl.
      iDestruct "Hsafe" as "[Hqv _]".
      iFrame "Hqv".
      iExists 1%nat.
      rewrite /quorum_pdec_at_rank /=.
      set ridsq := _ ∪ _.
      iExists ridsq.
      iSplit; first done.
      iPureIntro.
      split.
      { clear-Hsincl Hrid. set_solver. }
      { rewrite /cquorum_size.
        destruct (decide (rid ∈ dom srespm)) as [Hin | Hnotin].
        { assert (ridsq = dom srespm) as -> by set_solver.
          rewrite size_dom.
          apply elem_of_dom in Hin.
          rewrite map_size_insert_Some in Hn Hq; last apply Hin.
          clear -Hn Hq. word.
        }
        subst ridsq.
        rewrite size_union; last set_solver.
        rewrite size_singleton size_dom.
        apply not_elem_of_dom in Hnotin.
        rewrite map_size_insert_None in Hn Hq; last apply Hnotin.
        clear -Hn Hq. word.
      }
    }
    iApply "HΦ".
    iAssert (own_gpreparer_srespm gpp GPPPreparing ts gid γ)%I
      with "[HsrespmP Hsrespm]" as "Hsrespm".
    { iFrame. simpl.
      iSplit.
      { rewrite dom_insert_L.
        iApply (big_sepS_insert_2 with "[] Hslow").
        iFrame "Hvd".
      }
      iPureIntro.
      rewrite dom_insert_L.
      clear -Hrid Hsincl. set_solver.
    }
    by iFrame "∗ # %".
  Qed.

  Theorem wp_GroupPreparer__processUnprepareResult
    (gpp : loc) (rid : u64) (res : rpres) ts gid γ :
    rid ∈ rids_all ->
    accept_outcome γ gid rid ts 1%nat false res -∗
    {{{ own_gpreparer gpp ts gid γ }}}
      GroupPreparer__processUnprepareResult #gpp #rid #(rpres_to_u64 res)
    {{{ RET #(); own_gpreparer gpp ts gid γ }}}.
  Proof.
    iIntros (Hrid) "#Hvd".
    iIntros (Φ) "!> Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) processUnprepareResult(rid uint64, res uint64) { @*)
    (*@     // Result is ready or a backup coordinator has become live.         @*)
    (*@     if gpp.tryResign(res) {                                             @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_GroupPreparer__tryResign with "[] Hgpp").
    { by destruct res. }
    iIntros (resigned) "[Hgpp %Hresigned]".
    destruct resigned; wp_pures.
    { by iApply "HΦ". }
    (* Prove [res = ReplicaOK]. *)
    destruct res; try done. simpl.

    (*@     // We might be able to prove this without an additional check.      @*)
    (*@     if !gpp.in(GPP_UNPREPARING) {                                       @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_GroupPreparer__in _ GPPUnpreparing with "Hgpp").
    iIntros (unpreparing) "Hgpp".
    destruct unpreparing; wp_pures; last first.
    { by iApply "HΦ". }

    (*@     // Record success of unpreparing the replica and try to move to aborted. @*)
    (*@     gpp.srespm[rid] = true                                              @*)
    (*@                                                                         @*)
    iNamed "Hgpp". iNamed "Hsrespm".
    wp_loadField.
    wp_apply (wp_MapInsert with "Hsrespm"); first done.
    iIntros "Hsrespm".

    (*@     // Count how many replicas have unprepared.                         @*)
    (*@     n := uint64(len(gpp.srespm))                                        @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_MapLen with "Hsrespm").
    iIntros "[%Hn Hsrespm]".
    wp_pures.

    (*@     // Go to aborted phase if successful unprepares reaches a classic quorum. @*)
    (*@     if gpp.cquorum(n) {                                                 @*)
    (*@         gpp.phase = GPP_ABORTED                                         @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_apply (wp_GroupPreparer__cquorum with "Hnrps").
    iIntros "Hnrps".
    case_bool_decide as Hq; wp_pures.
    { iNamed "Hphase".
      wp_storeField.
      iApply "HΦ".
      iAssert (own_gpreparer_phase gpp GPPAborted)%I with "[HphaseP]" as "Hphase".
      { by iFrame. }
      simpl.
      iDestruct (big_sepS_insert_2 rid with "[] Hslow") as "Hslow'".
      { iFrame "Hvd". }
      iAssert (own_gpreparer_srespm gpp GPPAborted ts gid γ)%I
        with "[HsrespmP Hsrespm]" as "Hsrespm".
      { iFrame. simpl.
        iExists ∅. (* just a placeholder *)
        do 2 (iSplit; first done).
        iPureIntro.
        (* rewrite dom_insert_L. *)
        clear -Hrid Hsincl. set_solver.
      }
      iModIntro.
      iFrame "∗ # %".
      iRight.
      iExists 1%nat.
      rewrite /quorum_pdec_at_rank /=.
      set ridsq := _ ∪ _.
      iExists ridsq.
      iSplit; first done.
      iPureIntro.
      split.
      { clear-Hsincl Hrid. set_solver. }
      { rewrite /cquorum_size.
        destruct (decide (rid ∈ dom srespm)) as [Hin | Hnotin].
        { assert (ridsq = dom srespm) as -> by set_solver.
          rewrite size_dom.
          apply elem_of_dom in Hin.
          rewrite map_size_insert_Some in Hn Hq; last apply Hin.
          clear -Hn Hq. word.
        }
        subst ridsq.
        rewrite size_union; last set_solver.
        rewrite size_singleton size_dom.
        apply not_elem_of_dom in Hnotin.
        rewrite map_size_insert_None in Hn Hq; last apply Hnotin.
        clear -Hn Hq. word.
      }
    }
    iApply "HΦ".
    iAssert (own_gpreparer_srespm gpp GPPUnpreparing ts gid γ)%I
      with "[HsrespmP Hsrespm]" as "Hsrespm".
    { iFrame. simpl.
      iSplit.
      { rewrite dom_insert_L.
        iApply (big_sepS_insert_2 with "[] Hslow").
        iFrame "Hvd".
      }
      iPureIntro.
      rewrite dom_insert_L.
      clear -Hrid Hsincl. set_solver.
    }
    by iFrame "∗ # %".
  Qed.

  Theorem wp_GroupPreparer__processQueryResult
    (gpp : loc) (rid : u64) (res : rpres) ts gid γ :
    rid ∈ rids_all ->
    query_outcome γ ts res -∗
    {{{ own_gpreparer gpp ts gid γ }}}
      GroupPreparer__processQueryResult #gpp #rid #(rpres_to_u64 res)
    {{{ RET #(); own_gpreparer gpp ts gid γ }}}.
  Proof.
    iIntros (Hrid) "#Hquery".
    iIntros (Φ) "!> Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) processQueryResult(rid uint64, res uint64) {  @*)
    (*@     // Result is ready or a backup coordinator has become live.         @*)
    (*@     gpp.tryResign(res)                                                  @*)
    (*@ }                                                                       @*)
    wp_apply (wp_GroupPreparer__tryResign with "[] Hgpp").
    { by destruct res. }
    iIntros (resigned) "[Hgpp %Hresigned]".
    wp_pures.
    by iApply "HΦ".
  Qed.

  Definition safe_gppaction γ ts gid action : iProp Σ :=
    match action with
    | GPPFastPrepare => True
    | GPPValidate => True
    | GPPPrepare => is_group_prepare_proposal γ gid ts 1%nat true
    | GPPUnprepare => is_group_prepare_proposal γ gid ts 1%nat false
    | GPPQuery => True
    | GPPRefresh => True
    end.

  #[global]
  Instance gppaction_persistent γ ts gid action :
    Persistent (safe_gppaction γ ts gid action).
  Proof. destruct action; apply _. Defined.

  Theorem wp_GroupPreparer__action (gpp : loc) (rid : u64) γ ts gid :
    {{{ own_gpreparer gpp ts gid γ }}}
      GroupPreparer__action #gpp #rid
    {{{ (action : gppaction), RET #(gppaction_to_u64 action); 
        own_gpreparer gpp ts gid γ ∗
        safe_gppaction γ ts gid action
    }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) action(rid uint64) uint64 {                   @*)
    (*@     // Validate the transaction through fast-path or slow-path.         @*)
    (*@     if gpp.phase == GPP_VALIDATING {                                    @*)
    (*@         // Check if the fast-path response for replica @rid is available. @*)
    (*@         _, fresp := gpp.frespm[rid]                                     @*)
    (*@         if !fresp {                                                     @*)
    (*@             // Have not received the fast-path response.                @*)
    (*@             return GPP_FAST_PREPARE                                     @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    wp_pures.
    wp_apply (wp_GroupPreparer__in _ GPPValidating with "Hgpp").
    iIntros (validting) "Hgpp".
    destruct validting; wp_pures.
    { iNamed "Hgpp".
      iNamed "Hfrespm".
      wp_loadField.
      wp_apply (wp_MapGet with "Hfrespm").
      iIntros (b1 fresp) "[_ Hfrespm]".
      wp_pures.
      destruct fresp; wp_pures; last first.
      { iApply ("HΦ" $! GPPFastPrepare). by iFrame "∗ # %". }

      (*@         // Check if the validation response for replica @rid is available. @*)
      (*@         _, validated := gpp.vdm[rid]                                    @*)
      (*@         if !validated {                                                 @*)
      (*@             // Previous attemp of validation fails; retry.              @*)
      (*@             return GPP_VALIDATE                                         @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      iNamed "Hvdm".
      wp_loadField.
      wp_apply (wp_MapGet with "Hvdm").
      iIntros (b2 validated) "[_ Hvdm]".
      wp_pures.
      destruct validated; wp_pures; last first.
      { iApply ("HΦ" $! GPPValidate). by iFrame "HfrespmP HvdmP ∗ # %". }

      (*@         // Successfully validated (in either fast-path or slow-path).   @*)
      (*@         return GPP_QUERY                                                @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      { iApply ("HΦ" $! GPPQuery). by iFrame "HfrespmP HvdmP ∗ # %". }
    }

    (*@     // Prepare the transaction through slow-path.                       @*)
    (*@     if gpp.phase == GPP_PREPARING {                                     @*)
    (*@         _, prepared := gpp.srespm[rid]                                  @*)
    (*@         if !prepared {                                                  @*)
    (*@             return GPP_PREPARE                                          @*)
    (*@         }                                                               @*)
    (*@         return GPP_QUERY                                                @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_GroupPreparer__in _ GPPPreparing with "Hgpp").
    iIntros (preparing) "Hgpp".
    destruct preparing; wp_pures.
    { iNamed "Hgpp". iNamed "Hsrespm".
      wp_loadField.
      wp_apply (wp_MapGet with "Hsrespm").
      iIntros (b prepared) "[_ Hsrespm]".
      wp_pures.
      destruct prepared; wp_pures; last first.
      { iApply ("HΦ" $! GPPPrepare).
        iDestruct "Hsafe" as "[Hqv Hppsl]".
        iFrame "Hfrespm Hvdm ∗ # %".
        by iFrame "∗ #".
      }
      iApply ("HΦ" $! GPPQuery).
      iFrame "Hfrespm Hvdm ∗ # %".
      by iFrame "∗ #".
    }

    (*@     // Unprepare the transaction through slow-path.                     @*)
    (*@     if gpp.phase == GPP_UNPREPARING {                                   @*)
    (*@         _, unprepared := gpp.srespm[rid]                                @*)
    (*@         if !unprepared {                                                @*)
    (*@             return GPP_UNPREPARE                                        @*)
    (*@         }                                                               @*)
    (*@         return GPP_QUERY                                                @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_GroupPreparer__in _ GPPUnpreparing with "Hgpp").
    iIntros (unpreparing) "Hgpp".
    destruct unpreparing; wp_pures.
    { iNamed "Hgpp". iNamed "Hsrespm".
      wp_loadField.
      wp_apply (wp_MapGet with "Hsrespm").
      iIntros (b prepared) "[_ Hsrespm]".
      wp_pures.
      destruct prepared; wp_pures; last first.
      { iApply ("HΦ" $! GPPUnprepare).
        iFrame "Hfrespm Hvdm ∗ # %".
        by iFrame "∗ #".
      }
      iApply ("HΦ" $! GPPQuery).
      iFrame "Hfrespm Hvdm ∗ # %".
      by iFrame "∗ #".
    }

    (*@     // Backup coordinator exists, just wait for the result.             @*)
    (*@     if gpp.phase == GPP_WAITING {                                       @*)
    (*@         return GPP_QUERY                                                @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_GroupPreparer__in _ GPPWaiting with "Hgpp").
    iIntros (waiting) "Hgpp".
    destruct waiting; wp_pures.
    { iApply ("HΦ" $! GPPQuery). by iFrame. }

    (*@     // The transaction has either prepared, committed, or aborted.      @*)
    (*@     return GPP_REFRESH                                                  @*)
    (*@ }                                                                       @*)
    iApply ("HΦ" $! GPPRefresh). by iFrame.
  Qed.

  Theorem wp_GroupPreparer__getPhase (gpp : loc) phase ts gid γ :
    {{{ own_gpreparer_with_phase gpp phase ts gid γ }}}
      GroupPreparer__getPhase #gpp
    {{{ RET #(gppphase_to_u64 phase); 
        own_gpreparer_with_phase gpp phase ts gid γ ∗
        safe_gpreparer_phase γ ts gid phase
    }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) getPhase() uint64 {                           @*)
    (*@     return gpp.phase                                                    @*)
    (*@ }                                                                       @*)
    iNamed "Hgpp". iNamed "Hphase".
    wp_loadField.
    rewrite Hphase.
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

End program.
