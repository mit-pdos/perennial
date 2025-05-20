From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import gpreparer_repr.
From Perennial.program_proof.tulip.program.backup Require Import bgpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_mkBackupGroupPreparer (nrps : u64) rk ts cid gid γ :
    uint.nat nrps = size rids_all ->
    {{{ own_replica_backup_token γ cid.1 cid.2 ts rk gid }}}
      mkBackupGroupPreparer #nrps
    {{{ (gpp : loc), RET #gpp; own_backup_gpreparer gpp rk ts cid gid γ }}}.
  Proof.
    iIntros (Hnrps Φ) "Htoken HΦ".
    wp_rec.

    (*@ func mkBackupGroupPreparer(nrps uint64) *BackupGroupPreparer {          @*)
    (*@     gpp := &BackupGroupPreparer{                                        @*)
    (*@         nrps   : nrps,                                                  @*)
    (*@         phase  : BGPP_INQUIRING,                                        @*)
    (*@         pwrsok : false,                                                 @*)
    (*@         pps    : make(map[uint64]tulip.PrepareProposal),                @*)
    (*@         vdm    : make(map[uint64]bool),                                 @*)
    (*@         srespm : make(map[uint64]bool),                                 @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_NewMap u64 ppsl).
    iIntros (pps) "Hpps".
    wp_apply (wp_NewMap u64 bool).
    iIntros (vdmP) "Hvdm".
    wp_apply (wp_NewMap u64 bool).
    iIntros (srespmP) "Hsrespm".
    wp_apply (wp_allocStruct).
    { by auto 10. }
    iIntros (gpp) "Hgpp".
    wp_pures.

    (*@     return gpp                                                          @*)
    (*@ }                                                                       @*)
    iModIntro.
    iApply "HΦ".
    iDestruct (struct_fields_split with "Hgpp") as "Hgpp".
    iNamed "Hgpp".
    iExists BGPPInquiring, ∅.
    iFrame "nrps phase pwrsok pwrs pps vdm srespm ∗".
    iSplit; first done.
    iSplit; first done.
    iSplit.
    { by iExists ∅. }
    iSplit.
    { iExists ∅.
      iSplit; first by iApply big_sepM_empty.
      iSplit; first by iApply big_sepM_empty.
      rewrite dom_empty_L.
      iSplit; first by iApply big_sepS_empty.
      iPureIntro.
      split; first done.
      split; first done.
      apply map_Forall2_empty.
    }
    iSplit.
    { rewrite /validation_responses dom_empty_L.
      iSplit; first by iApply big_sepS_empty.
      done.
    }
    done.
  Qed.

End program.
