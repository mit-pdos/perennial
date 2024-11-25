From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gpreparer_repr gpreparer_in.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

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

End program.
