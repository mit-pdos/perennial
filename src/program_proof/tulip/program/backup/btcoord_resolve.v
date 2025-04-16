From Perennial.program_proof.tulip.invariance Require Import commit.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.txn Require Import proph.
From Perennial.program_proof.tulip.program.backup Require Import btcoord_repr bgcoord_get_pwrs.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_mergeKVMap (mwP mrP : loc) q (mw mr : dbmap) :
    {{{ own_map mwP (DfracOwn 1) mw ∗ own_map mrP q mr }}}
      mergeKVMap #mwP #mrP
    {{{ RET #(); own_map mwP (DfracOwn 1) (mr ∪ mw) ∗ own_map mrP q mr }}}.
  Proof.
    iIntros (Φ) "(Hown1&Hown2) HΦ".
    wp_rec.
    wp_pures.
    wp_apply (wp_MapIter_fold _ _ _ (λ (m : dbmap), own_map mwP (DfracOwn 1) (m ∪ mw))
                with "Hown2 [Hown1]").
    { rewrite left_id_L //. }
    { clear Φ.
      iIntros (m k v Φ) "!> (Hown&%&%) HΦ".
      wp_pures.
      wp_apply (wp_MapInsert _ dbval v _ _ _ _ k with "Hown").
      { rewrite //=. }
      rewrite /map_insert // insert_union_l //.
    }
    iIntros "(H1&H2)".
    wp_pures. by iApply "HΦ"; iFrame.
  Qed.

  Theorem wp_BackupTxnCoordinator__mergeWrites (tcoord : loc) ts wrs γ :
    all_prepared γ ts wrs -∗
    {{{ own_backup_tcoord tcoord ts γ }}}
      BackupTxnCoordinator__mergeWrites #tcoord
    {{{ (wrsP : loc) (valid : bool), RET (#wrsP, #valid);
        own_backup_tcoord tcoord ts γ ∗
        if valid then own_map wrsP (DfracOwn 1) wrs else True
    }}}.
  Proof.
    iIntros "#Hallprep" (Φ) "!> Htcoord HΦ".
    wp_rec.
    iNamed "Htcoord". iNamed "Hptgs". iNamed "Hwrs".
    iDestruct "Hallprep" as "[#Hwrs' _]".
    iDestruct (txn_wrs_agree with "Hwrs' Hwrs") as %->.
    iClear "Hwrs'".

    (*@ func (tcoord *BackupTxnCoordinator) mergeWrites() (tulip.KVMap, bool) { @*)
    (*@     var valid bool = true                                               @*)
    (*@     wrs := make(map[string]tulip.Value)                                 @*)
    (*@                                                                         @*)
    (*@     for _, gid := range(tcoord.ptgs) {                                  @*)
    (*@         // TODO: To prove availability of the write set, we'll have to associate @*)
    (*@         // a coordinator-local one-shot ghost variable to @gcoord.pwrsok. The @*)
    (*@         // persistent resource is first given by @gcoord.WaitUntilPrepareDone, @*)
    (*@         // and then is relayed to @gcoord.Prepare and finally to        @*)
    (*@         // @tcoord.stabilize.                                           @*)
    (*@         gcoord := tcoord.gcoords[gid]                                   @*)
    (*@         pwrs, ok := gcoord.GetPwrs()                                    @*)
    (*@         if ok {                                                         @*)
    (*@             mergeKVMap(wrs, pwrs)                                       @*)
    (*@         } else {                                                        @*)
    (*@             valid = false                                               @*)
    (*@         }                                                               @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     return wrs, valid                                                   @*)
    (*@ }                                                                       @*)

    wp_apply wp_ref_to; first by auto.
    iIntros (l) "Hl".
    wp_pures.
    wp_apply (wp_NewMap).
    iIntros (wrsP) "HwrsP".
    wp_pures.
    wp_loadField.
    wp_pures.
    iNamed "Hptgs".
    iDestruct "Hptgs" as "(#HptgsL&%Hlist&%Hnodup)". subst.
    wp_apply (wp_forSlicePrefix (λ ldone ltodo, ∃ (mdone : dbmap) (valid : bool),
                    own_backup_tcoord_gcoords tcoord (ptgroups (dom wrs)) rk ts γ ∗
                    own_map wrsP (DfracOwn 1) mdone ∗
                    l ↦[boolT] #valid ∗
                    ⌜ if valid then mdone = ∅ else True ⌝
                (* TODO: instead of ∅ should be union of the stuff from ldone *))%I
                with "[] [$Hl $HptgsL $Hgcoords HwrsP]").
    2:{ iExists ∅. by iFrame. }
    { clear Φ.
      iIntros (i x ldone ltodo Heq Φ) "!> H HΦ".
      iDestruct "H" as (dbmap valid) "(Hgcoords&HwrsP&Hl&%Hvalid)".
      wp_pures.
      iNamed "Hgcoords".
      wp_loadField.
      wp_apply (wp_MapGet with "Hgcoords").
      iIntros (? ok) "(%Hmap_get&Hgcoords)".
      wp_pures.
      assert (Hdomx: x ∈ dom gcoords).
      { rewrite Hdomgcoords -Hlist. apply elem_of_list_to_set.
        rewrite -Heq. apply elem_of_app. set_solver. }
      apply elem_of_dom in Hdomx. destruct Hdomx as (v'&Heqv').
      assert (v = v') as <-.
      { replace v with (map_get gcoords x).1; last first.
        { rewrite Hmap_get //. }
        rewrite map_get_val Heqv' //. }
      iDestruct (big_sepM_lookup with "[$]") as "Hgcoordv"; first eauto.
      wp_apply (wp_BackupGroupCoordinator__GetPwrs with "[$]").
      iIntros (pwrsP ok') "Hok'".
      wp_pures.
      wp_if_destruct.
      - admit.
      - wp_store. iModIntro.
        iApply "HΦ".
        iExists _, _. iFrame "∗ # %".
    }
    iFrame.
    iIntros "(_&Hpost)".
    iDestruct "Hpost" as (mdone valid) "(H1&H2&Hl&%Hvalid)".
    wp_pures.
    wp_load.
    destruct valid.
    - wp_pures. admit.
    - wp_pures. iModIntro. iApply "HΦ". iFrame "∗ #". eauto.
  Admitted.

  Theorem wp_BackupTxnCoordinator__resolve tcoord status ts γ :
    status ≠ TxnAborted ->
    safe_txnphase γ ts status -∗
    {{{ own_backup_tcoord tcoord ts γ }}}
      BackupTxnCoordinator__resolve #tcoord #(txnphase_to_u64 status)
    {{{ (ok : bool), RET #ok;
        own_backup_tcoord tcoord ts γ ∗ 
        if ok then is_txn_committed_ex γ ts else True
    }}}.
  Proof.
    iIntros (Hnabt) "#Hsafe".
    iIntros (Φ) "!> Htcoord HΦ".
    wp_rec.

    (*@ func (tcoord *BackupTxnCoordinator) resolve(status uint64) bool {       @*)
    (*@     if status == tulip.TXN_COMMITTED {                                  @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_pures.
    case_bool_decide; wp_pures.
    { destruct status; try done.
      iApply "HΦ".
      by iFrame "∗ #".
    }
    
    (*@     wrs, ok := tcoord.mergeWrites()                                     @*)
    (*@     if !ok {                                                            @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    destruct status; try done. simpl.
    iDestruct "Hsafe" as (wrs) "#Hallprep".
    wp_apply (wp_BackupTxnCoordinator__mergeWrites with "Hallprep Htcoord").
    iIntros (wrsP valid) "[Htcoord Hwrsmg]".
    wp_pures.
    destruct valid; wp_pures; last first.
    { iApply "HΦ". by iFrame "∗ #". }

    (*@     // Logical action: Commit.                                          @*)
    (*@     trusted_proph.ResolveCommit(tcoord.proph, tcoord.ts, wrs)           @*)
    (*@     return true                                                         @*)
    (*@ }                                                                       @*)
    iNamed "Htcoord".
    iNamed "Hts".
    do 2 wp_loadField.
    wp_apply (wp_ResolveCommit with "[$Hwrsmg]"); first done.
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO".
    iDestruct (txnsys_inv_extract_future with "Htxnsys") as (future) "[Hproph Htxnsys]".
    iFrame "Hproph".
    iIntros "(%future' & %Hfuture & Hproph)".
    iMod (txnsys_inv_commit with "Hlnrzed Hallprep Htxnsys Hgroups Hrgs Hkeys")
      as "(Htxnsys & Hgroups & Hrgs & Hkeys & #Hcmt)".
    { by rewrite Hfuture. }
    rewrite Hfuture /=.
    iDestruct (txnsys_inv_merge_future with "Hproph Htxnsys") as "Htxnsys".
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[Htxnsys Hkeys Hgroups Hrgs]") as "_"; first by iFrame.
    iIntros "!> Hwrsmg".
    wp_pures.
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

End program.
