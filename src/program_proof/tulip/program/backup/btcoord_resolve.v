From Perennial.program_proof.tulip.invariance Require Import commit.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.txn Require Import proph.
From Perennial.program_proof.tulip.program.backup Require Import btcoord_repr bgcoord_get_pwrs.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Lemma foldl_union_lookup_init wrs l0 init k :
    (∀ x, x ∈ l0 → wrs_group x wrs !! k = None) →
    foldl (λ (acc : dbmap) (x : w64), wrs_group x wrs ∪ acc) init l0 !! k = init !! k.
  Proof.
    revert init.
    induction l0 as [| x l0 IH] => init Hall //=.
    rewrite IH.
    - rewrite lookup_union_r; auto. apply Hall; set_solver.
    - intros. apply Hall. set_solver.
  Qed.

  Lemma foldl_union_lookup_None wrs l0 init k :
    (init !! k = None) →
    (∀ x, x ∈ l0 → wrs_group x wrs !! k = None) →
    foldl (λ (acc : dbmap) (x : w64), wrs_group x wrs ∪ acc) init l0 !! k = None.
  Proof. intros Hinit Hall. rewrite foldl_union_lookup_init //. Qed.

  Lemma foldl_union_lookup_Some_1 wrs x l0 init k v :
    wrs_group x wrs !! k = Some v →
    NoDup l0 →
    x ∈ l0 →
    (init !! k = None) →
    foldl (λ (acc : dbmap) (x : w64), wrs_group x wrs ∪ acc) init l0 !! k = Some v.
  Proof.
    revert init.
    induction l0 as [| y l0 IH] => init Hlookup Hnodup Helem Hinit.
    { set_solver. }
    apply NoDup_cons in Hnodup as (?&?).
    set_unfold in Helem. destruct Helem; subst.
    - simpl. rewrite foldl_union_lookup_init.
      { rewrite lookup_union_l //. }
      intros x' Hin'.
      apply lookup_wrs_group_Some in Hlookup as (?&Hkey).
      apply lookup_wrs_group_None. right.
      intros Heq. congruence.
    - simpl. apply IH; eauto.
      apply lookup_union_None; split; auto.
      apply lookup_wrs_group_Some in Hlookup as (?&Hkey).
      apply lookup_wrs_group_None. right.
      intros Heq. congruence.
  Qed.

  Lemma wrs_lookup_Some_elem_ptgroups wrs k v:
    valid_wrs wrs →
    wrs !! k = Some v → key_to_group k ∈ ptgroups (dom wrs).
  Proof.
    intros Hval Hlook.
    rewrite /key_to_group/ptgroups/key_to_group.
    apply: (elem_of_map_2 _ _ k).
    apply elem_of_dom; eauto.
  Qed.

  Lemma foldl_wrs_group wrs l0 :
    NoDup l0 →
    valid_wrs wrs →
    list_to_set l0 = ptgroups (dom wrs) →
    foldl (λ (acc : dbmap) (x : w64), wrs_group x wrs ∪ acc) ∅ l0 = wrs.
  Proof.
    intros HNoDup Hvalid Hlist.
    apply map_leibniz => k.
    destruct (wrs !! k) eqn:Hk; last first.
    - rewrite Hk. rewrite foldl_union_lookup_None; auto.
      intros x Hin.
      apply lookup_wrs_group_None. auto.
    - rewrite Hk. apply leibniz_equiv_iff.
      apply (foldl_union_lookup_Some_1 _ (key_to_group k)); auto.
      { apply lookup_wrs_group_Some; auto. }
      { apply wrs_lookup_Some_elem_ptgroups in Hk; auto.
        rewrite -Hlist in Hk.
        apply elem_of_list_to_set in Hk. auto. }
  Qed.

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
                    ⌜ if valid then mdone = foldl (λ acc x, wrs_group x wrs ∪ acc) ∅ ldone else True ⌝
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
      - iDestruct "Hok'" as (pwrs) "(Hown&Hsafe)".
        wp_apply (wp_mergeKVMap with "[$]").
        iIntros "(HwrsP&Hown)".
        iApply "HΦ". iExists _, _. iFrame "∗ #".
        iSplit; first eauto.
        destruct valid; last done.
        iNamed "Hsafe".
        iDestruct "Hsafe" as "(Hsafe&%Hvalid')".
        destruct Hvalid' as (?&?&?&->).
        iDestruct (txn_wrs_agree with "Hwrs Hsafe") as %->.
        rewrite foldl_snoc. iPureIntro; congruence.
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
    - wp_pures.
      iApply "HΦ".
      iModIntro; iFrame "∗ #".
      iSplit; first by eauto.
      iExactEq "H2".
      f_equal.
      rewrite Hvalid.
      by apply foldl_wrs_group.
    - wp_pures. iModIntro. iApply "HΦ". iFrame "∗ #". eauto.
  Qed.

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
