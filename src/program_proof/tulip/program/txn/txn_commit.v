From Perennial.program_proof.tulip.invariance Require Import commit.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.txn Require Import txn_repr proph txn_reset.
From Perennial.program_proof.tulip.program.gcoord Require Import gcoord_commit.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Txn__commit txn tid rds wrsphys wrsproph γ τ :
    is_lnrz_tid γ tid -∗
    all_prepared γ tid wrsphys -∗
    {{{ own_txn_prepared txn tid rds wrsphys γ τ ∗ own_cmt_tmod γ tid wrsproph }}}
      Txn__commit #txn
    {{{ RET #(); own_txn_uninit txn γ ∗ ⌜wrsphys = wrsproph⌝ }}}.
  Proof.
    iIntros "#Hlnrzed #Hprep" (Φ) "!> [Htxn Htidc] HΦ".
    wp_rec.

    (*@ func (txn *Txn) commit() {                                              @*)
    (*@     ResolveCommit(txn.proph, txn.ts, txn.wrs)                           @*)
    (*@                                                                         @*)
    do 2 iNamed "Htxn". iNamed "Hwrs".
    do 3 wp_loadField.
    wp_apply (wp_ResolveCommit with "[$Hwrsp]"); first done.
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO".
    iDestruct (txnsys_inv_extract_future with "Htxnsys") as (future) "[Hproph Htxnsys]".
    iFrame "Hproph".
    iIntros "(%future' & %Hfuture & Hproph)".
    iMod (txnsys_inv_commit with "Hlnrzed Hprep Htxnsys Hgroups Hrgs Hkeys")
      as "(Htxnsys & Hgroups & Hrgs & Hkeys & #Hcmt)".
    { by rewrite Hfuture. }
    iAssert (⌜wrsphys = wrsproph⌝)%I as %Heq.
    { do 2 iNamed "Htxnsys".
      iDestruct (txn_res_lookup with "Hresm Hcmt") as %Hwrsc.
      iDestruct (elem_of_committed_partitioned_tids with "Hpart") as %[Hnotinwc Hnotinwa].
      { by eauto. }
      iDestruct (cmt_tmod_lookup with "Htidcs Htidc") as %Htidc.
      specialize (Htidcs _ _ Htidc). simpl in Htidcs.
      (* Prove [resm !! tid = Some (ResCommitted wrs)]. *)
      destruct Htidcs as [Htmodcs | Hresm].
      { by rewrite not_elem_of_dom Htmodcs in Hnotinwc. }
      rewrite Hresm in Hwrsc. symmetry in Hwrsc. inv Hwrsc.
      done.
    }
    (* Close the invariant. *)
    rewrite Hfuture /=.
    iDestruct (txnsys_inv_merge_future with "Hproph Htxnsys") as "Htxnsys".
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[Htxnsys Hkeys Hgroups Hrgs]") as "_"; first by iFrame.
    iIntros "!> Hwrsp".
    wp_pures.
    do 2 wp_loadField.

    (*@     ts := txn.ts                                                        @*)
    (*@     for _, gid := range(txn.ptgs) {                                     @*)
    (*@                                                                         @*)
    iNamed "Hptgs". iNamed "Hwrs".
    iDestruct "Hpwrsm" as "#Hpwrsm".
    wp_loadField.
    set P := (λ (_ : u64),
                "HpwrsmP" ∷ own_map wrsP (DfracOwn 1) pwrsmP ∗
                "Hgcoords" ∷ own_txn_gcoords txn γ)%I.
    wp_apply (wp_forSlice P with "[] [$HptgsL $HpwrsmP $Hgcoords]").
    { (* Loop body. *)
      clear Φ.

      (*@         gcoord := txn.gcoords[gid]                                      @*)
      (*@         pwrs := txn.wrs[gid]                                            @*)
      (*@                                                                         @*)
      iIntros (i gid Φ) "!> (HP & %Hinbound & %Hgid) HΦ".
      iNamed "HP". iNamed "Hgcoords".
      wp_loadField.
      assert (Hin : gid ∈ gids_all).
      { pose proof (subseteq_ptgroups (dom wrsphys)) as Hdom.
        apply list_elem_of_lookup_2 in Hgid.
        clear -Hdom Hgid HptgsL.
        set_solver.
      }
      wp_apply (wp_MapGet with "Hgcoords").
      iIntros (gcoordP ok) "[%Hgetgcoords Hgcoords]".
      destruct ok; last first.
      { apply map_get_false in Hgetgcoords as [Hnone _].
        by rewrite -not_elem_of_dom Hdomgcoords in Hnone.
      }
      apply map_get_true in Hgetgcoords.
      wp_apply (wp_MapGet with "HpwrsmP").
      iIntros (pwrsP ok) "[%Hgetwrs HpwrsmP]".
      destruct ok; last first.
      { apply map_get_false in Hgetwrs as [Hnotin _].
        by rewrite -not_elem_of_dom Hdomwrs in Hnotin.
      }
      apply map_get_true in Hgetwrs.
      iAssert (⌜is_Some (pwrsm !! gid)⌝)%I as %[pwrs Hpwrs].
      { iDestruct (big_sepM2_dom with "Hpwrsm") as %Hdom.
        iPureIntro.
        by rewrite -elem_of_dom -Hdom elem_of_dom.
      }
      iDestruct (big_sepM2_lookup_acc with "Hpwrsm") as "[Hpwrs HpwrsmC]"; [done | done |].

      (*@         go func() {                                                     @*)
      (*@             gcoord.Commit(ts, pwrs)                                     @*)
      (*@         }()                                                             @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      wp_pures.
      iDestruct (big_sepM_lookup with "Hgcoordsabs") as "Hgcoordabs"; first apply Hgetgcoords.
      wp_apply wp_fork.
      { wp_apply (wp_GroupCoordinator__Commit with "[] Hgcoordabs Hpwrs").
        { rewrite Htsword.
          iFrame "Hcmt Htxnwrs".
          iPureIntro.
          assert (Hinptgs : gid ∈ ptgroups (dom wrsphys)).
          { rewrite -HptgsL elem_of_list_to_set list_elem_of_lookup. by eauto. }
          specialize (Hwrsg _ _ Hpwrs).
          done.
        }
        by iIntros "_".
      }
      iApply "HΦ".
      iFrame "∗ # %".
    }
    iIntros "[HP _]".
    iNamed "HP". clear P.
    iAssert (own_txn_ptgs_empty txn)%I with "[$HptgsS]" as "Hptgs".

    (*@     txn.reset()                                                         @*)
    (*@ }                                                                       @*)
    iAssert (own_txn_wrs txn DfracDiscarded wrsphys)%I
      with "[$HwrsP $HwrspP $Hwrsp $HpwrsmP]" as "Hwrs".
    { iFrame "# %". }
    wp_apply (wp_Txn__reset with "Hwrs").
    iIntros "Hwrs".
    wp_pures.
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

  Theorem wp_Txn__commit_in_abort_future txn tid rds wrs γ τ :
    is_lnrz_tid γ tid -∗
    all_prepared γ tid wrs -∗
    {{{ own_txn_prepared txn tid rds wrs γ τ ∗ own_wabt_tid γ tid }}}
      Txn__commit #txn
    {{{ RET #(); False }}}.
  Proof.
    iIntros "#Hlnrzed #Hprep" (Φ) "!> [Htxn Hwabt] HΦ".
    wp_rec.

    (*@ func (txn *Txn) commit() {                                              @*)
    (*@     trusted_proph.ResolveCommit(txn.proph, txn.ts, txn.wrsp)            @*)
    (*@                                                                         @*)
    do 2 iNamed "Htxn". iNamed "Hwrs".
    do 3 wp_loadField.
    wp_apply (wp_ResolveCommit with "[$Hwrsp]"); first done.
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO".
    iDestruct (txnsys_inv_extract_future with "Htxnsys") as (future) "[Hproph Htxnsys]".
    iFrame "Hproph".
    iIntros "(%future' & %Hfuture & Hproph)".
    iMod (txnsys_inv_commit with "Hlnrzed Hprep Htxnsys Hgroups Hrgs Hkeys")
      as "(Htxnsys & Hgroups & Hrgs & Hkeys & Hcmt)".
    { by rewrite Hfuture. }
    (* Obtain contradiction. *)
    do 2 iNamed "Htxnsys".
    iDestruct (txn_res_lookup with "Hresm Hcmt") as %Hcmt.
    iDestruct (wabt_tid_elem_of with "Htidas Hwabt") as %Hwabt.
    rewrite -Htidas in Hwabt.
    iDestruct (elem_of_tmodas_partitioned_tids with "Hpart") as %[_ Hnotin].
    { apply Hwabt. }
    by specialize (Hnotin _ Hcmt).

    (*@     ts := txn.ts                                                        @*)
    (*@     wrs := txn.wrs                                                      @*)
    (*@     for _, gid := range(txn.ptgs) {                                     @*)
    (*@         gcoord := txn.gcoords[gid]                                      @*)
    (*@         pwrs := wrs[gid]                                                @*)
    (*@                                                                         @*)
    (*@         go func() {                                                     @*)
    (*@             gcoord.Commit(ts, pwrs)                                     @*)
    (*@         }()                                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     txn.reset()                                                         @*)
    (*@ }                                                                       @*)
  Qed.

End program.
