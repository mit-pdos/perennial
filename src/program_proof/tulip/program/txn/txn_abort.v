From Perennial.program_proof.tulip.invariance Require Import abort.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.txn Require Import txn_repr proph txn_reset.
From Perennial.program_proof.tulip.program.gcoord Require Import gcoord_abort.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Txn__abort txn tid rds wrs γ τ :
    is_txn_aborted γ tid -∗
    {{{ own_txn_prepared txn tid rds wrs γ τ ∗ own_wabt_tid γ tid }}}
      Txn__abort #txn
    {{{ RET #(); own_txn_uninit txn γ }}}.
  Proof.
    iIntros "#Habt" (Φ) "!> [Htxn Hwabt] HΦ".
    wp_rec.

    (*@ func (txn *Txn) abort() {                                               @*)
    (*@     trusted_proph.ResolveAbort(txn.proph, txn.ts)                       @*)
    (*@                                                                         @*)
    do 2 iNamed "Htxn".
    do 2 wp_loadField.
    wp_apply (wp_ResolveAbort); first done.
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO".
    iDestruct (txnsys_inv_extract_future with "Htxnsys") as (future) "[Hproph Htxnsys]".
    iFrame "Hproph".
    iIntros "(%future' & %Hfuture & Hproph)".
    iMod (txnsys_inv_abort with "Habt Hwabt Htxnsys") as "Htxnsys".
    { by rewrite Hfuture. }
    rewrite Hfuture /=.
    iDestruct (txnsys_inv_merge_future with "Hproph Htxnsys") as "Htxnsys".
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[Htxnsys Hkeys Hgroups Hrgs]") as "_"; first by iFrame.
    iIntros "!> _".
    wp_pures.

    (*@     ts := txn.ts                                                        @*)
    (*@     for _, gid := range(txn.ptgs) {                                     @*)
    (*@                                                                         @*)
    iNamed "Hptgs".
    do 2 wp_loadField.
    set P := (λ (_ : u64), own_txn_gcoords txn γ)%I.
    wp_apply (wp_forSlice P with "[] [$HptgsL $Hgcoords]").
    { (* Loop body. *)
      clear Φ.

      (*@         gcoord := txn.gcoords[gid]                                      @*)
      (*@                                                                         @*)
      iIntros (i gid Φ) "!> (Hgcoords & %Hinbound & %Hgid) HΦ".
      iNamed "Hgcoords".
      wp_loadField.
      assert (Hin : gid ∈ gids_all).
      { pose proof (subseteq_ptgroups (dom wrs)) as Hdom.
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

      (*@         go func() {                                                     @*)
      (*@             gcoord.Abort(ts)                                            @*)
      (*@         }()                                                             @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      wp_pures.
      iDestruct (big_sepM_lookup with "Hgcoordsabs") as "Hgcoordabs"; first apply Hgetgcoords.
      wp_apply wp_fork.
      { wp_apply (wp_GroupCoordinator__Abort with "[] Hgcoordabs").
        { rewrite Htsword. by iFrame "Habt". }
        done.
      }
      iApply "HΦ".
      iFrame "∗ # %".
    }
    iIntros "[Hgcoods _]". subst P. simpl.
    iAssert (own_txn_ptgs_empty txn)%I with "[$HptgsS]" as "Hptgs".

    (*@     txn.reset()                                                         @*)
    (*@ }                                                                       @*)
    wp_apply (wp_Txn__reset with "Hwrs").
    iIntros "Hwrs".
    wp_pures.
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

  Theorem wp_Txn__abort_in_commit_future txn tid rds wrsphys wrsproph γ τ :
    is_txn_aborted γ tid -∗
    {{{ own_txn_prepared txn tid rds wrsphys γ τ ∗ own_cmt_tmod γ tid wrsproph }}}
      Txn__abort #txn
    {{{ RET #(); False }}}.
  Proof.
    iIntros "#Habt" (Φ) "!> [Htxn Htidc] HΦ".
    wp_rec.

    (*@ func (txn *Txn) abort() {                                               @*)
    (*@     trusted_proph.ResolveAbort(txn.proph, txn.ts)                       @*)
    (*@                                                                         @*)
    do 2 iNamed "Htxn".
    do 2 wp_loadField.
    wp_apply (wp_ResolveAbort); first done.
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO". do 2 iNamed "Htxnsys".
    iFrame "Hproph".
    iIntros "(%future' & %Hfuture & Hproph)".
    (* Prove [tid] must not have committed. *)
    iDestruct (txn_res_lookup with "Hresm Habt") as %Habt.
    iDestruct (cmt_tmod_lookup with "Htidcs Htidc") as %Htidc.
    specialize (Htidcs _ _ Htidc). simpl in Htidcs.
    destruct Htidcs as [Hwc | Hcmt]; last first.
    { by rewrite Hcmt in Habt. }
    specialize (Hcf _ _ Hwc). simpl in Hcf.
    destruct Hcf as (lp & ls & Hfc & _).
    assert (Hhead : head_abort future tid).
    { by rewrite Hfuture. }
    destruct (first_commit_head_abort _ _ _ _ _ Hfc Hhead) as [].

    (*@     ts := txn.ts                                                        @*)
    (*@     for _, gid := range(txn.ptgs) {                                     @*)
    (*@         gcoord := txn.gcoords[gid]                                      @*)
    (*@                                                                         @*)
    (*@         go func() {                                                     @*)
    (*@             gcoord.Abort(ts)                                            @*)
    (*@         }()                                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     txn.reset()                                                         @*)
    (*@ }                                                                       @*)
  Qed.

End program.
