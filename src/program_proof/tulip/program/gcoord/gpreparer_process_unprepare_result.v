From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gpreparer_repr gpreparer_try_resign gpreparer_in gpreparer_cquorum.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

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

End program.
