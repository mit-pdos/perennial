From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gpreparer_repr gpreparer_try_resign gpreparer_collect_fast_decision
  gpreparer_try_fast_abort gpreparer_try_become_preparing
  gpreparer_try_become_unpreparing gpreparer_try_fast_prepare
  gpreparer_collect_validation gpreparer_in.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupPreparer__processFastPrepareResult
    (gpp : loc) (rid : u64) (res : rpres) ts gid γ :
    gid ∈ gids_all ->
    rid ∈ rids_all ->
    fast_prepare_outcome γ gid rid ts res -∗
    know_tulip_inv γ -∗
    {{{ own_gpreparer gpp ts gid γ }}}
      GroupPreparer__processFastPrepareResult #gpp #rid #(rpres_to_u64 res)
    {{{ (resend : bool), RET #resend; own_gpreparer gpp ts gid γ }}}.
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
      done.
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
    done.
  Qed.

End program.
