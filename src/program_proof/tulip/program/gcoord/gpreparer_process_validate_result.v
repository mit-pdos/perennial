From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gpreparer_repr gpreparer_try_resign gpreparer_in
  gpreparer_collect_validation gpreparer_try_become_preparing.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupPreparer__processValidateResult
    (gpp : loc) (rid : u64) (res : rpres) ts gid γ :
    gid ∈ gids_all ->
    rid ∈ rids_all ->
    validate_outcome γ gid rid ts res -∗
    know_tulip_inv γ -∗
    {{{ own_gpreparer gpp ts gid γ }}}
      GroupPreparer__processValidateResult #gpp #rid #(rpres_to_u64 res)
    {{{ (resend : bool), RET #resend; own_gpreparer gpp ts gid γ }}}.
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
    done.
  Qed.

End program.
