From Perennial.program_proof.tulip.invariance Require Import cancel.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.txn Require Import txn_repr proph txn_reset.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Txn__cancel txn tid rds γ τ :
    {{{ own_txn txn tid rds γ τ ∗ own_wabt_tid γ tid ∗ own_txn_reserved_wrs γ tid }}}
      Txn__cancel #txn
    {{{ RET #(); own_txn_uninit txn γ }}}.
  Proof.
    iIntros (Φ) "(Htxn & Habt & Hwrsexcl) HΦ".
    wp_rec.

    (*@ func (txn *Txn) cancel() {                                              @*)
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
    iMod (txnsys_inv_cancel with "Habt Hwrsexcl Htxnsys") as "Htxnsys".
    { by rewrite Hfuture. }
    rewrite Hfuture /=.
    iDestruct (txnsys_inv_merge_future with "Hproph Htxnsys") as "Htxnsys".
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[Htxnsys Hkeys Hgroups Hrgs]") as "_"; first by iFrame.
    iIntros "!> _".

    (*@     txn.reset()                                                         @*)
    (*@ }                                                                       @*)
    wp_apply (wp_Txn__reset with "Hwrs").
    iIntros "Hwrs".
    wp_pures.
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

  Theorem wp_Txn__cancel_in_commit_future txn tid rds γ τ :
    {{{ own_txn txn tid rds γ τ ∗ (∃ m, own_cmt_tmod γ tid m) ∗ own_txn_reserved_wrs γ tid }}}
      Txn__cancel #txn
    {{{ RET #(); False }}}.
  Proof.
    iIntros (Φ) "(Htxn & [%m Htidc] & Hwrsexcl) HΦ".
    wp_rec.

    (*@ func (txn *Txn) cancel() {                                              @*)
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
    (* Obtain [tmods !! tid = Some m]. *)
    iDestruct (cmt_tmod_lookup with "Htidcs Htidc") as %Htidc.
    specialize (Htidcs _ _ Htidc). simpl in Htidcs.
    (* Prove [resm !! tid = Some (ResCommitted m)] impossible, i.e., [tid] not committed yet. *)
    destruct Htidcs as [Htmodcs | Hcmt]; last first.
    { iDestruct (big_sepM_lookup with "Hvr") as "Hvc"; first apply Hcmt.
      iDestruct "Hvc" as "[Hwrsrcpt _]".
      (* Contradicting facts:
       * 1. Txn still owns exclusively the write-set (which is true before prepare).
       * Represented as [Hwrsexcl] from the precondition.
       * 2. Txn has set the write-set and given up the ability to change
       * (which is true after prepare). Represented as [Hwrsrcpt].
       *)
      by iDestruct (txn_oneshot_wrs_agree with "Hwrsexcl Hwrsrcpt") as %Hcontra.
    }
    (* Obtain [first_commit]. *)
    specialize (Hcf _ _ Htmodcs). simpl in Hcf.
    destruct Hcf as (lp & ls & Hfc & _).
    (* Obtain contradiction from [first_commit] and [head_abort]. *)
    assert (Hha : head_abort future tid).
    { by rewrite Hfuture /head_abort /=. }
    destruct (first_commit_head_abort _ _ _ _ _ Hfc Hha).

    (*@     txn.reset()                                                         @*)
    (*@ }                                                                       @*)
  Qed.

End program.
