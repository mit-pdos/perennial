From Perennial.program_proof.tulip.invariance Require Import submit.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_repr replica_terminated.
From Perennial.program_proof.tulip.program.txnlog Require Import txnlog.
From Perennial.program_proof.tulip.paxos Require Import base.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ, !paxos_ghostG Σ}.

  Theorem wp_Replica__Abort (rp : loc) (tsW : u64) gid rid γ :
    let ts := uint.nat tsW in
    safe_abort γ ts -∗
    is_replica_plus_txnlog rp gid rid γ -∗
    {{{ True }}}
      Replica__Abort #rp #tsW
    {{{ (ok : bool), RET #ok; True }}}.
  Proof.
    iIntros (ts) "#Hsafe #Hrp".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (rp *Replica) Abort(ts uint64) bool {                              @*)
    (*@     // Query the transaction table. Note that if there's an entry for @ts in @*)
    (*@     // @txntbl, then transaction @ts can only be aborted. That's why we're not @*)
    (*@     // even reading the value of entry.                                 @*)
    (*@     aborted := rp.Terminated(ts)                                        @*)
    (*@                                                                         @*)
    iNamed "Hrp".
    wp_apply (wp_Replica__Terminated with "Hrp").
    iIntros (aborted) "_".
    wp_pures.

    (*@     if aborted {                                                        @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    destruct aborted; wp_pures; first by iApply "HΦ".

    (*@     lsn, term := rp.txnlog.SubmitAbort(ts)                              @*)
    (*@     if lsn == 0 {                                                       @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hrp". iNamed "Htxnlog".
    wp_loadField.
    wp_apply (wp_TxnLog__SubmitAbort with "Htxnlog").
    iNamed "Hinv".
    iInv "Hinv" as "> HinvO" "HinvC".
    iNamed "HinvO".
    iNamed "Hgidrid".
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first apply Hgid.
    iDestruct (group_inv_extract_cpool with "Hgroup") as (cpool) "[Hcpool Hgroup]".
    iApply ncfupd_mask_intro; first solve_ndisj.
    iIntros "Hmask".
    iFrame "Hcpool".
    iIntros "Hcpool".
    iDestruct (group_inv_submit (CmdAbort ts) with "Hsafe Hgroup") as "Hgroup".
    iDestruct (group_inv_merge_cpool with "Hcpool Hgroup") as "Hgroup".
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
    iIntros "!>" (lsn term) "_".
    wp_pures.
    case_bool_decide as Hlsn; wp_pures.
    { by iApply "HΦ". }

    (*@     safe := rp.txnlog.WaitUntilSafe(lsn, term)                          @*)
    (*@     if !safe {                                                          @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@     // We don't really care about the result, since at this point (i.e., after @*)
    (*@     // at least one failed prepares), abort should never fail.          @*)
    (*@     return true                                                         @*)
    (*@ }                                                                       @*)
    wp_loadField.
    wp_apply (wp_TxnLog__WaitUntilSafe with "Htxnlog").
    iIntros (safe) "_".
    wp_pures.
    by destruct safe; wp_pures; iApply "HΦ".
  Qed.

End program.
