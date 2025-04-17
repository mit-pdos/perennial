From Perennial.program_proof.tulip.invariance Require Import submit.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_repr replica_terminated.
From Perennial.program_proof.tulip.program.txnlog Require Import txnlog.
From Perennial.program_proof.tulip.paxos Require Import base.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ, !paxos_ghostG Σ}.

  Theorem wp_Replica__Commit
    (rp : loc) (tsW : u64) (pwrsS : Slice.t) (pwrs : dbmap) gid rid γ :
    let ts := uint.nat tsW in
    safe_commit γ gid ts pwrs -∗
    is_dbmap_in_slice pwrsS pwrs -∗
    is_replica_plus_txnlog rp gid rid γ -∗
    {{{ True }}}
      Replica__Commit #rp #tsW (to_val pwrsS)
    {{{ (ok : bool), RET #ok; True }}}.
  Proof.
    iIntros (ts) "#Hsafe #Hpwrs #Hrp".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (rp *Replica) Commit(ts uint64, pwrs []tulip.WriteEntry) bool {    @*)
    (*@     // Query the transaction table. Note that if there's an entry for @ts in @*)
    (*@     // @txntbl, then transaction @ts can only be committed. That's why we're not @*)
    (*@     // even reading the value of entry.                                 @*)
    (*@     committed := rp.Terminated(ts)                                      @*)
    (*@                                                                         @*)
    iNamed "Hrp".
    wp_apply (wp_Replica__Terminated with "Hrp").
    iIntros (committed) "_".
    wp_pures.

    (*@     if committed {                                                      @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    destruct committed; wp_pures; first by iApply "HΦ".

    (*@     lsn, term := rp.txnlog.SubmitCommit(ts, pwrs)                       @*)
    (*@     if lsn == 0 {                                                       @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hrp". iNamed "Htxnlog".
    wp_loadField.
    wp_apply (wp_TxnLog__SubmitCommit with "Hpwrs Htxnlog").
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
    iDestruct (group_inv_submit (CmdCommit ts pwrs) with "Hsafe Hgroup") as "Hgroup".
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
    (*@     // all the successful prepares), commit should never fail.          @*)
    (*@     return true                                                         @*)
    (*@ }                                                                       @*)
    wp_loadField.
    wp_apply (wp_TxnLog__WaitUntilSafe with "Htxnlog").
    iIntros (safe) "_".
    wp_pures.
    by destruct safe; wp_pures; iApply "HΦ".
  Qed.

End program.
