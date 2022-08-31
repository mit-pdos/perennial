From Perennial.program_proof.mvcc Require Import
     txn_prelude txnmgr_repr txnmgr_get_min_active_tid
     index_proof.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*****************************************************************)
(* func (txnMgr *TxnMgr) gc()                                    *)
(*****************************************************************)
Theorem wp_txnMgr__gc txnmgr γ :
  is_txnmgr txnmgr γ -∗
  {{{ True }}}
    TxnMgr__gc #txnmgr
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Htxnmgr" (Φ) "!> _ HΦ".
  wp_call.

  (***********************************************************)
  (* tidMin := txnMgr.getMinActiveTID()                      *)
  (* if tidMin < config.TID_SENTINEL {                       *)
  (*     txnMgr.idx.DoGC(tidMin)                             *)
  (* }                                                       *)
  (***********************************************************)
  wp_apply (wp_txnMgr__getMinActiveTID with "Htxnmgr").
  iIntros (tid) "#Hminlb".
  wp_pures.
  iNamed "Htxnmgr".
  (*
   * The if condition is for performance, not correctness, so it's
   * completely ignored in the proof.
   *)
  wp_if_destruct.
  { (* Actually do the GC. *)
    wp_loadField.
    wp_apply (wp_index__DoGC with "HidxRI Hminlb").
    wp_pures.
    by iApply "HΦ".
  }
  (* Do nothing as no active txns. *)
  by iApply "HΦ".
Qed.

(*****************************************************************)
(* func (txnMgr *TxnMgr) ActivateGC()                            *)
(*****************************************************************)
Theorem wp_txnMgr__ActivateGC txnmgr γ :
  is_txnmgr txnmgr γ -∗
  {{{ True }}}
    TxnMgr__ActivateGC #txnmgr
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Htxnmgr" (Φ) "!> _ HΦ".
  wp_call.

  (***********************************************************)
  (* go func() {                                             *)
  (*     for {                                               *)
  (*         txnMgr.gc()                                     *)
  (*         machine.Sleep(uint64(100) * uint64(1000000))    *)
  (*     }                                                   *)
  (* }()                                                     *)
  (***********************************************************)
  wp_apply wp_fork.
  { (* Forked process. *)
    wp_pures.
    wp_apply (wp_forBreak (λ _, True)%I); last done.
    clear Φ.
    iIntros (Φ) "!> _ HΦ".
    wp_pures.
    wp_apply (wp_txnMgr__gc with "Htxnmgr").
    wp_apply wp_Sleep.
    wp_pures.
    by iApply "HΦ".
  }
  wp_pures.
  by iApply "HΦ".
Qed.

End program.
