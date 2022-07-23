From Perennial.program_proof.mvcc Require Import txn_common txnmgr_activate.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*****************************************************************)
(* func (txn *Txn) Begin()                                       *)
(*****************************************************************)
Theorem wp_txn__Begin txn γ :
  {{{ own_txn_uninit txn γ }}}
    Txn__Begin #txn
  {{{ RET #(); own_txn txn γ }}}.
Proof.
  iIntros (Φ) "Htxn HΦ".
  iNamed "Htxn".
  wp_call.
  
  (***********************************************************)
  (* tid := txn.txnMgr.activate(txn.sid)                     *)
  (***********************************************************)
  wp_loadField.
  wp_loadField.
  wp_apply (wp_txnMgr__activate with "HtxnmgrRI"); first done.
  rename tid into tid_tmp.
  iIntros (tid) "[Hactive %HtidNZ]".

  (***********************************************************)
  (* txn.tid = tid                                           *)
  (***********************************************************)
  wp_pures.
  wp_storeField.
  
  (***********************************************************)
  (* txn.wrbuf.Clear()                                       *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_wrbuf__Clear with "HwrbufRP").
  iIntros "HwrbufRP".
  wp_pures.
  
  iModIntro.
  iApply "HΦ".
  iExists tid, ∅.
  eauto 15 with iFrame.
Qed.

End program.
