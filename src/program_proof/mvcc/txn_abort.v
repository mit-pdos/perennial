From Perennial.program_proof.mvcc Require Import txn_common txnmgr_deactivate.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Theorem wp_txn__Abort txn tid γ τ :
  {{{ own_txn txn tid γ τ }}}
    Txn__Abort #txn
  {{{ RET #(); own_txn_uninit txn γ }}}.
Proof.
  iIntros (Φ) "Htxn HΦ".
  wp_call.

  (***********************************************************)
  (* txn.txnMgr.deactivate(txn.sid, txn.tid)                 *)
  (***********************************************************)
  iNamed "Htxn".
  iNamed "Himpl".
  do 3 wp_loadField.
  wp_apply (wp_txnMgr__deactivate with "HtxnmgrRI Hactive").
  wp_pures.
  iApply "HΦ".
  eauto 20 with iFrame.
Qed.

End program.
