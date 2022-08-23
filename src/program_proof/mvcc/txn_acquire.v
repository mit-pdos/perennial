From Perennial.program_proof.mvcc Require Import
     txn_prelude txn_repr
     wrbuf_repr wrbuf_open_tuples.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*****************************************************************)
(* func (txn *Txn) acquire() bool                                *)
(*****************************************************************)
Theorem wp_txn__acquire txn tid view γ τ :
  {{{ own_txn txn tid view γ τ }}}
    Txn__acquire #txn
  {{{ (ok : bool), RET #ok;
      if ok then own_txn_ready txn tid view γ τ else own_txn txn tid view γ τ
  }}}.
Proof.
  iIntros (Φ) "Htxn HΦ".
  wp_call.

  (***********************************************************)
  (* ok := txn.wrbuf.OpenTuples(txn.tid, txn.idx)            *)
  (* return ok                                               *)
  (***********************************************************)
  iNamed "Htxn".
  iNamed "Himpl".
  do 3 wp_loadField.
  wp_apply (wp_wrbuf__OpenTuples with "HidxRI [$HwrbufRP $Hactive]").
  iIntros (ok) "[Hactive HwrbufRP]".
  wp_pures.
  iApply "HΦ".
  destruct ok.
  { (* Case success. *)
    iDestruct "HwrbufRP" as (tpls) "[HwrbufRP Htpls]".
    do 3 iExists _.
    rewrite Etid.
    iFrame "Htxnmap Htpls HwrbufRP Hltuples".
    eauto 20 with iFrame.
  }
  { (* Case failure. *)
    do 2 iExists _.
    iFrame "Htxnmap HwrbufRP Hltuples".
    eauto 20 with iFrame.
  }
Qed.

End program.
