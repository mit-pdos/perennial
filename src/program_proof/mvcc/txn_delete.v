From Perennial.program_proof.mvcc Require Import txn_common.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*****************************************************************)
(* func (txn *Txn) Delete(key uint64) bool                       *)
(*****************************************************************)
Theorem wp_txn__Delete txn (k : u64) γ :
  {{{ own_txn txn γ }}}
    Txn__Delete #txn #k
  {{{ (ok : bool), RET #ok; own_txn txn γ }}}.
Proof.
  iIntros (Φ) "Htxn HΦ".
  iNamed "Htxn".
  iNamed "Himpl".
  wp_call.
  
  (***********************************************************)
  (* wrbuf := txn.wrbuf                                      *)
  (* wrbuf.Delete(key)                                       *)
  (***********************************************************)
  wp_loadField.
  wp_pures.
  wp_apply (wp_wrbuf__Delete with "HwrbufRP").
  iIntros "HwrbufRP".
  wp_pures.

  (***********************************************************)
  (* return true                                             *)
  (***********************************************************)
  iModIntro.
  iApply "HΦ".
  eauto 15 with iFrame.
Qed.

End program.
