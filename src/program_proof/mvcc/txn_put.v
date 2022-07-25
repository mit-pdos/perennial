From Perennial.program_proof.mvcc Require Import txn_common.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*****************************************************************)
(* func (txn *Txn) Put(key, val uint64)                          *)
(*****************************************************************)
Theorem wp_txn__Put txn (k : u64) (v : u64) γ :
  {{{ own_txn txn γ }}}
    Txn__Put #txn #k #v
  {{{ RET #(); own_txn txn γ }}}.
Proof.
  iIntros (Φ) "Htxn HΦ".
  iNamed "Htxn".
  iNamed "Himpl".
  wp_call.
  
  (***********************************************************)
  (* wrbuf := txn.wrbuf                                      *)
  (* wrbuf.Put(key, val)                                     *)
  (***********************************************************)
  wp_loadField.
  wp_pures.
  wp_apply (wp_wrbuf__Put with "HwrbufRP").
  iIntros "HwrbufRP".
  wp_pures.

  iModIntro.
  iApply "HΦ".
  eauto 20 with iFrame.
Qed.

End program.
