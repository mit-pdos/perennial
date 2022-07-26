From Perennial.program_proof.mvcc Require Import txn_common.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*****************************************************************)
(* func (txn *Txn) Delete(key uint64) bool                       *)
(*****************************************************************)
Theorem wp_txn__Delete txn (k : u64) dbv γ τ :
  {{{ own_txn txn γ τ ∗ txnmap_ptsto τ k dbv }}}
    Txn__Delete #txn #k
  {{{ (ok : bool), RET #ok;
      own_txn txn γ τ ∗ txnmap_ptsto τ k Nil
  }}}.
Proof.
  iIntros (Φ) "[Htxn Hptsto] HΦ".
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
  iMod (txnmap_update Nil with "Htxnmap Hptsto") as "[Htxnmap Hptsto]".

  (***********************************************************)
  (* return true                                             *)
  (***********************************************************)
  iModIntro.
  iApply "HΦ".
  iSplitR "Hptsto".
  { unfold own_txn.
    rewrite insert_union_l.
    set mods' := (<[ _ := _ ]> mods).
    iExists _, view, mods'.
    eauto 20 with iFrame.
  }
  iFrame.
Qed.

End program.
