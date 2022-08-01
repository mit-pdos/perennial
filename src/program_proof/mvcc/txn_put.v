From Perennial.program_proof.mvcc Require Import txn_common.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*****************************************************************)
(* func (txn *Txn) Put(key, val uint64)                          *)
(*****************************************************************)
Theorem wp_txn__Put txn tid view (k : u64) dbv v γ τ :
  {{{ own_txn txn tid view γ τ ∗ txnmap_ptsto τ k dbv }}}
    Txn__Put #txn #k #v
  {{{ RET #();
      own_txn txn tid view γ τ ∗ txnmap_ptsto τ k (Value v)
  }}}.
Proof.
  iIntros (Φ) "[Htxn Hptsto] HΦ".
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
  iMod (txnmap_update (Value v) with "Htxnmap Hptsto") as "[Htxnmap Hptsto]".

  iModIntro.
  iApply "HΦ".
  iSplitR "Hptsto".
  { unfold own_txn.
    rewrite insert_union_l.
    set mods' := (<[ _ := _ ]> mods).
    iExists mods'.
    eauto 20 with iFrame.
  }
  iFrame.
Qed.

End program.
