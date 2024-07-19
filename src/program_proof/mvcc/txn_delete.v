From Perennial.program_proof.mvcc Require Import
     txn_prelude txn_repr
     wrbuf_proof.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*****************************************************************)
(* func (txn *Txn) Delete(key uint64) bool                       *)
(*****************************************************************)
Theorem wp_txn__Delete txn tid view (k : u64) dbv γ τ :
  {{{ own_txn txn tid view γ τ ∗ txnmap_ptsto τ k dbv }}}
    Txn__Delete #txn #k
  {{{ (ok : bool), RET #ok;
      own_txn txn tid view γ τ ∗ txnmap_ptsto τ k Nil
  }}}.
Proof.
  iIntros (Φ) "[Htxn Hptsto] HΦ".
  iNamed "Htxn".
  iNamed "Himpl".
  wp_rec. wp_pures.
  iDestruct (txnmap_lookup with "Htxnmap Hptsto") as "%Hlookup".
  
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
    iExists _, mods'.
    iFrame "Hltuples Htxnmap Hwrbuf HwrbufRP".
    iSplitL; first eauto 20 with iFrame.
    iPureIntro.
    destruct (mods !! k) eqn:E.
    - rewrite dom_insert_lookup_L; auto.
    - rewrite lookup_union_r in Hlookup; last auto.
      rewrite dom_insert_L.
      apply elem_of_dom_2 in Hlookup.
      set_solver.
  }
  iFrame.
Qed.

End program.
