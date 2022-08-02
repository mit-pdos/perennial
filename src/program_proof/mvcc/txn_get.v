From Perennial.program_proof.mvcc Require Import txn_common proph_proof tuple_read_version tuple_release.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*****************************************************************)
(* func (txn *Txn) Get(key uint64) (uint64, bool)                *)
(*****************************************************************)
Theorem wp_txn__Get txn tid view (k : u64) dbv γ τ :
  {{{ own_txn txn tid view γ τ ∗ txnmap_ptsto τ k dbv }}}
    Txn__Get #txn #k
  {{{ (v : u64) (found : bool), RET (#v, #found);
      own_txn txn tid view γ τ ∗ txnmap_ptsto τ k dbv ∗ ⌜dbv = to_dbval found v⌝
  }}}.
Proof.
  iIntros (Φ) "[Htxn Hptsto] HΦ".
  iNamed "Htxn".
  iNamed "Himpl".
  wp_call.

  (***********************************************************)
  (* wrbuf := txn.wrbuf                                      *)
  (* valb, wr, found := wrbuf.Lookup(key)                    *)
  (***********************************************************)
  wp_loadField.
  wp_pures.
  wp_apply (wp_wrbuf__Lookup with "HwrbufRP").
  iIntros (v d ok) "[HwrbufRP %Hlookup]".
  wp_pures.

  (***********************************************************)
  (* if found {                                              *)
  (*     return valb, wr                                     *)
  (* }                                                       *)
  (***********************************************************)
  unfold spec_wrbuf__Lookup in Hlookup.
  wp_if_destruct.
  { wp_pures.
    iModIntro.
    iApply "HΦ".
    iDestruct (txnmap_lookup with "Htxnmap Hptsto") as "%Hlookup'".
    apply (lookup_union_Some_l _ view) in Hlookup.
    rewrite Hlookup' in Hlookup.
    inversion_clear Hlookup.
    iSplitR "Hptsto".
    { eauto 25 with iFrame. }
    by iFrame.
  }

  (***********************************************************)
  (* idx := txn.idx                                          *)
  (* tuple := idx.GetTuple(key)                              *)
  (* val, found := tuple.ReadVersion(txn.tid)                *)
  (***********************************************************)
  wp_loadField.
  wp_pures.
  wp_apply (wp_index__GetTuple with "HidxRI").
  iIntros (tuple) "#HtupleRI".
  wp_pures.
  wp_loadField.
  wp_apply (wp_tuple__ReadVersion with "HtupleRI [Hactive]").
  { unfold active_tid. eauto with iFrame. }
  iIntros (val found latch) "[Hactive [Hlocked Hread]]".
  wp_pures.

  (***********************************************************)
  (* proph.ResolveRead(txn.txnMgr.p, txn.tid, key)           *)
  (***********************************************************)
  do 3 wp_loadField.
  wp_apply (wp_ResolveRead γ); first auto.
  iInv "Hinv" as "> HinvO" "HinvC".
  iApply ncfupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iNamed "HinvO".
  iExists future.
  iFrame "Hproph".
  iIntros "(%future' & %Hhead & Hproph)".
  (* Extend the physical tuple. *)
  iMod (tuple_read_safe with "Hkeys Hcmt Hread") as "(Hkeys & Hcmt & Htuple & Hptuple)"; first set_solver.
  (* Deduce eq between logical and physical read. *)
  iDestruct (big_sepS_elem_of_acc _ _ k with "Hkeys") as "[Hkey Hkeys]"; first set_solver.
  iDestruct (txnmap_lookup with "Htxnmap Hptsto") as "%Hlookup'".
  rewrite lookup_union_r in Hlookup'; last auto.
  iDestruct (big_sepM_lookup_acc with "Hltuples") as "[Hltuple Hltuples]"; first apply Hlookup'.
  rewrite Etid.
  iDestruct (ltuple_ptuple_ptsto_eq with "[Hkey] Hltuple Hptuple") as "%Heq".
  { iNamed "Hkey".
    unfold tuple_auth_prefix.
    unfold tuple_mods_rel in Htmrel.
    destruct Htmrel as (diff & _ & [H _]).
    do 2 iExists _.
    iFrame.
    iPureIntro.
    by exists diff.
  }
  (* Close things. *)
  iDestruct ("Hkeys" with "Hkey") as "Hkeys".
  iDestruct ("Hltuples" with "Hltuple") as "Hltuples".
  iMod "Hclose".
  iMod ("HinvC" with "[Hproph Hm Hts Hkeys Hcmt Hnca Hfa Hfci Hfcc]") as "_".
  { (* Close the inv. *)
    iNext. unfold mvcc_inv_sst_def.
    do 7 iExists _.
    iExists (past ++ [EvRead tid k]), future'.
    iDestruct (nca_inv_any_action with "Hnca") as "Hnca"; first apply Hhead.
    iDestruct (fa_inv_diff_action  with "Hfa")  as "Hfa";  [apply Hhead | done |].
    iDestruct (fci_inv_diff_action with "Hfci") as "Hfci"; [apply Hhead | done |].
    iDestruct (fcc_inv_diff_action with "Hfcc") as "Hfcc"; [apply Hhead | done |].
    iDestruct (cmt_inv_diff_action with "Hcmt") as "Hcmt"; [apply Hhead | done |].
    iFrame.
  }
  iModIntro.
  iIntros "_".
  wp_pures.

  (***********************************************************)
  (* tuple.Release()                                         *)
  (***********************************************************)
  wp_apply (wp_tuple__Release with "[$Htuple $Hlocked]").
  wp_pures.

  (***********************************************************)
  (* return val, found                                       *)
  (***********************************************************)
  iModIntro.
  iApply "HΦ".
  iSplitR "Hptsto".
  { iExists _.
    iFrame "Hltuples Htxnmap".
    iSplitL; last done.
    do 6 iExists _.
    iFrame "Hactive Htid Hsid Hwrbuf HwrbufRP".
    by iFrame "#".
  }
  by iFrame "Hptsto".
Qed.

End program.
