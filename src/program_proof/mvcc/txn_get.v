From Perennial.program_proof.mvcc Require Import txn_common proph_proof tuple_read_version.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*****************************************************************)
(* func (txn *Txn) Get(key uint64) (uint64, bool)                *)
(*****************************************************************)
Theorem wp_txn__Get txn (k : u64) γ :
  {{{ own_txn txn γ }}}
    Txn__Get #txn #k
  {{{ (v : u64) (found : bool), RET (#v, #found); own_txn txn γ }}}.
Proof.
  iIntros (Φ) "Htxn HΦ".
  iNamed "Htxn".
  iNamed "Himpl".
  wp_call.

  (***********************************************************)
  (* wrbuf := txn.wrbuf                                      *)
  (* valb, del, found := wrbuf.Lookup(key)                   *)
  (***********************************************************)
  wp_loadField.
  wp_pures.
  wp_apply (wp_wrbuf__Lookup with "HwrbufRP").
  iIntros (v d ok) "[HwrbufRP %HLookup]".
  wp_pures.

  (***********************************************************)
  (* if found {                                              *)
  (*     return valb, !del                                   *)
  (* }                                                       *)
  (***********************************************************)
  unfold spec_wrbuf__Lookup in HLookup.
  wp_if_destruct.
  { wp_pures.
    iModIntro.
    iApply "HΦ".
    eauto 20 with iFrame.
  }

  (***********************************************************)
  (* idx := txn.idx                                          *)
  (* tuple := idx.GetTuple(key)                              *)
  (* val, ret := tuple.ReadVersion(txn.tid)                  *)
  (***********************************************************)
  wp_loadField.
  wp_pures.
  wp_apply (wp_index__GetTuple with "HidxRI").
  iIntros (tuple) "#HtupleRI".
  wp_pures.
  wp_loadField.
  wp_apply (wp_tuple__ReadVersion with "HtupleRI [Hactive]").
  { unfold active_tid. eauto with iFrame. }
  iIntros (val ret latch) "[Hactive [Hlocked Hread]]".
  wp_pures.

  (***********************************************************)
  (* proph.ResolveRead(txn.txnMgr.p, txn.tid, key)           *)
  (***********************************************************)
  do 3 wp_loadField.
  wp_apply (wp_ResolveRead γ).
  iInv "Hinv" as "> HinvO" "HinvC".
  iApply ncfupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iNamed "HinvO".
  iExists future.
  iFrame "Hproph".
  iIntros "(%future' & %Hresolve & Hproph)".
  iDestruct (big_sepS_elem_of_acc _ _ k with "Hkeys") as "[Hkey Hkeys]"; first set_solver.
  iMod (tuple_read_safe with "[$Hkey $Hcmt] Hread") as "[[Hkey Hcmt] Htuple]"; first set_solver.
  iDestruct ("Hkeys" with "Hkey") as "Hkeys".
  iMod "Hclose".
  iMod ("HinvC" with "[Hproph Hm Hkeys Hcmt Hnca Hfa Hfci Hfcc]") as "_".
  { (* Close the inv. *) admit. }
  iModIntro.
  iIntros "_".
  wp_pures.

  (***********************************************************)
  (* tuple.Release()                                         *)
  (***********************************************************)
  wp_apply (wp_tuple__Release with "[$Htuple $Hlocked]").
  wp_pures.

  (***********************************************************)
  (* return val, ret == common.RET_SUCCESS                   *)
  (***********************************************************)
  iModIntro.
  iApply "HΦ".
  do 7 iExists _.
  iFrame "Hactive".
  iFrameNamed.
Admitted.

End program.
