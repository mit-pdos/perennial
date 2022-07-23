From Perennial.program_proof.mvcc Require Import txn_common.

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
    eauto 15 with iFrame.
  }

  (***********************************************************)
  (* idx := txn.idx                                          *)
  (* tuple := idx.GetTuple(key)                              *)
  (* val, ret := tuple.ReadVersion(txn.tid)                  *)
  (* return val, ret == common.RET_SUCCESS                   *)
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
  iModIntro.
  iApply "HΦ".
  eauto 15 with iFrame.
Qed.

End program.
