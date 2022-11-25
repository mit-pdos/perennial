From Perennial.program_proof.mvcc Require Import
     txn_prelude txn_repr
     txnmgr_activate
     wrbuf_repr wrbuf_proof.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*****************************************************************)
(* func (txn *Txn) begin()                                       *)
(*****************************************************************)
Theorem wp_txn__begin txn γ :
  ⊢ {{{ own_txn_uninit txn γ }}}
    <<< ∀∀ (ts : nat), ts_auth γ ts >>>
      Txn__begin #txn @ ↑mvccNGC ∪ ↑mvccNTID
    <<< ∃∃ ts', ts_auth γ ts' ∗ ⌜(ts < ts')%nat⌝ >>>
    {{{ (tid : u64) (wrbuf : loc), RET #();
        own_txn_impl txn wrbuf ts' γ ∗
        own_wrbuf_xtpls wrbuf ∅ ∧ ⌜int.nat tid = ts'⌝
    }}}.
Proof.
  iIntros "!>" (Φ) "Htxn HAU".
  iNamed "Htxn".
  wp_call.
  
  (***********************************************************)
  (* tid := txn.txnMgr.activate(txn.sid)                     *)
  (***********************************************************)
  wp_loadField.
  wp_loadField.
  wp_apply (wp_txnMgr__activate with "HtxnmgrRI"); first done.
  rename tid into tid_tmp.
  iMod "HAU" as (ts) "[Hts HAUC]".
  iModIntro.
  iExists ts.
  iFrame "Hts".
  iIntros "%n [H %Hlt]".
  iMod ("HAUC" with "[H]") as "HΦ"; first eauto with iFrame.
  iIntros "!>" (tid) "[Hactive %HtidNZ]".

  (***********************************************************)
  (* txn.tid = tid                                           *)
  (***********************************************************)
  wp_pures.
  wp_storeField.
  
  (***********************************************************)
  (* txn.wrbuf.Clear()                                       *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_wrbuf__Clear with "HwrbufRP").
  iIntros "HwrbufRP".
  wp_pures.

  iModIntro.
  iApply "HΦ". iFrame "HwrbufRP". iSplitL; last done.
  repeat iExists _. iFrame "∗#".
  iSplit; done.
Qed.

End program.
