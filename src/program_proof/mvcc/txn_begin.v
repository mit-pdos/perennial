From Perennial.program_proof.mvcc Require Import txn_common txnmgr_activate.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*****************************************************************)
(* func (txn *Txn) Begin()                                       *)
(*****************************************************************)
Theorem wp_txn__Begin txn γ :
  ⊢ {{{ own_txn_uninit txn γ }}}
    <<< ∀∀ (ts : nat), ts_auth γ ts >>>
      Txn__Begin #txn @ ∅
    <<< ∃ n, ts_auth γ (ts + n)%nat ∗ ⌜0 < n⌝ >>>
    {{{ (tid : u64), RET #(); own_txn_impl txn ts ∅ γ ∧ ⌜int.nat tid = ts⌝ }}}.
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
  iIntros "[%n H]".
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
  iApply "HΦ".
  eauto 20 with iFrame.
Qed.

End program.
