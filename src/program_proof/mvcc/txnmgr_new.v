From Perennial.program_proof.mvcc Require Import txn_common.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*****************************************************************)
(* func (txnMgr *TxnMgr) New() *Txn                              *)
(*****************************************************************)
Theorem wp_txnMgr__New txnmgr γ :
  is_txnmgr txnmgr γ -∗
  {{{ True }}}
    TxnMgr__New #txnmgr
  {{{ (txn : loc), RET #txn; own_txn_uninit txn γ }}}.
Proof.
  iIntros "#Htxnmgr" (Φ) "!> _ HΦ".
  iPoseProof "Htxnmgr" as "Htxnmgr'".
  iNamed "Htxnmgr".
  wp_call.
  
  (***********************************************************)
  (* txnMgr.latch.Lock()                                     *)
  (***********************************************************)
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked HtxnmgrOwn]".
  iNamed "HtxnmgrOwn".
  wp_pures.
  
  (***********************************************************)
  (* txn := new(Txn)                                         *)
  (***********************************************************)
  wp_apply (wp_allocStruct); first auto 10.
  iIntros (txn) "Htxn".
  iDestruct (struct_fields_split with "Htxn") as "Htxn".
  iNamed "Htxn".
  simpl.
  wp_pures.
  
  (***********************************************************)
  (* txn.wrbuf = wrbuf.MkWrBuf                               *)
  (***********************************************************)
  wp_apply (wp_MkWrBuf).
  iIntros (wrbuf) "HwrbufRP".
  wp_storeField.
          
  (***********************************************************)
  (* sid := txnMgr.sidCur                                    *)
  (* txn.sid = sid                                           *)
  (***********************************************************)
  wp_loadField.
  wp_pures.
  wp_storeField.
  
  (***********************************************************)
  (* txn.idx = txnMgr.idx                                    *)
  (* txn.txnMgr = txnMgr                                     *)
  (***********************************************************)
  wp_loadField.
  do 2 wp_storeField.
  
  (***********************************************************)
  (* txnMgr.sidCur = sid + 1                                 *)
  (* if txnMgr.sidCur == config.N_TXN_SITES {                *)
  (*     txnMgr.sidCur = 0                                   *)
  (* }                                                       *)
  (***********************************************************)
  wp_storeField.
  wp_loadField.
  wp_apply (wp_If_join_evar with "[Hsidcur]").
  { iIntros (b') "%Eb'".
    case_bool_decide.
    { wp_if_true.
      wp_storeField.
      iSplit; first done.
      replace (U64 0) with (if b' then (U64 0) else (word.add sidcur (U64 1))) by by rewrite Eb'.
      iNamedAccu.
    }
    { wp_if_false.
      iModIntro.
      subst.
      by iFrame "∗".
    }
  }
  iIntros "H".
  iNamed "H".
  wp_pures.
    
  (***********************************************************)
  (* txnMgr.latch.Unlock()                                   *)
  (* return txn                                              *)
  (***********************************************************)
  wp_loadField.
  wp_apply (release_spec with "[Hlocked Hsidcur]").
  { iFrame "Hlock Hlocked".
    iNext.
    unfold own_txnmgr.
    iExists _.
    iFrame.
    iSplit; last done.
    iPureIntro.
    case_bool_decide; first done.
    unfold N_TXN_SITES in *.
    apply Znot_le_gt in H.
    by apply Z.gt_lt.
  }
  wp_pures.
  iApply "HΦ".
  iMod (readonly_alloc_1 with "idx") as "#Hidx_txn".
  iMod (readonly_alloc_1 with "txnMgr") as "#Htxnmgr_txn".
  replace (int.nat 0) with 0%nat by word.
  simpl.
  eauto 20 with iFrame.
Qed.

End program.
