From Perennial.program_proof.mvcc Require Import proph_proof txn_common txnmgr_deactivate.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition abort_false_cases γ : iProp Σ :=
  (∃ tid, nca_tids_frag γ tid) ∨
  (∃ tmods, fci_tmods_frag γ tmods) ∨
  (∃ tmods, fcc_tmods_frag γ tmods) ∨
  (∃ tmods, cmt_tmods_frag γ tmods).

Theorem wp_txn__Abort_false txn tid γ τ :
  {{{ own_txn txn tid γ τ ∗ abort_false_cases γ }}}
    Txn__Abort #txn
  {{{ RET #(); False }}}.
Admitted.

Theorem wp_txn__Abort txn tid γ τ :
  {{{ own_txn txn tid γ τ ∗ fa_tids_frag γ tid }}}
    Txn__Abort #txn
  {{{ RET #(); own_txn_uninit txn γ }}}.
Proof.
  iIntros (Φ) "[Htxn Hfrag] HΦ".
  wp_call.

  (***********************************************************)
  (* proph.ResolveAbort(txn.txnMgr.p, txn.tid)               *)
  (***********************************************************)
  iNamed "Htxn".
  iNamed "Himpl".
  do 3 wp_loadField.
  wp_apply (wp_ResolveAbort); first auto.
  iInv "Hinv" as "> HinvO" "HinvC".
  iApply ncfupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iNamed "HinvO".
  iExists future.
  iFrame "Hproph".
  iIntros "(%future' & %Hhead & Hproph)".
  iMod "Hclose" as "_".
  (* Update the sets of ok/doomed txns to re-establish inv w.r.t. [future']. *)
  iDestruct (nca_inv_any_action with "Hnca") as "Hnca"; first apply Hhead.
  iMod (fa_inv_same_action with "Hfrag Hfa") as "Hfa"; first apply Hhead.
  iDestruct (fci_inv_diff_action with "Hfci") as "Hfci"; [apply Hhead | done |].
  iDestruct (fcc_inv_diff_action with "Hfcc") as "Hfcc"; [apply Hhead | done |].
  iDestruct (cmt_inv_diff_action with "Hcmt") as "Hcmt"; [apply Hhead | done |].
  iDestruct (per_key_inv_past_abort tid with "Hkeys") as "Hkeys".
  iMod ("HinvC" with "[- HΦ Htid Hsid Hwrbuf HwrbufRP Hactive Hltuples Htxnmap]") as "_".
  { (* Close the invariant. *) eauto 15 with iFrame. }
  iIntros "!> _".
  wp_pures.

  (***********************************************************)
  (* txn.txnMgr.deactivate(txn.sid, txn.tid)                 *)
  (***********************************************************)
  do 3 wp_loadField.
  wp_apply (wp_txnMgr__deactivate with "HtxnmgrRI Hactive").
  wp_pures.
  iApply "HΦ".
  eauto 20 with iFrame.
Qed.

End program.

Hint Extern 1 (environments.envs_entails _ (abort_false_cases _)) => unfold abort_false_cases : core.
