From Perennial.program_proof.mvcc Require Import
     txn_prelude txn_repr
     txnmgr_deactivate proph_proof.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition abort_false_cases tid γ : iProp Σ :=
  (nca_tids_frag γ tid) ∨
  (∃ mods, fci_tmods_frag γ (tid, mods)) ∨
  (∃ mods, fcc_tmods_frag γ (tid, mods)) ∨
  (∃ mods, cmt_tmods_frag γ (tid, mods)).

Theorem wp_txn__abort_false txn tid view γ τ :
  {{{ own_txn txn tid view γ τ ∗ abort_false_cases tid γ }}}
    Txn__abort #txn
  {{{ RET #(); False }}}.
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

  (* Obtain contradiction for each case. *)
  unfold abort_false_cases.
  iDestruct "Hfrag" as "[HncaFrag | Hfrag]".
  { (* Case NCA. *)
    iNamed "Hnca".
    iDestruct (nca_tids_lookup with "HncaAuth HncaFrag") as "%Helem".
    apply Hnca in Helem.
    destruct (no_commit_abort_false Helem).
    right.
    set_solver.
  }
  iDestruct "Hfrag" as "[HfciFrag | Hfrag]".
  { (* Case FCI. *)
    iNamed "Hfci".
    iDestruct "HfciFrag" as (m') "HfciFrag".
    iDestruct (fci_tmods_lookup with "HfciAuth HfciFrag") as "%Helem".
    apply Hfci in Helem. simpl in Helem.
    destruct Helem as (lp & ls & Hfc & _).
    destruct (first_commit_false Hfc).
    set_solver.
  }
  iDestruct "Hfrag" as "[HfccFrag | HcmtFrag]".
  { (* Case FCC. *)
    iNamed "Hfcc".
    iDestruct "HfccFrag" as (m') "HfccFrag".
    iDestruct (fcc_tmods_lookup with "HfccAuth HfccFrag") as "%Helem".
    apply Hfcc in Helem. simpl in Helem.
    destruct Helem as (lp & ls & Hfc & _).
    destruct (first_commit_false Hfc).
    set_solver.
  }
  { (* Case CMT. *)
    iNamed "Hcmt".
    iDestruct "HcmtFrag" as (m') "HcmtFrag".
    iDestruct (cmt_tmods_lookup with "HcmtAuth HcmtFrag") as "%Helem".
    apply Hcmt in Helem. simpl in Helem.
    destruct Helem as (lp & ls & Hfc & _).
    destruct (first_commit_false Hfc).
    set_solver.
  }
Qed.

Theorem wp_txn__abort txn tid view γ τ :
  {{{ own_txn txn tid view γ τ ∗ fa_tids_frag γ tid }}}
    Txn__abort #txn
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

#[global]
Hint Extern 1 (environments.envs_entails _ (abort_false_cases _ _)) => unfold abort_false_cases : core.
