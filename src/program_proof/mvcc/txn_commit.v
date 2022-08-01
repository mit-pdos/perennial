From Perennial.program_proof.mvcc Require Import proph_proof txn_common txn_apply.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(**
 * Proof plan:
 * 1. Prove FCC
 * 2. Define [ptuple_past_rel]
 * 3. Prove FCI
 * 4. Prove CMT (incl. tuple-write safe extension)
 * 5. Prove tuple-read safe extension
 *)

(* TODO: the last case also needs [¬ Q r w].*)
Definition commit_false_cases tid γ : iProp Σ :=
  (nca_tids_frag γ tid) ∨
  (fa_tids_frag γ tid)  ∨
  (∃ mods, fci_tmods_frag γ (tid, mods)) ∨
  (∃ mods, fcc_tmods_frag γ (tid, mods)).

Theorem wp_txn__Commit_false txn tid γ τ :
  {{{ own_txn_ready txn tid γ τ ∗ commit_false_cases tid γ }}}
    Txn__Commit #txn
  {{{ (ok : bool), RET #ok; False }}}.
Proof.
  iIntros (Φ) "[Htxn Hfrag] HΦ".
  wp_call.

  (***********************************************************)
  (* txn.apply()                                             *)
  (***********************************************************)
  wp_apply (wp_txn__apply with "Htxn").
  iIntros "Htxn".
  wp_pures.

  (***********************************************************)
  (* proph.ResolveCommit(txn.txnMgr.p, txn.tid, txn.wrbuf)   *)
  (***********************************************************)
  iNamed "Htxn".
  iNamed "Himpl".
  do 4 wp_loadField.
  wp_apply (wp_ResolveCommit with "[$HwrbufRP]"); first eauto.
  iInv "Hinv" as "> HinvO" "HinvC".
  iApply ncfupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iNamed "HinvO".
  iExists future.
  iFrame "Hproph".
  iIntros "(%future' & %Hhead & Hproph)".

  (* Obtain contradiction for each case. *)
  unfold commit_false_cases.
  iDestruct "Hfrag" as "[HncaFrag | Hfrag]".
  { (* Case NCA. *)
    iNamed "Hnca".
    iDestruct (nca_tids_lookup with "HncaFrag HncaAuth") as "%Helem".
    apply Hnca in Helem.
    destruct (no_commit_abort_false Helem).
    left.
    set_solver.
  }
  iDestruct "Hfrag" as "[HfaFrag | Hfrag]".
  { (* Case FA. *)
    iNamed "Hfa".
    iDestruct (fa_tids_lookup with "HfaFrag HfaAuth") as "%Helem".
    apply Hfa in Helem.
    destruct (first_abort_false mods Helem).
    set_solver.
  }
  iDestruct "Hfrag" as "[HfciFrag | HfccFrag]".
  { (* Case FCI. *)
    iNamed "Hfci".
    iDestruct "HfciFrag" as (m') "HfciFrag".
    iDestruct (fci_tmods_lookup with "HfciFrag HfciAuth") as "%Helem".
    apply Hfci in Helem. simpl in Helem.
    (* TODO: Obtain contradiction by length of physical tuple. *)
    admit.
  }
  { (* Case FCC. *)
    iNamed "Hfcc".
    iDestruct "HfccFrag" as (m') "HfccFrag".
    iDestruct (fcc_tmods_lookup with "HfccFrag HfccAuth") as "%Helem".
    apply Hfcc in Helem. simpl in Helem.
    (* TODO: Obtain contradiction from [Q r w] and [¬ Q r w]. *)
    admit.
  }
Admitted.

Theorem wp_txn__Commit txn tid mods γ τ :
  {{{ own_txn_ready txn tid γ τ ∗ cmt_tmods_frag γ (tid, mods) }}}
    Txn__Commit #txn
  {{{ (ok : bool), RET #ok; own_txn_uninit txn γ }}}.
Proof.
  iIntros (Φ) "[Htxn Hfrag] HΦ".
  wp_call.

  (***********************************************************)
  (* txn.apply()                                             *)
  (***********************************************************)
  wp_apply (wp_txn__apply with "Htxn").
  iIntros "Htxn".
  wp_pures.

  (***********************************************************)
  (* proph.ResolveCommit(txn.txnMgr.p, txn.tid, txn.wrbuf)   *)
  (***********************************************************)
  iNamed "Htxn".
  iNamed "Himpl".
  do 4 wp_loadField.
  wp_apply (wp_ResolveCommit with "[$HwrbufRP]"); first eauto.
  iInv "Hinv" as "> HinvO" "HinvC".
  iApply ncfupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iNamed "HinvO".
  iExists future.
  iFrame "Hproph".
  iIntros "(%future' & %Hhead & Hproph)".

  iNamed "Hcmt".
  iDestruct (cmt_tmods_lookup with "Hfrag HcmtAuth") as "%Helem".
  apply Hcmt in Helem. simpl in Helem.
  (* TODO: Obtain equality between [mods] and [mods0] using [Helem] and [Hhead]. *)

  (* TODO: Update the abstract part of the tuple RP to match the physical part. *)

  (* TODO: Update the sets of ok/doomed txns to re-establish inv w.r.t. [future']. *)

  (* TODO: Remove [(tid, mods)] from [tmods]. *)

  (***********************************************************)
  (* txn.txnMgr.deactivate(txn.sid, txn.tid)                 *)
  (***********************************************************)
Admitted.

End program.

Hint Extern 1 (environments.envs_entails _ (commit_false_cases _ _)) => unfold commit_false_cases : core.
