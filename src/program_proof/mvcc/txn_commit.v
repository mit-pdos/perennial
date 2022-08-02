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
Definition commit_false_cases tid r γ τ : iProp Σ :=
  (nca_tids_frag γ tid) ∨
  (fa_tids_frag γ tid)  ∨
  (∃ mods, fci_tmods_frag γ (tid, mods)) ∨
  (∃ mods w Q, fcc_tmods_frag γ (tid, mods) ∗ txnmap_ptstos τ w ∗
               ⌜Q r w ∧ ¬ Q r (mods ∪ r) ∧ dom w = dom r⌝).

Theorem wp_txn__Commit_false txn tid view γ τ :
  {{{ own_txn_ready txn tid view γ τ ∗ commit_false_cases tid view γ τ }}}
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
  iIntros "(%future' & %Hfuture & Hproph)".

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
    iDestruct "HfciFrag" as (mods') "HfciFrag".
    iDestruct (fci_tmods_lookup with "HfciFrag HfciAuth") as "%Helem".
    apply Hfci in Helem. simpl in Helem.
    destruct Helem as (lp & ls & Hfc & Hincomp).
    apply hd_error_tl_repr in Hfuture as [Hhead _].
    pose proof (first_commit_eq Hfc Hhead) as Emods.
    subst mods'.

    (* TODO: Obtain contradiction by length of physical tuple. *)
    admit.
  }
  { (* Case FCC. *)
    iNamed "Hfcc".
    iDestruct "HfccFrag" as (mods' w Q) "(HfccFrag & Htxnps & %HQ & %HnotQ & %Hdom)".
    iDestruct (fcc_tmods_lookup with "HfccFrag HfccAuth") as "%Helem".
    apply Hfcc in Helem. simpl in Helem.
    (* Obtain equality between [mods] (in proph) and [mods'] (in evidence). *)
    destruct Helem as (lp & ls & Hfc & Hcomp).
    apply hd_error_tl_repr in Hfuture as Hhdtl.
    destruct Hhdtl as [Hhead _].
    pose proof (first_commit_eq Hfc Hhead) as Emods.
    subst mods'.
    (* Obtain contradiction from [Q r w] and [¬ Q r w]. *)
    iDestruct (txnmap_lookup_big with "Htxnmap Htxnps") as "%Hw".
    assert (Hviewdom : dom view = dom (mods ∪ view)) by set_solver.
    rewrite Hviewdom in Hdom.
    symmetry in Hdom.
    pose proof (Map.map_subset_dom_eq _ _ _ _ Hdom Hw) as H.
    by subst w.
  }
Admitted.

Theorem wp_txn__Commit txn tid view mods γ τ :
  {{{ own_txn_ready txn tid view γ τ ∗ cmt_tmods_frag γ (tid, mods) }}}
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
  iIntros "(%future' & %Hfuture & Hproph)".

  iNamed "Hcmt".
  iDestruct (cmt_tmods_lookup with "Hfrag HcmtAuth") as "%Helem".
  (* Obtain equality between [mods] and [mods0] using [Helem] and [Hhead]. *)
  apply Hcmt in Helem. simpl in Helem.
  destruct Helem as (lp & ls & Hfc & Hcomp).
  apply hd_error_tl_repr in Hfuture as Hhdtl.
  destruct Hhdtl as [Hhead _].
  pose proof (first_commit_eq Hfc Hhead) as Emods.
  subst mods0.

  (* TODO: Remove [(tid, mods)] from [tmods]. *)

  (* TODO: Update the abstract part of the tuple RP to match the physical part. *)

  (* TODO: Update the sets of ok/doomed txns to re-establish inv w.r.t. [future']. *)

  (***********************************************************)
  (* txn.txnMgr.deactivate(txn.sid, txn.tid)                 *)
  (***********************************************************)
Admitted.

End program.

Hint Extern 1 (environments.envs_entails _ (commit_false_cases _ _ _ _)) => unfold commit_false_cases : core.
