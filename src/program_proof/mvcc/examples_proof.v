From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.go_mvcc Require Import examples.
From Perennial.program_proof.mvcc Require Import txn_proof.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

#[local]
Definition mvcc_inv_app_def γ : iProp Σ :=
  ∃ (v0 v1 : dbval),
    "Hdbpt0" ∷ dbmap_ptsto γ (U64 0) (1 / 2)%Qp v0 ∗
    "Hdbpt1" ∷ dbmap_ptsto γ (U64 1) 1%Qp v1.

Instance mvcc_inv_app_timeless γ :
  Timeless (mvcc_inv_app_def γ).
Proof. unfold mvcc_inv_app_def. apply _. Defined.

#[local]
Definition mvccNApp := nroot .@ "app".
#[local]
Definition mvcc_inv_app γ : iProp Σ :=
  inv mvccNApp (mvcc_inv_app_def γ).

Definition P_WriteReservedKey (r : dbmap) := dom r = {[ (U64 0) ]}.
Definition Q_WriteReservedKey (r w: dbmap) :=
  w !! (U64 0) = Some (Value (U64 2)).

Theorem wp_WriteReservedKeySeq txn tid r γ τ :
  {{{ own_txn txn tid r γ τ ∗ ⌜P_WriteReservedKey r⌝ ∗ txnmap_ptstos τ r }}}
    WriteReservedKeySeq #txn
  {{{ w (ok : bool), RET #ok;
      own_txn txn tid r γ τ ∗
      if ok then ⌜Q_WriteReservedKey r w ∧ dom r = dom w⌝ ∗ txnmap_ptstos τ w else True
  }}}.
Proof.
  iIntros (Φ) "(Htxn & %Hdom & Hpts) HΦ".
  wp_call.

  (***********************************************************)
  (* txn.Put(0, 2)                                           *) 
  (* return true                                             *) 
  (***********************************************************)
  assert (Helem : (U64 0) ∈ dom r) by set_solver.
  rewrite elem_of_dom in Helem. destruct Helem as [v Hlookup].
  wp_apply (wp_txn__Put with "[$Htxn Hpts]").
  { iDestruct (big_sepM_lookup with "Hpts") as "Hpts"; [apply Hlookup | iFrame]. }
  iIntros "[Htxn Hpts]".
  wp_pures.
  iModIntro.
  iApply ("HΦ" $! ({[ (U64 0) := (Value (U64 2)) ]})).
  iFrame "Htxn".
  iSplit.
  { iPureIntro. unfold Q_WriteReservedKey. split; [by rewrite lookup_singleton | set_solver]. }
  unfold txnmap_ptstos.
  rewrite big_sepM_singleton.
  done.
Qed.

Theorem wp_WriteReservedKey (txn : loc) γ :
  ⊢ {{{ own_txn_uninit txn γ }}}
    <<< ∀∀ (r : dbmap), ⌜P_WriteReservedKey r⌝ ∗ dbmap_ptstos γ 1 r >>>
      WriteReservedKey #txn @ ↑mvccNSST
    <<< ∃∃ (ok : bool), if ok then (∃ w, ⌜Q_WriteReservedKey r w⌝ ∗ dbmap_ptstos γ 1 w) else dbmap_ptstos γ 1 r >>>
    {{{ RET #ok; own_txn_uninit txn γ }}}.
Proof.
  iIntros "!>".
  iIntros (Φ) "Htxn HAU".
  wp_call.

  (***********************************************************)
  (* return txn.DoTxn(WriteReservedKeySeq)                   *)
  (***********************************************************)
  wp_apply (wp_txn__DoTxn _ _ _ Q_WriteReservedKey with "[$Htxn]").
  { unfold Q_WriteReservedKey. apply _. }
  { unfold spec_body.
    iIntros (tid r τ Φ') "!> HP HΦ'".
    iApply (wp_WriteReservedKeySeq with "HP HΦ'").
  }
  done.
Qed.

Definition P_WriteFreeKey (r : dbmap) := dom r = {[ (U64 1) ]}.
Definition Q_WriteFreeKey (r w: dbmap) :=
  w !! (U64 1) = Some (Value (U64 3)).

Theorem wp_WriteFreeKeySeq txn tid r γ τ :
  {{{ own_txn txn tid r γ τ ∗ ⌜P_WriteFreeKey r⌝ ∗ txnmap_ptstos τ r }}}
    WriteFreeKeySeq #txn
  {{{ w (ok : bool), RET #ok;
      own_txn txn tid r γ τ ∗
      if ok then ⌜Q_WriteFreeKey r w ∧ dom r = dom w⌝ ∗ txnmap_ptstos τ w else True
  }}}.
Proof.
  iIntros (Φ) "(Htxn & %Hdom & Hpts) HΦ".
  wp_call.

  (***********************************************************)
  (* txn.Put(1, 3)                                           *) 
  (* return true                                             *) 
  (***********************************************************)
  assert (Helem : (U64 1) ∈ dom r) by set_solver.
  rewrite elem_of_dom in Helem. destruct Helem as [v Hlookup].
  wp_apply (wp_txn__Put with "[$Htxn Hpts]").
  { iDestruct (big_sepM_lookup with "Hpts") as "Hpts"; [apply Hlookup | iFrame]. }
  iIntros "[Htxn Hpts]".
  wp_pures.
  iModIntro.
  iApply ("HΦ" $! ({[ (U64 1) := (Value (U64 3)) ]})).
  iFrame "Htxn".
  iSplit.
  { iPureIntro. unfold Q_WriteFreeKey. split; [by rewrite lookup_singleton | set_solver]. }
  unfold txnmap_ptstos.
  rewrite big_sepM_singleton.
  done.
Qed.

Theorem wp_WriteFreeKey (txn : loc) γ :
  ⊢ {{{ own_txn_uninit txn γ }}}
    <<< ∀∀ (r : dbmap), ⌜P_WriteFreeKey r⌝ ∗ dbmap_ptstos γ 1 r >>>
      WriteFreeKey #txn @ ↑mvccNSST
    <<< ∃∃ (ok : bool), if ok then (∃ w, ⌜Q_WriteFreeKey r w⌝ ∗ dbmap_ptstos γ 1 w) else dbmap_ptstos γ 1 r >>>
    {{{ RET #ok; own_txn_uninit txn γ }}}.
Proof.
  iIntros "!>".
  iIntros (Φ) "Htxn HAU".
  wp_call.

  (***********************************************************)
  (* return txn.DoTxn(WriteFreeKeySeq)                       *)
  (***********************************************************)
  wp_apply (wp_txn__DoTxn _ _ _ Q_WriteFreeKey with "[$Htxn]").
  { unfold Q_WriteFreeKey. apply _. }
  { unfold spec_body.
    iIntros (tid r τ Φ') "!> HP HΦ'".
    iApply (wp_WriteFreeKeySeq with "HP HΦ'").
  }
  done.
Qed.

(*****************************************************************)
(* func InitializeData(txnmgr *txn.TxnMgr)                       *)
(*****************************************************************)
Theorem wp_InitializeData (txnmgr : loc) γ :
  is_txnmgr txnmgr γ -∗
  {{{ dbmap_ptstos γ 1 (gset_to_gmap Nil keys_all) }}}
    InitializeData #txnmgr
  {{{ (v : dbval), RET #(); dbmap_ptsto γ (U64 0) (1 / 2)%Qp v ∗ mvcc_inv_app γ }}}.
Admitted.

Theorem wp_InitExample :
  {{{ True }}}
    InitExample #()
  {{{ γ (v : dbval) (mgr : loc), RET #mgr;
      dbmap_ptsto γ (U64 0) (1 / 2)%Qp v ∗ is_txnmgr mgr γ ∗ mvcc_inv_app γ
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.

  (***********************************************************)
  (* mgr := txn.MkTxnMgr()                                   *)
  (* InitializeData(mgr)                                     *)
  (* return mgr                                              *)
  (***********************************************************)
  wp_apply wp_MkTxnMgr.
  iIntros (γ mgr) "[#Hmgr Hdbpts]".
  wp_pures.
  wp_apply (wp_InitializeData with "Hmgr [$Hdbpts]").
  iIntros (v) "[Hdbpt #Hinv]".
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iFrame "∗ #".
Qed.

(* FIXME: move this to mvcc_ghost *)
Lemma dbmap_elem_split {γ k q} q1 q2 v :
  (q1 + q2 = q)%Qp ->
  dbmap_ptsto γ k q v -∗
  dbmap_ptsto γ k q1 v ∗
  dbmap_ptsto γ k q2 v.
Admitted.

(**
 * This method should specify the new value, but currently we don't
 * have support for txn arguments, so we always set the value to 2.
 *)
Theorem wp_WriteReservedKeyExample (mgr : loc) (v : dbval) γ :
  mvcc_inv_app γ -∗
  is_txnmgr mgr γ -∗
  {{{ dbmap_ptsto γ (U64 0) (1 / 2)%Qp v }}}
    WriteReservedKeyExample #mgr
  {{{ (ok : bool), RET #ok;
      dbmap_ptsto γ (U64 0) (1 / 2)%Qp (if ok then (Value (U64 2)) else v)
  }}}.
Proof.
  iIntros "#Hinv #Hmgr" (Φ) "!> Hdbpt HΦ".
  wp_call.

  (***********************************************************)
  (* txn := mgr.New()                                        *)
  (***********************************************************)
  wp_apply (wp_txnMgr__New with "Hmgr").
  iNamed "Hmgr".
  iIntros (txn) "Htxn".
  wp_pures.

  (***********************************************************)
  (* ok := WriteReservedKey(txn)                             *)
  (***********************************************************)
  wp_apply (wp_WriteReservedKey with "Htxn").
  iInv "Hinv" as "> HinvO" "HinvC".
  iApply ncfupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iNamed "HinvO".
  (* Give atomic precondition. *)
  iExists {[ (U64 0) := v0 ]}.
  unfold dbmap_ptstos. rewrite {1} big_sepM_singleton.
  iDestruct (dbmap_elem_combine with "Hdbpt Hdbpt0") as "[Hdbpt0 ->]".
  rewrite Qp_half_half.
  iFrame.
  iSplit.
  { iPureIntro. unfold P_WriteReservedKey. set_solver. }
  (* Take atomic postcondition. *)
  iIntros (ok) "H".
  iMod "Hclose" as "_".

  (***********************************************************)
  (* return p, ok                                            *)
  (***********************************************************)
  destruct ok eqn:E.
  { (* Case COMMIT. *)
    iDestruct "H" as (w) "[%HQ Hdbpt0]".
    unfold Q_WriteReservedKey in HQ.
    iDestruct (big_sepM_lookup with "Hdbpt0") as "Hdbpt0"; first apply HQ.
    iDestruct (dbmap_elem_split (1 / 2) (1 / 2) with "Hdbpt0") as "[Hdbpt Hdbpt0]"; first compute_done.
    iMod ("HinvC" with "[- HΦ Hdbpt]") as "_".
    { (* Close the invariant. *) do 2 iExists _. iFrame. }
    iModIntro.
    iIntros "Htxn".
    wp_pures.
    iApply "HΦ".
    by iFrame.
  }
  { (* Case ABORT. *)
    unfold dbmap_ptstos. rewrite big_sepM_singleton.
    iDestruct (dbmap_elem_split (1 / 2) (1 / 2) with "H") as "[Hdbpt Hdbpt0]"; first compute_done.
    iMod ("HinvC" with "[- HΦ Hdbpt]") as "_".
    { (* Close the invariant. *) do 2 iExists _. iFrame. }
    iModIntro.
    iIntros "Htxn".
    wp_pures.
    iApply "HΦ".
    by iFrame.
  }
Qed.

(**
 * The purpose of this example is to show that writing to the reserved
 * key required the [dbmap_ptsto].
*)
Theorem wp_WriteReservedKeyNonexample (mgr : loc) γ :
  mvcc_inv_app γ -∗
  is_txnmgr mgr γ -∗
  {{{ True }}}
    WriteReservedKeyExample #mgr
  {{{ (ok : bool), RET #ok; True }}}.
Proof.
  iIntros "#Hinv #Hmgr" (Φ) "!> _ HΦ".
  wp_call.

  (***********************************************************)
  (* txn := mgr.New()                                        *)
  (***********************************************************)
  wp_apply (wp_txnMgr__New with "Hmgr").
  iNamed "Hmgr".
  iIntros (txn) "Htxn".
  wp_pures.

  (***********************************************************)
  (* ok := WriteReservedKey(txn)                             *)
  (***********************************************************)
  wp_apply (wp_WriteReservedKey with "Htxn").
  iInv "Hinv" as "> HinvO" "HinvC".
  iApply ncfupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iNamed "HinvO".
  (* Give atomic precondition *)
  iExists {[ (U64 0) := v0 ]}.
  unfold dbmap_ptstos. rewrite {1} big_sepM_singleton.
  (**
   * However, we only have one half of the ownership of key 0 (see
   * [Hdbpt0]), so we get stuck.
   *)
Abort.

(**
 * The point of this example is to demonstrate that [frac_ptsto] is
 * not required to update free keys.
 *)
Theorem wp_WriteFreeKeyExample (mgr : loc) γ :
  mvcc_inv_app γ -∗
  is_txnmgr mgr γ -∗
  {{{ True }}}
    WriteFreeKeyExample #mgr
  {{{ (ok : bool), RET #ok; True }}}.
Proof using heapGS0 mvcc_ghostG0 Σ.
  iIntros "#Hinv #Hmgr" (Φ) "!> _ HΦ".
  wp_call.

  (***********************************************************)
  (* txn := mgr.New()                                        *)
  (***********************************************************)
  wp_pures.
  wp_apply (wp_txnMgr__New with "Hmgr").
  iNamed "Hmgr".
  iIntros (txn) "Htxn".
  wp_pures.

  (***********************************************************)
  (* ok := WriteFreeKey(txn)                                 *)
  (***********************************************************)
  wp_apply (wp_WriteFreeKey with "Htxn").
  iInv "Hinv" as "> HinvO" "HinvC".
  iApply ncfupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iNamed "HinvO".
  iExists {[ (U64 1) := v1 ]}.
  (* Give atomic precondition *)
  unfold dbmap_ptstos. rewrite {1} big_sepM_singleton.
  iFrame.
  iSplit.
  { iPureIntro. unfold P_WriteFreeKey. set_solver. }
  (* Take atomic precondition *)
  iIntros (ok) "H".
  iMod "Hclose" as "_".

  (***********************************************************)
  (* return ok                                               *)
  (***********************************************************)
  destruct ok eqn:E.
  { (* Case COMMIT. *)
    iDestruct "H" as (w) "[%HQ Hdbpt1]".
    (* iDestruct "H" as (w) "[%HQ Hdbpt0]". This typo produces weird behavior. *)
    unfold Q_WriteFreeKey in HQ.
    iDestruct (big_sepM_lookup with "Hdbpt1") as "Hdbpt1"; first apply HQ.
    iMod ("HinvC" with "[- HΦ]") as "_".
    { (* Close the invariant. *) do 2 iExists _. iFrame. }
    iModIntro.
    iIntros "Htxn".
    wp_pures.
    by iApply "HΦ".
  }
  { (* Case ABORT. *)
    rewrite big_sepM_singleton.
    iMod ("HinvC" with "[- HΦ]") as "_".
    { (* Close the invariant. *) do 2 iExists _. iFrame. }
    iModIntro.
    iIntros "Htxn".
    wp_pures.
    by iApply "HΦ".
  }
Qed.

End program.
