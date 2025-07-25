From Perennial.program_proof.mvcc Require Import
     mvcc_prelude mvcc_ghost mvcc_inv
     db_repr db_mk db_new_txn
     txn_repr txn_read txn_write txn_run.
From Goose.github_com.mit_pdos.vmvcc Require Import examples.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

#[local]
Definition mvcc_inv_app_def γ : iProp Σ :=
  ∃ (v0 v1 : dbval),
    "Hdbpt0" ∷ dbmap_ptsto γ (W64 0) (1 / 2)%Qp v0 ∗
    "Hdbpt1" ∷ dbmap_ptsto γ (W64 1) 1%Qp v1.

Instance mvcc_inv_app_timeless γ :
  Timeless (mvcc_inv_app_def γ).
Proof. unfold mvcc_inv_app_def. apply _. Defined.

#[local]
Definition mvccNApp := nroot .@ "app".
#[local]
Definition mvcc_inv_app γ : iProp Σ :=
  inv mvccNApp (mvcc_inv_app_def γ).

Definition P_WriteReservedKey (r : dbmap) := dom r = {[ (W64 0) ]}.
Definition Q_WriteReservedKey (v : u64) (r w : dbmap) :=
  w !! (W64 0) = Some (Value v).

Theorem wp_WriteReservedKeySeq txn (v : u64) tid r γ τ :
  {{{ own_txn txn tid r γ τ ∗ ⌜P_WriteReservedKey r⌝ ∗ txnmap_ptstos τ r }}}
    WriteReservedKeySeq #txn #v
  {{{ (ok : bool), RET #ok;
      own_txn txn tid r γ τ ∗
      if ok then ∃ w, ⌜Q_WriteReservedKey v r w ∧ dom r = dom w⌝ ∗ txnmap_ptstos τ w else True
  }}}.
Proof.
  iIntros (Φ) "(Htxn & %Hdom & Hpts) HΦ".
  wp_rec. wp_pures.

  (***********************************************************)
  (* txn.Put(0, v)                                           *) 
  (* return true                                             *) 
  (***********************************************************)
  assert (Helem : (W64 0) ∈ dom r) by set_solver.
  rewrite elem_of_dom in Helem. destruct Helem as [u Hlookup].
  wp_apply (wp_txn__Put with "[$Htxn Hpts]").
  { iDestruct (big_sepM_lookup with "Hpts") as "Hpts"; [apply Hlookup | iFrame]. }
  iIntros "[Htxn Hpts]".
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iFrame "Htxn".
  iExists {[ (W64 0) := (Value v) ]}.
  iSplit.
  { iPureIntro. unfold Q_WriteReservedKey. split; [by rewrite lookup_singleton_eq | set_solver]. }
  unfold txnmap_ptstos.
  rewrite big_sepM_singleton.
  done.
Qed.

Theorem wp_WriteReservedKey (txn : loc) (v : u64) γ :
  ⊢ {{{ own_txn_uninit txn γ }}}
    <<< ∀∀ (r : dbmap), ⌜P_WriteReservedKey r⌝ ∗ dbmap_ptstos γ 1 r >>>
      WriteReservedKey #txn #v @ ↑mvccN
    <<< ∃∃ (ok : bool) (w : dbmap),
          if ok then ⌜Q_WriteReservedKey v r w⌝ ∗ dbmap_ptstos γ 1 w else dbmap_ptstos γ 1 r
    >>>
    {{{ RET #ok; own_txn_uninit txn γ }}}.
Proof.
  iIntros "!>".
  iIntros (Φ) "Htxn HAU".
  wp_rec. wp_pures.

  (***********************************************************)
  (* body := func(txn *txn.Txn) bool {                       *) 
  (*     return WriteReservedKeySeq(txn, v)                  *) 
  (* }                                                       *) 
  (* return t.DoTxn(body)                                    *) 
  (***********************************************************)
  wp_apply (wp_txn__DoTxn_xres _ _ _ (Q_WriteReservedKey v) with "[$Htxn]").
  { unfold Q_WriteReservedKey. apply _. }
  { unfold spec_body.
    iIntros (tid r τ Φ') "HP HΦ'".
    wp_pures.
    iApply (wp_WriteReservedKeySeq with "HP HΦ'").
  }
  done.
Qed.

Definition P_WriteFreeKey (r : dbmap) := dom r = {[ (W64 1) ]}.
Definition Q_WriteFreeKey (v : u64) (r w : dbmap) :=
  w !! (W64 1) = Some (Value v).

Theorem wp_WriteFreeKeySeq txn (v : u64) tid r γ τ :
  {{{ own_txn txn tid r γ τ ∗ ⌜P_WriteFreeKey r⌝ ∗ txnmap_ptstos τ r }}}
    WriteFreeKeySeq #txn #v
  {{{ (ok : bool), RET #ok;
      own_txn txn tid r γ τ ∗
      if ok then ∃ w, ⌜Q_WriteFreeKey v r w ∧ dom r = dom w⌝ ∗ txnmap_ptstos τ w else True
  }}}.
Proof.
  iIntros (Φ) "(Htxn & %Hdom & Hpts) HΦ".
  wp_rec. wp_pures.

  (***********************************************************)
  (* txn.Put(1, v)                                           *) 
  (* return true                                             *) 
  (***********************************************************)
  assert (Helem : (W64 1) ∈ dom r) by set_solver.
  rewrite elem_of_dom in Helem. destruct Helem as [u Hlookup].
  wp_apply (wp_txn__Put with "[$Htxn Hpts]").
  { iDestruct (big_sepM_lookup with "Hpts") as "Hpts"; [apply Hlookup | iFrame]. }
  iIntros "[Htxn Hpts]".
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iFrame "Htxn".
  iExists {[ (W64 1) := (Value v) ]}.
  iSplit.
  { iPureIntro. unfold Q_WriteFreeKey. split; [by rewrite lookup_singleton_eq | set_solver]. }
  unfold txnmap_ptstos.
  rewrite big_sepM_singleton.
  done.
Qed.

Theorem wp_WriteFreeKey (txn : loc) (v : u64) γ :
  ⊢ {{{ own_txn_uninit txn γ }}}
    <<< ∀∀ (r : dbmap), ⌜P_WriteFreeKey r⌝ ∗ dbmap_ptstos γ 1 r >>>
      WriteFreeKey #txn #v @ ↑mvccN
    <<< ∃∃ (ok : bool) (w : dbmap),
          if ok then ⌜Q_WriteFreeKey v r w⌝ ∗ dbmap_ptstos γ 1 w else dbmap_ptstos γ 1 r
    >>>
    {{{ RET #ok; own_txn_uninit txn γ }}}.
Proof.
  iIntros "!>".
  iIntros (Φ) "Htxn HAU".
  wp_rec. wp_pures.

  (***********************************************************)
  (* body := func(txn *txn.Txn) bool {                       *)
  (*     return WriteFreeKeySeq(txn, v)                      *)
  (* }                                                       *)
  (* return t.DoTxn(body)                                    *)
  (***********************************************************)
  wp_apply (wp_txn__DoTxn_xres _ _ _ (Q_WriteFreeKey v) with "[$Htxn]").
  { unfold Q_WriteFreeKey. apply _. }
  { unfold spec_body.
    iIntros (tid r τ Φ') "HP HΦ'".
    wp_pures.
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
  {{{ (v : dbval), RET #(); dbmap_ptsto γ (W64 0) (1 / 2)%Qp v ∗ mvcc_inv_app γ }}}.
Proof.
  iIntros "#Htxn" (Φ) "!> Hdbpts HΦ".
  wp_rec. wp_pures.
  iApply "HΦ".
  unfold dbmap_ptstos.
  iDestruct (big_sepM_delete _ _ (W64 0) with "Hdbpts") as "[Hdbpt Hdbpts]".
  { rewrite lookup_gset_to_gmap_Some. split; [set_solver | done]. }
  iDestruct (dbmap_elem_split (1 / 2) (1 / 2) with "Hdbpt") as "[H Hdbpt0]".
  { compute_done. }
  iFrame "H".
  iMod (inv_alloc mvccNApp _ (mvcc_inv_app_def γ) with "[-]") as "#Hinv".
  { iNext.
    do 2 iExists _.
    iDestruct (big_sepM_delete _ _ (W64 1) with "Hdbpts") as "[Hdbpt1 Hdbpts]".
    { rewrite lookup_delete_Some.
      split; first done.
      rewrite lookup_gset_to_gmap_Some. split; [set_solver | done].
    }
    iFrame.
  }
  done.
Qed.

Theorem wp_InitExample :
  {{{ True }}}
    InitExample #()
  {{{ γ (v : dbval) (mgr : loc), RET #mgr;
      dbmap_ptsto γ (W64 0) (1 / 2)%Qp v ∗ is_txnmgr mgr γ ∗ mvcc_inv_app γ
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_rec. wp_pures.

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

Theorem wp_WriteReservedKeyExample (mgr : loc) (u : u64) (v : dbval) γ :
  mvcc_inv_app γ -∗
  is_txnmgr mgr γ -∗
  {{{ dbmap_ptsto γ (W64 0) (1 / 2)%Qp v }}}
    WriteReservedKeyExample #mgr #u
  {{{ (ok : bool), RET #ok;
      dbmap_ptsto γ (W64 0) (1 / 2)%Qp (if ok then (Value u) else v)
  }}}.
Proof.
  iIntros "#Hinv #Hmgr" (Φ) "!> Hdbpt HΦ".
  wp_rec. wp_pures.

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
  iExists {[ (W64 0) := v0 ]}.
  unfold dbmap_ptstos. rewrite {1} big_sepM_singleton.
  iDestruct (dbmap_elem_combine with "Hdbpt Hdbpt0") as "[Hdbpt0 ->]".
  rewrite Qp.half_half.
  iFrame.
  iSplit.
  { iPureIntro. unfold P_WriteReservedKey. set_solver. }
  (* Take atomic postcondition. *)
  iIntros (ok w) "H".
  iMod "Hclose" as "_".

  (***********************************************************)
  (* return p, ok                                            *)
  (***********************************************************)
  destruct ok eqn:E.
  { (* Case COMMIT. *)
    iDestruct "H" as "[%HQ Hdbpt0]".
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
Theorem wp_WriteReservedKeyNonexample (mgr : loc) (u : u64) γ :
  mvcc_inv_app γ -∗
  is_txnmgr mgr γ -∗
  {{{ True }}}
    WriteReservedKeyExample #mgr #u
  {{{ (ok : bool), RET #ok; True }}}.
Proof.
  iIntros "#Hinv #Hmgr" (Φ) "!> _ HΦ".
  wp_rec. wp_pures.

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
  iExists {[ (W64 0) := v0 ]}.
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
Theorem wp_WriteFreeKeyExample (mgr : loc) (u : u64) γ :
  mvcc_inv_app γ -∗
  is_txnmgr mgr γ -∗
  {{{ True }}}
    WriteFreeKeyExample #mgr #u
  {{{ (ok : bool), RET #ok; True }}}.
Proof using heapGS0 mvcc_ghostG0 Σ.
  iIntros "#Hinv #Hmgr" (Φ) "!> _ HΦ".
  wp_rec. wp_pures.

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
  iExists {[ (W64 1) := v1 ]}.
  (* Give atomic precondition *)
  unfold dbmap_ptstos. rewrite {1} big_sepM_singleton.
  iFrame.
  iSplit.
  { iPureIntro. unfold P_WriteFreeKey. set_solver. }
  (* Take atomic precondition *)
  iIntros (ok w) "H".
  iMod "Hclose" as "_".

  (***********************************************************)
  (* return ok                                               *)
  (***********************************************************)
  destruct ok eqn:E.
  { (* Case COMMIT. *)
    iDestruct "H" as "[%HQ Hdbpt1]".
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
