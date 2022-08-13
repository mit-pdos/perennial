From iris.base_logic Require Import mono_nat.
(* This should go first otherwise the default scope becomes nat. *)
From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.go_mvcc Require Import examples.
From Perennial.program_proof.mvcc Require Import txn_proof.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ, !mono_natG Σ}.

#[local]
Definition mvcc_inv_app_def γ α : iProp Σ :=
  ∃ (v : u64),
    "Hdbpt" ∷ dbmap_ptsto γ (U64 0) 1 (Value v) ∗
    "Hmn"   ∷ mono_nat_auth_own α 1 (int.nat v).

Instance mvcc_inv_app_timeless γ α :
  Timeless (mvcc_inv_app_def γ α).
Proof. unfold mvcc_inv_app_def. apply _. Defined.

#[local]
Definition mvccNApp := nroot .@ "app".
#[local]
Definition mvcc_inv_app γ α : iProp Σ :=
  inv mvccNApp (mvcc_inv_app_def γ α).

Definition P_Increment (r : dbmap) := ∃ v, r = {[ (U64 0) := (Value v) ]}.
Definition Q_Increment (r w : dbmap) :=
  ∃ (v u : u64),
    r !! (U64 0) = Some (Value v) ∧
    w !! (U64 0) = Some (Value u) ∧
    int.Z u = int.Z v + 1.
Definition Rc_Increment (r w : dbmap) : iProp Σ := True.
Definition Ra_Increment (r : dbmap) : iProp Σ := True.

(**
 * [p] is not used until [R/R1/R2] are added to [wp_txn__DoTxn].
 *)
Theorem wp_IncrementSeq txn (p : loc) tid r γ τ :
  {{{ own_txn txn tid r γ τ ∗ ⌜P_Increment r⌝ ∗ txnmap_ptstos τ r }}}
    IncrementSeq #txn #p
  {{{ (ok : bool), RET #ok;
      own_txn txn tid r γ τ ∗
      if ok
      then ∃ w, ⌜Q_Increment r w ∧ dom r = dom w⌝ ∗
                (Rc_Increment r w ∧ Ra_Increment r) ∗
                txnmap_ptstos τ w
      else Ra_Increment r
  }}}.
Proof.
  iIntros (Φ) "(Htxn & %HP & Hpt) HΦ".
  wp_call.

  (***********************************************************)
  (* v, _ := txn.Get(0)                                      *)
  (***********************************************************)
  destruct HP as [v Hr].
  unfold txnmap_ptstos.
  rewrite {2} Hr.
  rewrite big_sepM_singleton.
  wp_apply (wp_txn__Get with "[$Htxn $Hpt]").
  iIntros (v' found).
  iIntros "(Htxn & Hpt & %Hv)".
  (* From the precondition we know [found] can only be [true]. *)
  unfold to_dbval in Hv. destruct found; last done.
  inversion Hv.
  subst v'.
  wp_pures.

  (***********************************************************)
  (* if v == 18446744073709551615 {                          *)
  (*     return false                                        *)
  (* }                                                       *)
  (***********************************************************)
  wp_if_destruct.
  { iApply "HΦ". by iFrame. }

  (***********************************************************)
  (* txn.Put(0, v + 1)                                       *)
  (***********************************************************)
  wp_apply (wp_txn__Put with "[$Htxn $Hpt]").
  iIntros "[Htxn Hpt]".
  wp_pures.

  (***********************************************************)
  (* return true                                             *)
  (***********************************************************)
  iApply "HΦ".
  rewrite -big_sepM_singleton.
  iFrame "Htxn".
  iExists _. iFrame "Hpt".
  iPureIntro.
  split; last done.
  split; last set_solver.
  unfold Q_Increment.
  eexists _, _.
  split.
  { rewrite Hr. by rewrite lookup_singleton. }
  split.
  { by rewrite lookup_singleton. }
  apply u64_val_ne in Heqb.
  word.
Qed.

Theorem wp_Increment (txn : loc) (p : loc) γ :
  ⊢ {{{ own_txn_uninit txn γ }}}
    <<< ∀∀ (r : dbmap), ⌜P_Increment r⌝ ∗ dbmap_ptstos γ 1 r >>>
      Increment #txn #p @ ↑mvccNSST
    <<< ∃∃ (ok : bool) (w : dbmap), if ok then ⌜Q_Increment r w⌝ ∗ dbmap_ptstos γ 1 w else dbmap_ptstos γ 1 r >>>
    {{{ RET #ok; own_txn_uninit txn γ ∗ if ok then Rc_Increment r w else Ra_Increment r }}}.
Proof.
  iIntros "!>".
  iIntros (Φ) "Htxn HAU".
  wp_call.

  (***********************************************************)
  (* body := func(txn *txn.Txn) bool {                       *) 
  (*     return DecrementSeq(txn, p)                         *) 
  (* }                                                       *) 
  (* return t.DoTxn(body)                                    *) 
  (***********************************************************)
  wp_apply (wp_txn__DoTxn _ _ _ Q_Increment Rc_Increment Ra_Increment with "[$Htxn]").
  { unfold spec_body.
    iIntros (tid r τ Φ') "HP HΦ'".
    wp_pures.
    unfold Rc_Increment, Ra_Increment.
    iApply (wp_IncrementSeq with "HP HΦ'").
  }
  done.
Qed.

Definition P_Decrement (r : dbmap) := ∃ v, r = {[ (U64 0) := (Value v) ]}.
Definition Q_Decrement (r w : dbmap) :=
  ∃ (v u : u64),
    r !! (U64 0) = Some (Value v) ∧
    w !! (U64 0) = Some (Value u) ∧
    int.Z u = int.Z v - 1.
Definition Rc_Decrement (r w : dbmap) : iProp Σ := True.
Definition Ra_Decrement (r : dbmap) : iProp Σ := True.

(**
 * [p] is not used until [R/R1/R2] are added to [wp_txn__DoTxn].
 *)
Theorem wp_DecrementSeq txn (p : loc) tid r γ τ :
  {{{ own_txn txn tid r γ τ ∗ ⌜P_Decrement r⌝ ∗ txnmap_ptstos τ r }}}
    DecrementSeq #txn #p
  {{{ (ok : bool), RET #ok;
      own_txn txn tid r γ τ ∗
      if ok
      then ∃ w, ⌜Q_Decrement r w ∧ dom r = dom w⌝ ∗
                (Rc_Decrement r w ∧ Ra_Decrement r) ∗
                txnmap_ptstos τ w
      else Ra_Decrement r
  }}}.
Proof.
  iIntros (Φ) "(Htxn & %HP & Hpt) HΦ".
  wp_call.

  (***********************************************************)
  (* v, _ := txn.Get(0)                                      *) 
  (***********************************************************)
  destruct HP as [v Hr].
  unfold txnmap_ptstos.
  rewrite {2} Hr.
  rewrite big_sepM_singleton.
  wp_apply (wp_txn__Get with "[$Htxn $Hpt]").
  iIntros (v' found).
  iIntros "(Htxn & Hpt & %Hv)".
  (* From the precondition we know [found] can only be [true]. *)
  unfold to_dbval in Hv. destruct found; last done.
  inversion Hv.
  subst v'.
  wp_pures.

  (***********************************************************)
  (* if v == 0 {                                             *) 
  (*     return false                                        *) 
  (* }                                                       *) 
  (***********************************************************)
  wp_if_destruct.
  { iApply "HΦ". by iFrame. }

  (***********************************************************)
  (* txn.Put(0, v + 1)                                       *)
  (***********************************************************)
  wp_apply (wp_txn__Put with "[$Htxn $Hpt]").
  iIntros "[Htxn Hpt]".
  wp_pures.

  (***********************************************************)
  (* return true                                             *)
  (***********************************************************)
  iApply "HΦ".
  rewrite -big_sepM_singleton.
  iFrame "Htxn".
  iExists _. iFrame "Hpt".
  iPureIntro.
  split; last done.
  split; last set_solver.
  unfold Q_Decrement.
  eexists _, _.
  split.
  { rewrite Hr. by rewrite lookup_singleton. }
  split.
  { by rewrite lookup_singleton. }
  apply u64_val_ne in Heqb.
  replace (int.Z 0) with 0 in Heqb by word.
  word.
Qed.

Theorem wp_Decrement (txn : loc) (p : loc) γ :
  ⊢ {{{ own_txn_uninit txn γ }}}
    <<< ∀∀ (r : dbmap), ⌜P_Decrement r⌝ ∗ dbmap_ptstos γ 1 r >>>
      Decrement #txn #p @ ↑mvccNSST
    <<< ∃∃ (ok : bool) (w : dbmap), if ok then ⌜Q_Decrement r w⌝ ∗ dbmap_ptstos γ 1 w else dbmap_ptstos γ 1 r >>>
    {{{ RET #ok; own_txn_uninit txn γ ∗ if ok then Rc_Decrement r w else Ra_Decrement r }}}.
Proof.
  iIntros "!>".
  iIntros (Φ) "Htxn HAU".
  wp_call.

  (***********************************************************)
  (* body := func(txn *txn.Txn) bool {                       *) 
  (*     return DecrementSeq(txn, p)                         *) 
  (* }                                                       *) 
  (* return t.DoTxn(body)                                    *) 
  (***********************************************************)
  wp_apply (wp_txn__DoTxn _ _ _ Q_Decrement with "[$Htxn]").
  { unfold spec_body.
    iIntros (tid r τ Φ') "HP HΦ'".
    wp_pures.
    iApply (wp_DecrementSeq with "HP HΦ'").
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
  {{{ α, RET #(); mvcc_inv_app γ α }}}.
Proof.
Admitted.

Theorem wp_InitExample :
  {{{ True }}}
    InitExample #()
  {{{ γ α (mgr : loc), RET #mgr; is_txnmgr mgr γ ∗ mvcc_inv_app γ α }}}.
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
  iIntros (α) "#Hinv".
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iFrame "∗ #".
Qed.

Theorem wp_CallIncrement (mgr : loc) γ α :
  mvcc_inv_app γ α -∗
  is_txnmgr mgr γ -∗
  {{{ True }}}
    CallIncrement #mgr
  (* TODO: give lower bound of the counter. *)
  {{{ (v : u64) (ok : bool), RET (#v, #ok); True }}}.
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
  (* var n uint64                                            *)
  (* ok := Increment(txn, &n)                                *)
  (***********************************************************)
  wp_apply wp_ref_of_zero; first done.
  iIntros (vRef) "HvRef".
  wp_pures.
  wp_apply (wp_Increment with "Htxn").
  iInv "Hinv" as "> HinvO" "HinvC".
  iApply ncfupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iNamed "HinvO".
  (* Give atomic precondition. *)
  iExists {[ (U64 0) := (Some v) ]}.
  unfold dbmap_ptstos. rewrite {1} big_sepM_singleton.
  iFrame.
  iSplit.
  { iPureIntro. unfold P_Increment. by eauto. }
  (* Take atomic postcondition. *)
  iIntros (ok w) "H".
  iMod "Hclose" as "_".

  (***********************************************************)
  (* return v, ok                                            *)
  (***********************************************************)
  destruct ok eqn:E.
  { (* Case COMMIT. *)
    iDestruct "H" as "[%HQ Hdbpt]".
    unfold Q_Increment in HQ.
    destruct HQ as (v' & u' & Hlookupr & Hlookupw & Hvu).
    (* Show [v = v']. *)
    rewrite lookup_singleton in Hlookupr. inversion_clear Hlookupr.
    iDestruct (big_sepM_lookup with "Hdbpt") as "Hdbpt"; first apply Hlookupw.
    iMod (mono_nat_own_update (int.nat u') with "Hmn") as "[Hmn #Hmnlb]".
    { (* Show [int.nat v' ≤ int.nat u']. *) word. }
    iMod ("HinvC" with "[- HΦ HvRef]") as "_".
    { (* Close the invariant. *) iExists _. iFrame. }
    iIntros "!> Htxn".
    wp_load.
    wp_pures.
    iApply "HΦ".
    by iFrame.
  }
  { (* Case ABORT. *)
    unfold dbmap_ptstos. rewrite big_sepM_singleton.
    iMod ("HinvC" with "[- HΦ HvRef]") as "_".
    { (* Close the invariant. *) iExists _. iFrame. }
    iIntros "!> Htxn".
    wp_load.
    wp_pures.
    iApply "HΦ".
    by iFrame.
  }
Qed.

Theorem wp_CallDecrement (mgr : loc) γ α :
  mvcc_inv_app γ α -∗
  is_txnmgr mgr γ -∗
  {{{ True }}}
    CallDecrement #mgr
  {{{ (v : u64) (ok : bool), RET (#v, #ok); True }}}.
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
  (* var n uint64                                            *)
  (* ok := Decrement(txn, &n)                                *)
  (***********************************************************)
  wp_apply wp_ref_of_zero; first done.
  iIntros (vRef) "HvRef".
  wp_pures.
  wp_apply (wp_Decrement with "Htxn").
  iInv "Hinv" as "> HinvO" "HinvC".
  iApply ncfupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iNamed "HinvO".
  (* Give atomic precondition. *)
  iExists {[ (U64 0) := (Some v) ]}.
  unfold dbmap_ptstos. rewrite {1} big_sepM_singleton.
  iFrame.
  iSplit.
  { iPureIntro. unfold P_Decrement. by eauto. }
  (* Take atomic postcondition. *)
  iIntros (ok w) "H".
  iMod "Hclose" as "_".

  (***********************************************************)
  (* return n, ok                                            *)
  (***********************************************************)
  destruct ok eqn:E.
  { (* Case COMMIT. *)
    iDestruct "H" as "[%HQ Hdbpt]".
    unfold Q_Increment in HQ.
    destruct HQ as (v' & u' & Hlookupr & Hlookupw & Hvu).
    (* Show [v = v']. *)
    rewrite lookup_singleton in Hlookupr. inversion_clear Hlookupr.
    iDestruct (big_sepM_lookup with "Hdbpt") as "Hdbpt"; first apply Hlookupw.
    iMod (mono_nat_own_update (int.nat u') with "Hmn") as "[Hmn #Hmnlb]".
    { (* Cannot show [int.nat v' ≤ int.nat u']. *)
      Fail word.
Abort.

End program.
