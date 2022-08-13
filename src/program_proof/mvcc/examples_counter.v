(* [mono_nat] should go first otherwise the default scope becomes nat. *)
From iris.base_logic Require Import mono_nat.
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
Definition Ri_Increment (p : loc) : iProp Σ :=
  ∃ (v : u64), p ↦[uint64T] #v.
Definition Rc_Increment (p : loc) (r w : dbmap) : iProp Σ :=
  ∃ (v : u64), p ↦[uint64T] #v ∗ ⌜r !! (U64 0) = Some (Value v)⌝.
Definition Ra_Increment (p : loc) (r : dbmap) : iProp Σ :=
  ∃ (v : u64), p ↦[uint64T] #v ∗ ⌜r !! (U64 0) = Some (Value v)⌝.

Theorem wp_IncrementSeq txn (p : loc) tid r γ τ :
  {{{ Ri_Increment p ∗ own_txn txn tid r γ τ ∗ ⌜P_Increment r⌝ ∗ txnmap_ptstos τ r }}}
    IncrementSeq #txn #p
  {{{ (ok : bool), RET #ok;
      own_txn txn tid r γ τ ∗
      if ok
      then ∃ w, ⌜Q_Increment r w ∧ dom r = dom w⌝ ∗
                (Rc_Increment p r w ∧ Ra_Increment p r) ∗
                txnmap_ptstos τ w
      else Ra_Increment p r
  }}}.
Proof.
  iIntros (Φ) "(Hp & Htxn & %HP & Hpt) HΦ".
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
  (* *p = v                                                  *)
  (***********************************************************)
  iDestruct "Hp" as (u) "Hp".
  wp_store.

  (***********************************************************)
  (* if v == 18446744073709551615 {                          *)
  (*     return false                                        *)
  (* }                                                       *)
  (***********************************************************)
  wp_if_destruct.
  { iApply "HΦ". iFrame.
    iExists _. iFrame.
    iPureIntro. by rewrite lookup_singleton.
  }

  (***********************************************************)
  (* txn.Put(0, v + 1)                                       *)
  (***********************************************************)
  wp_apply (wp_txn__Put with "[$Htxn $Hpt]").
  iIntros "[Htxn Hpt]".
  wp_pures.

  (***********************************************************)
  (* return true                                             *)
  (***********************************************************)
  iModIntro.
  iApply "HΦ".
  rewrite -big_sepM_singleton.
  iFrame "Htxn".
  iExists _. iFrame "Hpt".
  iSplit.
  { iPureIntro. split; last set_solver.
    unfold Q_Increment.
    eexists _, _.
    split.
    { rewrite Hr. by rewrite lookup_singleton. }
    split.
    { by rewrite lookup_singleton. }
    apply u64_val_ne in Heqb.
    word.
  }
  unfold Rc_Increment, Ra_Increment.
  rewrite Hr lookup_singleton.
  iSplit; by eauto with iFrame.
Qed.

Theorem wp_Increment (txn : loc) γ :
  ⊢ {{{ own_txn_uninit txn γ }}}
    <<< ∀∀ (r : dbmap), ⌜P_Increment r⌝ ∗ dbmap_ptstos γ 1 r >>>
      Increment #txn @ ↑mvccNSST
    <<< ∃∃ (ok : bool) (w : dbmap), if ok then ⌜Q_Increment r w⌝ ∗ dbmap_ptstos γ 1 w else dbmap_ptstos γ 1 r >>>
    {{{ (v : u64), RET (#v, #ok);
        own_txn_uninit txn γ ∗ ⌜r !! (U64 0) = Some (Value v)⌝
    }}}.
Proof.
  iIntros "!>".
  iIntros (Φ) "Htxn HAU".
  wp_call.

  (***********************************************************)
  (* var n uint64                                            *)
  (***********************************************************)
  wp_apply wp_ref_of_zero; first done.
  iIntros (nRef) "HnRef".
  wp_pures.

  (***********************************************************)
  (* body := func(txn *txn.Txn) bool {                       *)
  (*     return IncrementSeq(txn, &n)                        *)
  (* }                                                       *)
  (* ok := t.DoTxn(body)                                     *)
  (* return n, ok                                            *)
  (***********************************************************)
  (* Move ownership of [n] to [DoTxn]. *)
  wp_apply (wp_txn__DoTxn
              _ _ P_Increment Q_Increment
              (Rc_Increment nRef) (Ra_Increment nRef) with "[$Htxn HnRef]").
  { unfold spec_body.
    iIntros (tid r τ Φ') "(Htxn & %HP & Htxnps) HΦ'".
    wp_pures.
    iApply (wp_IncrementSeq with "[$Htxn $Htxnps HnRef] HΦ'").
    { iSplit; last done. iExists _. iFrame. }
  }
  iMod "HAU".
  iModIntro.
  iDestruct "HAU" as (r) "[[%HP Hdbpts] HAU]".
  iExists _.
  iFrame "Hdbpts".
  iSplit; first done.
  iIntros (ok w) "Hpost".
  iMod ("HAU" with "Hpost") as "HΦ".
  iIntros "!> [Htxn HR]".
  wp_pures.
  destruct ok eqn:E.
  { (* Case COMMIT. *)
    unfold Rc_Increment. iDestruct "HR" as (v) "[HnRef %Hlookup]".
    wp_load.
    wp_pures.
    iApply "HΦ".
    by iFrame.
  }
  { (* Case ABORT. *)
    unfold Rc_Increment. iDestruct "HR" as (v) "[HnRef %Hlookup]".
    wp_load.
    wp_pures.
    iApply "HΦ".
    by iFrame.
  }
Qed.

Definition P_Decrement (r : dbmap) := ∃ v, r = {[ (U64 0) := (Value v) ]}.
Definition Q_Decrement (r w : dbmap) :=
  ∃ (v u : u64),
    r !! (U64 0) = Some (Value v) ∧
    w !! (U64 0) = Some (Value u) ∧
    int.Z u = int.Z v - 1.
Definition Ri_Decrement (p : loc) : iProp Σ :=
  ∃ (v : u64), p ↦[uint64T] #v.
Definition Rc_Decrement (p : loc) (r w : dbmap) : iProp Σ :=
  ∃ (v : u64), p ↦[uint64T] #v ∗ ⌜r !! (U64 0) = Some (Value v)⌝.
Definition Ra_Decrement (p : loc) (r : dbmap) : iProp Σ :=
  ∃ (v : u64), p ↦[uint64T] #v ∗ ⌜r !! (U64 0) = Some (Value v)⌝.

(**
 * [p] is not used until [R/R1/R2] are added to [wp_txn__DoTxn].
 *)
Theorem wp_DecrementSeq txn (p : loc) tid r γ τ :
  {{{ Ri_Decrement p ∗ own_txn txn tid r γ τ ∗ ⌜P_Decrement r⌝ ∗ txnmap_ptstos τ r }}}
    DecrementSeq #txn #p
  {{{ (ok : bool), RET #ok;
      own_txn txn tid r γ τ ∗
      if ok
      then ∃ w, ⌜Q_Decrement r w ∧ dom r = dom w⌝ ∗
                (Rc_Decrement p r w ∧ Ra_Decrement p r) ∗
                txnmap_ptstos τ w
      else Ra_Decrement p r
  }}}.
Proof.
  iIntros (Φ) "(Hp & Htxn & %HP & Hpt) HΦ".
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
  (* *p = v                                                  *)
  (***********************************************************)
  iDestruct "Hp" as (u) "Hp".
  wp_store.

  (***********************************************************)
  (* if v == 0 {                                             *)
  (*     return false                                        *)
  (* }                                                       *)
  (***********************************************************)
  wp_if_destruct.
  { iApply "HΦ". iFrame.
    iExists _. iFrame.
    iPureIntro. by rewrite lookup_singleton.
  }

  (***********************************************************)
  (* txn.Put(0, v - 1)                                       *)
  (***********************************************************)
  wp_apply (wp_txn__Put with "[$Htxn $Hpt]").
  iIntros "[Htxn Hpt]".
  wp_pures.

  (***********************************************************)
  (* return true                                             *)
  (***********************************************************)
  iModIntro.
  iApply "HΦ".
  rewrite -big_sepM_singleton.
  iFrame "Htxn".
  iExists _. iFrame "Hpt".
  iSplit.
  { iPureIntro. split; last set_solver.
    unfold Q_Increment.
    eexists _, _.
    split.
    { rewrite Hr. by rewrite lookup_singleton. }
    split.
    { by rewrite lookup_singleton. }
    apply u64_val_ne in Heqb.
    replace (int.Z 0) with 0 in Heqb by word.
    word.
  }
  unfold Rc_Decrement, Ra_Decrement.
  rewrite Hr lookup_singleton.
  iSplit; by eauto with iFrame.
Qed.

Theorem wp_Decrement (txn : loc) γ :
  ⊢ {{{ own_txn_uninit txn γ }}}
    <<< ∀∀ (r : dbmap), ⌜P_Decrement r⌝ ∗ dbmap_ptstos γ 1 r >>>
      Decrement #txn @ ↑mvccNSST
    <<< ∃∃ (ok : bool) (w : dbmap), if ok then ⌜Q_Decrement r w⌝ ∗ dbmap_ptstos γ 1 w else dbmap_ptstos γ 1 r >>>
    {{{ (v : u64), RET (#v, #ok);
        own_txn_uninit txn γ ∗ ⌜r !! (U64 0) = Some (Value v)⌝
    }}}.
Proof.
  iIntros "!>".
  iIntros (Φ) "Htxn HAU".
  wp_call.

  (***********************************************************)
  (* var n uint64                                            *)
  (***********************************************************)
  wp_apply wp_ref_of_zero; first done.
  iIntros (nRef) "HnRef".
  wp_pures.

  (***********************************************************)
  (* body := func(txn *txn.Txn) bool {                       *)
  (*     return IncrementSeq(txn, &n)                        *)
  (* }                                                       *)
  (* ok := t.DoTxn(body)                                     *)
  (* return n, ok                                            *)
  (***********************************************************)
  (* Move ownership of [n] to [DoTxn]. *)
  wp_apply (wp_txn__DoTxn
              _ _ P_Decrement Q_Decrement
              (Rc_Decrement nRef) (Ra_Decrement nRef) with "[$Htxn HnRef]").
  { unfold spec_body.
    iIntros (tid r τ Φ') "(Htxn & %HP & Htxnps) HΦ'".
    wp_pures.
    iApply (wp_DecrementSeq with "[$Htxn $Htxnps HnRef] HΦ'").
    { iSplit; last done. iExists _. iFrame. }
  }
  iMod "HAU".
  iModIntro.
  iDestruct "HAU" as (r) "[[%HP Hdbpts] HAU]".
  iExists _.
  iFrame "Hdbpts".
  iSplit; first done.
  iIntros (ok w) "Hpost".
  iMod ("HAU" with "Hpost") as "HΦ".
  iIntros "!> [Htxn HR]".
  wp_pures.
  destruct ok eqn:E.
  { (* Case COMMIT. *)
    unfold Rc_Decrement. iDestruct "HR" as (v) "[HnRef %Hlookup]".
    wp_load.
    wp_pures.
    iApply "HΦ".
    by iFrame.
  }
  { (* Case ABORT. *)
    unfold Rc_Decrement. iDestruct "HR" as (v) "[HnRef %Hlookup]".
    wp_load.
    wp_pures.
    iApply "HΦ".
    by iFrame.
  }
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

(**
 * The purpose of this example is to show [Increment] *can* be called
 * under invariant [mvcc_inv_app].
 *)
Theorem wp_CallIncrement (mgr : loc) γ α :
  mvcc_inv_app γ α -∗
  is_txnmgr mgr γ -∗
  {{{ True }}}
    CallIncrement #mgr
  {{{ RET #(); True }}}.
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
  (* Increment(txn)                                          *)
  (***********************************************************)
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
    iMod ("HinvC" with "[- HΦ]") as "_".
    { (* Close the invariant. *) iExists _. iFrame. }
    iIntros "!>" (u) "Htxn".
    wp_pures.
    by iApply "HΦ".
  }
  { (* Case ABORT. *)
    unfold dbmap_ptstos. rewrite big_sepM_singleton.
    iMod ("HinvC" with "[- HΦ]") as "_".
    { (* Close the invariant. *) iExists _. iFrame. }
    iIntros "!>" (u) "Htxn".
    wp_pures.
    by iApply "HΦ".
  }
Qed.

(**
 * The purpose of this example is to show [Decrement] *cannot* be
 * called under invariant [mvcc_inv_app].
 *)
Theorem wp_CallDecrement (mgr : loc) γ α :
  mvcc_inv_app γ α -∗
  is_txnmgr mgr γ -∗
  {{{ True }}}
    CallDecrement #mgr
  {{{RET #(); True }}}.
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
  (* Decrement(txn)                                          *)
  (***********************************************************)
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

(**
 * The purpose of this example is to show that, under invariant
 * [mvcc_inv_app], the counter value strictly increases when the txn
 * successfully commits.
 *)
Theorem wp_CallIncrementTwice (mgr : loc) γ α :
  mvcc_inv_app γ α -∗
  is_txnmgr mgr γ -∗
  {{{ True }}}
    CallIncrementTwice #mgr
  {{{ RET #(); True }}}.
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
  (* n1, ok1 := Increment(txn)                               *)
  (***********************************************************)
  wp_apply (wp_Increment with "Htxn").
  iInv "Hinv" as "> HinvO" "HinvC".
  iApply ncfupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iNamed "HinvO".
  (* Give atomic precondition. *)
  iExists {[ (U64 0) := (Some v) ]}.
  rewrite {1} /dbmap_ptstos. rewrite {1} big_sepM_singleton.
  iFrame.
  iSplit.
  { iPureIntro. unfold P_Increment. by eauto. }
  (* Take atomic postcondition. *)
  iIntros (ok w) "H".
  iMod "Hclose" as "_".
  (* Merge. *)
  iAssert (
      |==> mvcc_inv_app_def γ α ∗
           if ok then mono_nat_lb_own α (S (int.nat v)) else True
    )%I with "[Hmn H]" as "H".
  { destruct ok eqn:E.
    { (* Case COMMIT. *)
      iDestruct "H" as "[%HQ Hdbpt]".
      unfold Q_Increment in HQ.
      destruct HQ as (v' & u & Hlookupr & Hlookupw & Hvu).
      (* Show [v = v']. *)
      rewrite lookup_singleton in Hlookupr. inversion Hlookupr. subst v'.
      iDestruct (big_sepM_lookup with "Hdbpt") as "Hdbpt"; first apply Hlookupw.
      iMod (mono_nat_own_update (int.nat u) with "Hmn") as "[Hmn #Hmnlb]".
      { (* Show [int.nat v ≤ int.nat u]. *) word. }
      replace (S (int.nat v)) with (int.nat u) by word.
      iFrame "Hmnlb". iExists _. by iFrame.
    }
    { (* Case ABORT. *)
      rewrite /dbmap_ptstos big_sepM_singleton.
      iModIntro. iSplit; last done.
      iExists _. by iFrame.
    }
  }
  (* Q: Can we directly introduce [#Hmnlb]? *)
  iMod "H" as "[HinvO Hmnlb]".
  iMod ("HinvC" with "[- HΦ Hmnlb]") as "_"; first done.
  iIntros "!>" (n1) "[Htxn %Hlookup]".
  wp_pures.
  (* Deduce [n1 = v]. *)
  rewrite lookup_singleton in Hlookup.
  inversion Hlookup. subst v. clear Hlookup.

  (***********************************************************)
  (* if !ok1 {                                               *)
  (*     return                                              *)
  (* }                                                       *)
  (***********************************************************)
  wp_if_destruct.
  { by iApply "HΦ". }
  iDestruct "Hmnlb" as "#Hmnlb".

  (***********************************************************)
  (* n2, _ := Increment(txn)                                 *)
  (***********************************************************)
  wp_apply (wp_Increment with "Htxn").
  iInv "Hinv" as "> HinvO" "HinvC".
  iApply ncfupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iNamed "HinvO".
  (* Deduce [S (int.nat n1) ≤ int.nat v], which we'll need for the assertion below. *)
  iDestruct (mono_nat_lb_own_valid with "Hmn Hmnlb") as "%H".
  (* The following will consume [Hmn], so we do a separate [destruct]. *)
  (* iDestruct (mono_nat_lb_own_valid with "Hmn Hmnlb") as "[_ %H]". *)
  destruct H as [_ Hle].
  (* Give atomic precondition. *)
  iExists {[ (U64 0) := (Some v) ]}.
  rewrite {1} /dbmap_ptstos. rewrite {1} big_sepM_singleton.
  iFrame.
  iSplit.
  { iPureIntro. unfold P_Increment. by eauto. }
  (* Take atomic postcondition. *)
  iIntros (ok w') "H".
  iMod "Hclose" as "_".
  (* Merge. *)
  iAssert (|==> mvcc_inv_app_def γ α)%I with "[Hmn H]" as "HinvO".
  { destruct ok eqn:E.
    { (* Case COMMIT. *)
      iDestruct "H" as "[%HQ Hdbpt]".
      unfold Q_Increment in HQ.
      destruct HQ as (v' & u & Hlookupr & Hlookupw & Hvu).
      (* Show [v = v']. *)
      rewrite lookup_singleton in Hlookupr. inversion Hlookupr. subst v'.
      iDestruct (big_sepM_lookup with "Hdbpt") as "Hdbpt"; first apply Hlookupw.
      iMod (mono_nat_own_update (int.nat u) with "Hmn") as "[Hmn _]".
      { (* Show [int.nat v ≤ int.nat u]. *) word. }
      iExists _. by iFrame.
    }
    { (* Case ABORT. *)
      rewrite /dbmap_ptstos big_sepM_singleton.
      iExists _. by iFrame.
    }
  }
  iMod "HinvO" as "HinvO".
  iMod ("HinvC" with "[- HΦ]") as "_"; first done.
  iIntros "!>" (n2) "[Htxn %Hlookup]".
  wp_pures.
  (* Deduce [n2 = v]. *)
  rewrite lookup_singleton in Hlookup.
  inversion Hlookup. subst v. clear Hlookup.

  (***********************************************************)
  (* machine.Assert(n1 < n2)                                 *)
  (***********************************************************)
  wp_apply wp_Assert.
  { (* Prove [int.Z n1 < int.Z n2]. *) rewrite bool_decide_eq_true. word. }
  wp_pures.
  by iApply "HΦ".
Qed.

End program.
