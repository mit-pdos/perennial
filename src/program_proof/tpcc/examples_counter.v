(* [mono_nat] must go first otherwise the default scope becomes nat. *)
From iris.base_logic Require Import mono_nat.
From Perennial.program_proof.mvcc Require Import
     mvcc_prelude mvcc_ghost mvcc_inv
     db_repr db_mk db_new_txn
     txn_repr txn_read txn_write txn_run.
From Goose.github_com.mit_pdos.vmvcc Require Import examples.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ, !mono_natG Σ}.

Definition P_Fetch (r : dbmap) := ∃ v, r = {[ (W64 0) := (Value v) ]}.
Definition Q_Fetch (r w : dbmap) := w !! (W64 0) = r !! (W64 0).
Definition Ri_Fetch (p : loc) : iProp Σ :=
  ∃ (v : u64), p ↦[uint64T] #v.
Definition Rc_Fetch (p : loc) (r w : dbmap) : iProp Σ :=
  ∃ (v : u64), p ↦[uint64T] #v ∗ ⌜r !! (W64 0) = Some (Value v)⌝.
Definition Ra_Fetch (p : loc) (r : dbmap) : iProp Σ :=
  ∃ (v : u64), p ↦[uint64T] #v ∗ ⌜r !! (W64 0) = Some (Value v)⌝.

Theorem wp_fetch txn (p : loc) tid r γ τ :
  {{{ Ri_Fetch p ∗ own_txn txn tid r γ τ ∗ ⌜P_Fetch r⌝ ∗ txnmap_ptstos τ r }}}
    fetch #txn #p
  {{{ (ok : bool), RET #ok;
      own_txn txn tid r γ τ ∗
      if ok
      then ∃ w, ⌜Q_Fetch r w ∧ dom r = dom w⌝ ∗
                (Rc_Fetch p r w ∧ Ra_Fetch p r) ∗
                txnmap_ptstos τ w
      else Ra_Fetch p r
  }}}.
Proof.
  iIntros (Φ) "(Hp & Htxn & %HP & Hpt) HΦ".
  wp_rec. wp_pures.

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
  (* return true                                             *)
  (***********************************************************)
  iModIntro.
  iApply "HΦ".
  iFrame "Htxn".
  rewrite -big_sepM_singleton.
  iExists _. iFrame "Hpt".
  iSplit.
  { iPureIntro. split; last set_solver.
    unfold Q_Fetch.
    set_solver.
  }
  unfold Rc_Fetch, Ra_Fetch.
  rewrite Hr lookup_singleton_eq.
  iSplit; by eauto with iFrame.
Qed.

Theorem wp_Fetch (txn : loc) γ :
  ⊢ {{{ own_txn_uninit txn γ }}}
    <<< ∀∀ (v : u64), dbmap_ptsto γ (W64 0) 1 (Value v) >>>
      Fetch #txn @ ↑mvccN
    <<< dbmap_ptsto γ (W64 0) 1 (Value v) >>>
    {{{ RET #v; own_txn_uninit txn γ }}}.
Proof.
  iIntros "!>".
  iIntros (Φ) "Htxn HAU".
  wp_rec. wp_pures.

  (***********************************************************)
  (* var n uint64                                            *)
  (***********************************************************)
  wp_apply wp_ref_of_zero; first done.
  iIntros (nRef) "HnRef".
  wp_pures.

  (***********************************************************)
  (* body := func(txn *txn.Txn) bool {                       *)
  (*     return fetch(txn, &n)                               *)
  (* }                                                       *)
  (* ok := t.DoTxn(body)                                     *)
  (* return n, ok                                            *)
  (***********************************************************)
  (* Move ownership of [n] to [DoTxn]. *)
  wp_apply (wp_txn__DoTxn
              _ _ P_Fetch Q_Fetch
              (Rc_Fetch nRef) (Ra_Fetch nRef) with "[$Htxn HnRef]").
  { unfold Q_Fetch. apply _. }
  { unfold spec_body.
    iIntros (tid r τ Φ') "(Htxn & %HP & Htxnps) HΦ'".
    wp_pures.
    iApply (wp_fetch with "[$Htxn $Htxnps HnRef] HΦ'").
    { iSplit; last done. iExists _. iFrame. }
  }
  iMod "HAU".
  iModIntro.
  iDestruct "HAU" as (v) "[Hdbpt HAU]".
  iExists {[ (W64 0) := (Value v) ]}.
  rewrite {1} /dbmap_ptstos. rewrite big_sepM_singleton.
  iFrame "Hdbpt".
  iSplit.
  { iPureIntro. unfold P_Fetch. by eauto. }
  iIntros (ok w) "H".

  (* Apply the view shift. *)
  destruct ok eqn:E.
  { (* Case COMMIT. *)
    iDestruct "H" as "[%HQ Hdbpt]".
    unfold Q_Fetch in HQ.
    rewrite lookup_singleton_eq in HQ.
    iDestruct (big_sepM_lookup with "Hdbpt") as "Hdbpt"; first apply HQ.
    iMod ("HAU" with "Hdbpt") as "HΦ".
    iIntros "!> [Htxn HR]".
    wp_pures.
    iDestruct "HR" as (v') "[HnRef %Hlookup]".
    rewrite lookup_singleton_eq in Hlookup.
    inversion Hlookup. subst v'.
    wp_load.
    iApply "HΦ".
    by iFrame.
  }
  { (* Case ABORT. *)
    iRename "H" into "Hdbpt".
    unfold dbmap_ptstos. rewrite big_sepM_singleton.
    iMod ("HAU" with "Hdbpt") as "HΦ".
    iIntros "!> [Htxn HR]".
    wp_pures.
    iDestruct "HR" as (v') "[HnRef %Hlookup]".
    rewrite lookup_singleton_eq in Hlookup.
    inversion Hlookup. subst v'.
    wp_load.
    iApply "HΦ".
    by iFrame.
  }
Qed.

Definition P_Increment (r : dbmap) := ∃ v, r = {[ (W64 0) := (Value v) ]}.
Definition Q_Increment (r w : dbmap) :=
  ∃ (v u : u64),
    r !! (W64 0) = Some (Value v) ∧
    w !! (W64 0) = Some (Value u) ∧
    uint.Z u = uint.Z v + 1.
Definition Ri_Increment (p : loc) : iProp Σ :=
  ∃ (v : u64), p ↦[uint64T] #v.
Definition Rc_Increment (p : loc) (r w : dbmap) : iProp Σ :=
  ∃ (v : u64), p ↦[uint64T] #v ∗ ⌜r !! (W64 0) = Some (Value v)⌝.
Definition Ra_Increment (p : loc) (r : dbmap) : iProp Σ :=
  ∃ (v : u64), p ↦[uint64T] #v ∗ ⌜r !! (W64 0) = Some (Value v)⌝.

Theorem wp_increment txn (p : loc) tid r γ τ :
  {{{ Ri_Increment p ∗ own_txn txn tid r γ τ ∗ ⌜P_Increment r⌝ ∗ txnmap_ptstos τ r }}}
    increment #txn #p
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
  wp_rec. wp_pures.

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
    iPureIntro. by rewrite lookup_singleton_eq.
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
    { rewrite Hr. by rewrite lookup_singleton_eq. }
    split.
    { by rewrite lookup_singleton_eq. }
    apply u64_val_ne in Heqb.
    word.
  }
  unfold Rc_Increment, Ra_Increment.
  rewrite Hr lookup_singleton_eq.
  iSplit; by eauto with iFrame.
Qed.

Theorem wp_Increment (txn : loc) γ :
  ⊢ {{{ own_txn_uninit txn γ }}}
    <<< ∀∀ (v : u64), dbmap_ptsto γ (W64 0) 1 (Value v) >>>
      Increment #txn @ ↑mvccN
    <<< ∃∃ (ok : bool),
          if ok
          then ∃ (u : u64), dbmap_ptsto γ (W64 0) 1 (Value u) ∗ ⌜uint.Z u = (uint.Z v + 1)%Z⌝
          else dbmap_ptsto γ (W64 0) 1 (Value v)
    >>>
    {{{ RET (#v, #ok); own_txn_uninit txn γ }}}.
Proof.
  iIntros "!>".
  iIntros (Φ) "Htxn HAU".
  wp_rec. wp_pures.

  (***********************************************************)
  (* var n uint64                                            *)
  (***********************************************************)
  wp_apply wp_ref_of_zero; first done.
  iIntros (nRef) "HnRef".
  wp_pures.

  (***********************************************************)
  (* body := func(txn *txn.Txn) bool {                       *)
  (*     return increment(txn, &n)                           *)
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
    iApply (wp_increment with "[$Htxn $Htxnps HnRef] HΦ'").
    { iSplit; last done. iExists _. iFrame. }
  }
  iMod "HAU".
  iModIntro.
  iDestruct "HAU" as (v) "[Hdbpt HAU]".
  iExists {[ (W64 0) := (Value v) ]}.
  rewrite {1} /dbmap_ptstos. rewrite big_sepM_singleton.
  iFrame "Hdbpt".
  iSplit.
  { iPureIntro. unfold P_Increment. by eauto. }
  iIntros (ok w) "H".

  (* Apply the view shift. *)
  destruct ok eqn:E.
  { (* Case COMMIT. *)
    iDestruct "H" as "[%HQ Hdbpt]".
    unfold Q_Increment in HQ.
    destruct HQ as (v' & u & Hlookupr & Hlookupw & Hrel).
    rewrite lookup_singleton_eq in Hlookupr.
    inversion Hlookupr. subst v'.
    iDestruct (big_sepM_lookup with "Hdbpt") as "Hdbpt"; first apply Hlookupw.
    iMod ("HAU" $! true with "[Hdbpt]") as "HΦ"; first by eauto with iFrame.
    iIntros "!> [Htxn HR]".
    wp_pures.
    iDestruct "HR" as (v') "[HnRef %Hlookup]".
    rewrite lookup_singleton_eq in Hlookup.
    inversion Hlookup. subst v'.
    wp_load.
    wp_pures.
    iApply "HΦ".
    by iFrame.
  }
  { (* Case ABORT. *)
    iRename "H" into "Hdbpt".
    unfold dbmap_ptstos. rewrite big_sepM_singleton.
    iMod ("HAU" $! false with "Hdbpt") as "HΦ".
    iIntros "!> [Htxn HR]".
    wp_pures.
    iDestruct "HR" as (v') "[HnRef %Hlookup]".
    rewrite lookup_singleton_eq in Hlookup.
    inversion Hlookup. subst v'.
    wp_load.
    wp_pures.
    iApply "HΦ".
    by iFrame.
  }
Qed.

Definition P_Decrement (r : dbmap) := ∃ v, r = {[ (W64 0) := (Value v) ]}.
Definition Q_Decrement (r w : dbmap) :=
  ∃ (v u : u64),
    r !! (W64 0) = Some (Value v) ∧
    w !! (W64 0) = Some (Value u) ∧
    uint.Z u = uint.Z v - 1.
Definition Ri_Decrement (p : loc) : iProp Σ :=
  ∃ (v : u64), p ↦[uint64T] #v.
Definition Rc_Decrement (p : loc) (r w : dbmap) : iProp Σ :=
  ∃ (v : u64), p ↦[uint64T] #v ∗ ⌜r !! (W64 0) = Some (Value v)⌝.
Definition Ra_Decrement (p : loc) (r : dbmap) : iProp Σ :=
  ∃ (v : u64), p ↦[uint64T] #v ∗ ⌜r !! (W64 0) = Some (Value v)⌝.

Theorem wp_decrement txn (p : loc) tid r γ τ :
  {{{ Ri_Decrement p ∗ own_txn txn tid r γ τ ∗ ⌜P_Decrement r⌝ ∗ txnmap_ptstos τ r }}}
    decrement #txn #p
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
  wp_rec. wp_pures.

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
    iPureIntro. by rewrite lookup_singleton_eq.
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
    unfold Q_Decrement.
    eexists _, _.
    split.
    { rewrite Hr. by rewrite lookup_singleton_eq. }
    split.
    { by rewrite lookup_singleton_eq. }
    apply u64_val_ne in Heqb.
    replace (uint.Z 0) with 0 in Heqb by word.
    word.
  }
  unfold Rc_Decrement, Ra_Decrement.
  rewrite Hr lookup_singleton_eq.
  iSplit; by eauto with iFrame.
Qed.

Theorem wp_Decrement (txn : loc) γ :
  ⊢ {{{ own_txn_uninit txn γ }}}
    <<< ∀∀ (v : u64), dbmap_ptsto γ (W64 0) 1 (Value v) >>>
      Decrement #txn @ ↑mvccN
    <<< ∃∃ (ok : bool),
          if ok
          then ∃ (u : u64), dbmap_ptsto γ (W64 0) 1 (Value u) ∗ ⌜uint.Z u = (uint.Z v - 1)%Z⌝
          else dbmap_ptsto γ (W64 0) 1 (Value v)
    >>>
    {{{ RET (#v, #ok); own_txn_uninit txn γ }}}.
Proof.
  iIntros "!>".
  iIntros (Φ) "Htxn HAU".
  wp_rec. wp_pures.

  (***********************************************************)
  (* var n uint64                                            *)
  (***********************************************************)
  wp_apply wp_ref_of_zero; first done.
  iIntros (nRef) "HnRef".
  wp_pures.

  (***********************************************************)
  (* body := func(txn *txn.Txn) bool {                       *)
  (*     return decrement(txn, &n)                           *)
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
    iApply (wp_decrement with "[$Htxn $Htxnps HnRef] HΦ'").
    { iSplit; last done. iExists _. iFrame. }
  }
  iMod "HAU".
  iModIntro.
  iDestruct "HAU" as (v) "[Hdbpt HAU]".
  iExists {[ (W64 0) := (Value v) ]}.
  rewrite {1} /dbmap_ptstos. rewrite big_sepM_singleton.
  iFrame "Hdbpt".
  iSplit.
  { iPureIntro. unfold P_Decrement. by eauto. }
  iIntros (ok w) "H".

  (* Apply the view shift. *)
  destruct ok eqn:E.
  { (* Case COMMIT. *)
    iDestruct "H" as "[%HQ Hdbpt]".
    unfold Q_Decrement in HQ.
    destruct HQ as (v' & u & Hlookupr & Hlookupw & Hrel).
    rewrite lookup_singleton_eq in Hlookupr.
    inversion Hlookupr. subst v'.
    iDestruct (big_sepM_lookup with "Hdbpt") as "Hdbpt"; first apply Hlookupw.
    iMod ("HAU" $! true with "[Hdbpt]") as "HΦ"; first by eauto with iFrame.
    iIntros "!> [Htxn HR]".
    wp_pures.
    iDestruct "HR" as (v') "[HnRef %Hlookup]".
    rewrite lookup_singleton_eq in Hlookup.
    inversion Hlookup. subst v'.
    wp_load.
    wp_pures.
    iApply "HΦ".
    by iFrame.
  }
  { (* Case ABORT. *)
    iRename "H" into "Hdbpt".
    unfold dbmap_ptstos. rewrite big_sepM_singleton.
    iMod ("HAU" $! false with "Hdbpt") as "HΦ".
    iIntros "!> [Htxn HR]".
    wp_pures.
    iDestruct "HR" as (v') "[HnRef %Hlookup]".
    rewrite lookup_singleton_eq in Hlookup.
    inversion Hlookup. subst v'.
    wp_load.
    wp_pures.
    iApply "HΦ".
    by iFrame.
  }
Qed.

(* Application-specific invariants. *)
#[local]
Definition mvcc_inv_app_def γ α : iProp Σ :=
  ∃ (v : u64),
    "Hdbpt" ∷ dbmap_ptsto γ (W64 0) 1 (Value v) ∗
    "Hmn"   ∷ mono_nat_auth_own α 1 (uint.nat v).

Instance mvcc_inv_app_timeless γ α :
  Timeless (mvcc_inv_app_def γ α).
Proof. unfold mvcc_inv_app_def. apply _. Defined.

#[local]
Definition mvccNApp := nroot .@ "app".
#[local]
Definition mvcc_inv_app γ α : iProp Σ :=
  inv mvccNApp (mvcc_inv_app_def γ α).

(*****************************************************************)
(* func InitializeCounterData(txnmgr *txn.TxnMgr)                *)
(*****************************************************************)
Theorem wp_InitializeCounterData (db : loc) γ :
  is_db db γ -∗
  {{{ dbmap_ptstos γ 1 (gset_to_gmap Nil keys_all) }}}
    InitializeCounterData #db
  {{{ α, RET #(); mvcc_inv_app γ α }}}.
Proof.
  iIntros "#Hdb" (Φ) "!> Hdbpts HΦ".
  wp_rec. wp_pures.

  (***********************************************************)
  (* body := func(txn *txn.Txn) bool {                       *)
  (*     txn.Put(0, 0)                                       *)
  (*     return true                                         *)
  (* }                                                       *)
  (* t := mgr.New()                                          *)
  (* for !t.DoTxn(body) {                                    *)
  (* }                                                       *)
  (***********************************************************)
  wp_apply (wp_DB__NewTxn with "Hdb").
  iIntros (txn) "Htxn".
  wp_pures.
  set P := (λ (b : bool),
              own_txn_uninit txn γ ∗
              if b
              then dbmap_ptsto γ (W64 0) 1 Nil
              else ∃ v, dbmap_ptsto γ (W64 0) 1 (Value v)
           )%I.
  wp_apply (wp_forBreak_cond P with "[] [Htxn Hdbpts]").
  { clear Φ.
    iIntros (Φ) "!> HP HΦ".
    subst P. simpl.
    iDestruct "HP" as "[Htxn Hdbpt]".
    wp_pures.
    set P := (λ r : dbmap, dom r = {[ (W64 0) ]}).
    set Q := (λ r w : dbmap, ∃ u, w !! (W64 0) = Some (Value u)).
    wp_apply (wp_txn__DoTxn_xres _ _ P Q with "[$Htxn]").
    { (* Txn body. *)
      iIntros (tid r τ).
      unfold spec_body_xres.
      clear Φ.
      iIntros (Φ) "(Htxn & %HP & Htxnpt) HΦ".
      subst P. simpl in HP. unfold txnmap_ptstos.
      apply dom_singleton_inv_L in HP as [u Hr]. subst r.
      rewrite big_sepM_singleton.
      wp_pures.
      wp_apply (wp_txn__Put with "[$Htxn $Htxnpt]").
      iIntros "[Htxn Htxnpt]".
      wp_pures.
      iApply "HΦ".
      iFrame "Htxn".
      subst Q. simpl.
      iModIntro.
      iExists {[ (W64 0) := Value (W64 0) ]}.
      iSplit; last by rewrite big_sepM_singleton.
      iPureIntro.
      split; last set_solver.
      rewrite lookup_singleton_eq.
      by eauto.
    }
    (* Give [dbmap_ptsto] owned exclusively. *)
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hclose".
    iExists {[ (W64 0) := Nil ]}.
    iSplitL "Hdbpt".
    { subst P. simpl.
      unfold dbmap_ptstos.
      rewrite big_sepM_singleton.
      iFrame.
      iPureIntro. set_solver.
    }
    iIntros (ok w) "Hpost".
    iMod "Hclose" as "_".
    destruct ok eqn:Eok.
    { (* Case success. *)
      iIntros "!> Htxn".
      wp_pures.
      subst Q. simpl.
      iDestruct "Hpost" as "[%HQ Hdbpt]".
      destruct HQ as [u Hlookup].
      iApply "HΦ".
      unfold dbmap_ptstos.
      iDestruct (big_sepM_lookup with "Hdbpt") as "Hdbpt"; first apply Hlookup.
      by eauto with iFrame.
    }
    { (* Case failure. *)
      iIntros "!> Htxn".
      wp_pures.
      iApply "HΦ".
      unfold dbmap_ptstos.
      rewrite big_sepM_singleton.
      by eauto with iFrame.
    }
  }
  { (* Loop entry. *)
    subst P. simpl.
    unfold dbmap_ptstos.
    iDestruct (big_sepM_lookup _ _ (W64 0) with "Hdbpts") as "Hdbpt".
    { rewrite lookup_gset_to_gmap_Some. split; [set_solver | reflexivity]. }
    iFrame.
  }
  iIntros "HP".
  wp_pures.
  subst P. simpl.
  iDestruct "HP" as "[Htxn [%v Hdbpt]]".
  (* Allocate [mono_nat_auth_own]. *)
  iMod (mono_nat_own_alloc (uint.nat v)) as (α) "[Hmn _]".
  iApply "HΦ".
  iMod (inv_alloc mvccNApp _ (mvcc_inv_app_def γ α) with "[-]") as "#Hinv".
  { iExists _. iFrame. }
  done.
Qed.

Theorem wp_InitCounter :
  {{{ True }}}
    InitCounter #()
  {{{ γ α (db : loc), RET #db; is_db db γ ∗ mvcc_inv_app γ α }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_rec. wp_pures.

  (***********************************************************)
  (* mgr := txn.MkTxnMgr()                                   *)
  (* InitializeCounterData(mgr)                              *)
  (* return mgr                                              *)
  (***********************************************************)
  wp_apply wp_MkDB.
  iIntros (γ db) "[#Hdb Hdbpts]".
  wp_pures.
  wp_apply (wp_InitializeCounterData with "Hdb [$Hdbpts]").
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
Theorem wp_CallIncrement (db : loc) γ α :
  mvcc_inv_app γ α -∗
  is_db db γ -∗
  {{{ True }}}
    CallIncrement #db
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Hinv #Hdb" (Φ) "!> _ HΦ".
  wp_rec. wp_pures.

  (***********************************************************)
  (* txn := mgr.New()                                        *)
  (***********************************************************)
  wp_apply (wp_DB__NewTxn with "Hdb").
  iNamed "Hdb".
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
  iExists _.
  iFrame "Hdbpt".
  (* Take atomic postcondition. *)
  iIntros (ok) "H".
  iMod "Hclose" as "_".

  destruct ok eqn:E.
  { (* Case COMMIT. *)
    iDestruct "H" as (u) "[Hdbpt %Huv]".
    iMod (mono_nat_own_update (uint.nat u) with "Hmn") as "[Hmn #Hmnlb]".
    { (* Show [uint.nat v' ≤ uint.nat u']. *) word. }
    iMod ("HinvC" with "[- HΦ]") as "_".
    { (* Close the invariant. *) iExists _. iFrame. }
    iIntros "!> Htxn".
    wp_pures.
    by iApply "HΦ".
  }
  { (* Case ABORT. *)
    iMod ("HinvC" with "[- HΦ]") as "_".
    { (* Close the invariant. *) iExists _. iFrame. }
    iIntros "!> Htxn".
    wp_pures.
    by iApply "HΦ".
  }
Qed.

(**
 * The purpose of this example is to show [Decrement] *cannot* be
 * called under invariant [mvcc_inv_app].
 *)
Theorem wp_CallDecrement (db : loc) γ α :
  mvcc_inv_app γ α -∗
  is_db db γ -∗
  {{{ True }}}
    CallDecrement #db
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Hinv #Hdb" (Φ) "!> _ HΦ".
  wp_rec. wp_pures.

  (***********************************************************)
  (* txn := mgr.New()                                        *)
  (***********************************************************)
  wp_apply (wp_DB__NewTxn with "Hdb").
  iNamed "Hdb".
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
  iExists _.
  iFrame "Hdbpt".
  (* Take atomic postcondition. *)
  iIntros (ok) "H".
  iMod "Hclose" as "_".

  destruct ok eqn:E.
  { (* Case COMMIT. *)
    iDestruct "H" as (u) "[Hdbpt %Huv]".
    iMod (mono_nat_own_update (uint.nat u) with "Hmn") as "[Hmn #Hmnlb]".
    { (* Show [uint.nat v' ≤ uint.nat u']. *) Fail word.
Abort.

(**
 * The purpose of this example is to show that, under invariant
 * [mvcc_inv_app], the counter value strictly increases when the txn
 * successfully commits.
 *)
Theorem wp_CallIncrementFetch (db : loc) γ α :
  mvcc_inv_app γ α -∗
  is_db db γ -∗
  {{{ True }}}
    CallIncrementFetch #db
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Hinv #Hdb" (Φ) "!> _ HΦ".
  wp_rec. wp_pures.

  (***********************************************************)
  (* txn := mgr.New()                                        *)
  (***********************************************************)
  wp_apply (wp_DB__NewTxn with "Hdb").
  iNamed "Hdb".
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
  iExists _.
  iFrame "Hdbpt".
  (* Take atomic postcondition. *)
  iIntros (ok) "H".
  iMod "Hclose" as "_".
  (* Merge. *)
  iAssert (
      |==> mvcc_inv_app_def γ α ∗
           if ok then mono_nat_lb_own α (S (uint.nat v)) else True
    )%I with "[Hmn H]" as "> [HinvO Hmnlb]".
  { destruct ok eqn:E.
    { (* Case COMMIT. *)
      iDestruct "H" as (u) "[Hdbpt %Huv]".
      iMod (mono_nat_own_update (uint.nat u) with "Hmn") as "[Hmn #Hmnlb]".
      { (* Show [uint.nat v ≤ uint.nat u]. *) word. }
      replace (S (uint.nat v)) with (uint.nat u) by word.
      iFrame "Hmnlb". iExists _. by iFrame.
    }
    { (* Case ABORT. *)
      iModIntro. iSplit; last done.
      iExists _. iFrame.
    }
  }
  iMod ("HinvC" with "[- HΦ Hmnlb]") as "_"; first done.
  iIntros "!> Htxn".
  wp_pures.
  rename v into n1.

  (***********************************************************)
  (* if !ok1 {                                               *)
  (*     return                                              *)
  (* }                                                       *)
  (***********************************************************)
  wp_if_destruct.
  { by iApply "HΦ". }
  iDestruct "Hmnlb" as "#Hmnlb".

  (***********************************************************)
  (* n2 := Fetch(txn)                                        *)
  (***********************************************************)
  wp_apply (wp_Fetch with "Htxn").
  iInv "Hinv" as "> HinvO" "HinvC".
  iApply ncfupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iNamed "HinvO".
  (* Deduce [S (uint.nat n1) ≤ uint.nat v], which we'll need for the assertion below. *)
  iDestruct (mono_nat_lb_own_valid with "Hmn Hmnlb") as %[_ Hle].
  (* Give atomic precondition. *)
  iExists _.
  iFrame "Hdbpt".
  (* Take atomic postcondition. *)
  iIntros "Hdbpt".
  iMod "Hclose" as "_".
  iMod ("HinvC" with "[- HΦ]") as "_".
  { unfold mvcc_inv_app_def. eauto with iFrame. }
  iIntros "!> Htxn".
  wp_pures.
  rename v into n2.

  (***********************************************************)
  (* machine.Assert(n1 < n2)                                 *)
  (***********************************************************)
  wp_apply wp_Assert.
  { (* Prove [uint.Z n1 < uint.Z n2]. *) rewrite bool_decide_eq_true. word. }
  wp_pures.
  by iApply "HΦ".
Qed.

End program.
