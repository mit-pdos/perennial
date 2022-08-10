From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.go_mvcc Require Import examples.
From Perennial.program_proof.mvcc Require Import txn_proof.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

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
    <<< ∀∀ (r : dbmap), ⌜P_WriteReservedKey r⌝ ∗ dbmap_ptstos γ r >>>
      WriteReservedKey #txn @ ↑mvccNSST
    <<< ∃∃ (ok : bool), if ok then (∃ w, ⌜Q_WriteReservedKey r w⌝ ∗ dbmap_ptstos γ w) else dbmap_ptstos γ r >>>
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
    <<< ∀∀ (r : dbmap), ⌜P_WriteFreeKey r⌝ ∗ dbmap_ptstos γ r >>>
      WriteFreeKey #txn @ ↑mvccNSST
    <<< ∃∃ (ok : bool), if ok then (∃ w, ⌜Q_WriteFreeKey r w⌝ ∗ dbmap_ptstos γ w) else dbmap_ptstos γ r >>>
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

Theorem wp_WriteReservedKeyExample :
  {{{ True }}}
    WriteReservedKeyExample #()
  {{{ γ (p : loc) (ok : bool), RET (#p, #ok);
      if ok
      then frac_ptsto γ (1 / 2)%Qp (U64 0) (Value (U64 2)) ∗ p ↦[uint64T] #(U64 2)
      (* Still give the res above, but not set to the specified value (2). *)
      else ∃ (v : u64), frac_ptsto γ (1 / 2)%Qp (U64 0) (Value v) ∗ p ↦[uint64T] #v
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.

  (***********************************************************)
  (* mgr := txn.MkTxnMgr()                                   *)
  (* p := new(uint64)                                        *)
  (* mgr.InitializeData(p)                                   *)
  (* txn := mgr.New()                                        *)
  (* ok := WriteReservedKey(txn)                             *)
  (* if ok {                                                 *)
  (*     *p = 2                                              *)
  (* }                                                       *)
  (* return p, ok                                            *)
  (***********************************************************)
  wp_apply wp_MkTxnMgr.
  iIntros (γ mgr) "[Hmgr Hdbpts]".
  wp_pures.
  wp_apply wp_ref_of_zero; first done.
  iIntros (p) "HpRef".
  wp_pures.
  wp_apply (wp_txnMgr__InitializeData with "Hmgr [$Hdbpts $HpRef]").
  iIntros (u) "(#Hmgr & Hptsto' & HpRef)".
  wp_pures.
  wp_apply (wp_txnMgr__New with "Hmgr").
  iNamed "Hmgr".
  iIntros (txn) "Htxn".
  wp_pures.
  wp_apply (wp_WriteReservedKey with "Htxn").
  iInv "Hinvdb" as "> HinvdbO" "HinvdbC".
  iApply ncfupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iNamed "HinvdbO".
  iExists {[ (U64 0) := v ]}.
  iDestruct (big_sepM_delete with "Hdbpts") as "[Hdbpt Hdbpts]".
  { apply Hval. }
  iSplitL "Hdbpt".
  { unfold dbmap_ptstos. rewrite big_sepM_singleton.
    iFrame.
    iPureIntro. unfold P_WriteReservedKey.
    set_solver.
  }
  iIntros (ok) "Hdbpt".
  iMod "Hclose" as "_".
  destruct ok eqn:E.
  { (* Case COMMIT. *)
    set v' := Value (U64 2).
    iMod (frac_ptsto_update v' with "Hptsto Hptsto'") as "[Hptsto Hptsto']"; first apply Qp_half_half.
    iMod ("HinvdbC" with "[- HΦ Hptsto' HpRef]") as "_".
    { (* Close the invariant. *)
      iNext.
      iDestruct "Hdbpt" as (w) "[%HQ Hdbpt]".
      unfold Q_WriteReservedKey in HQ.
      unfold dbmap_ptstos.
      unfold mvcc_inv_db_def.
      set m' := <[(U64 0) := v']> m.
      iExists m', v'.
      iDestruct (big_sepM_lookup with "Hdbpt") as "Hdbpt".
      { apply HQ. }
      (* Q: Can we directly iDestruct the LHS of an iff? *)
      iAssert (dbmap_ptstos γ m')%I with "[Hdbpt Hdbpts]" as "Hdbpts".
      { unfold dbmap_ptstos. rewrite big_sepM_insert_delete. iFrame. }
      iFrame.
      iPureIntro.
      subst m'. rewrite lookup_insert.
      split; [done | set_solver].
    }
    iModIntro.
    iIntros "Htxn".
    wp_pures.
    wp_store.
    wp_pures.
    iApply "HΦ".
    by iFrame.
  }
  { (* Case ABORT. *)
    iMod ("HinvdbC" with "[- HΦ Hptsto' HpRef]") as "_".
    { (* Close the invariant. *)
      iNext.
      unfold dbmap_ptstos.
      rewrite big_sepM_singleton.
      unfold mvcc_inv_db_def.
      iExists m, v.
      iAssert (dbmap_ptstos γ m)%I with "[Hdbpt Hdbpts]" as "Hdbpts".
      { unfold dbmap_ptstos.
        iApply big_sepM_delete; first apply Hval.
        iFrame.
      }
      iFrame.
      iPureIntro.
      split; [done | set_solver].
    }
    iModIntro.
    iIntros "Htxn".
    wp_pures.
    iApply "HΦ".
    eauto with iFrame.
  }
Qed.

Theorem wp_WriteFreeKeyExample :
  {{{ True }}}
    WriteFreeKeyExample #()
  {{{ (ok : bool), RET #ok; True }}}.
Proof using heapGS0 mvcc_ghostG0 Σ.
  iIntros (Φ) "_ HΦ".
  wp_call.

  (***********************************************************)
  (* mgr := txn.MkTxnMgr()                                   *)
  (* p := new(uint64)                                        *)
  (* mgr.InitializeData(p)                                   *)
  (* txn := mgr.New()                                        *)
  (* ok := WriteFreeKey(txn)                                 *)
  (* return ok                                               *)
  (***********************************************************)
  wp_apply wp_MkTxnMgr.
  iIntros (γ mgr) "[Hmgr Hdbpts]".
  wp_pures.
  wp_apply wp_ref_of_zero; first done.
  iIntros (p) "HpRef".
  wp_pures.
  wp_apply (wp_txnMgr__InitializeData with "Hmgr [$Hdbpts $HpRef]").
  iIntros (u) "(#Hmgr & Hptsto' & HpRef)".
  (* Delete the [Hptsto'] to show that [WriteFreeKey] does not require that. *)
  iClear "Hptsto'".
  wp_pures.
  wp_apply (wp_txnMgr__New with "Hmgr").
  iNamed "Hmgr".
  iIntros (txn) "Htxn".
  wp_pures.
  wp_apply (wp_WriteFreeKey with "Htxn").
  iInv "Hinvdb" as "> HinvdbO" "HinvdbC".
  iApply ncfupd_mask_intro; first set_solver.
  iIntros "Hclose".
  iNamed "HinvdbO".
  assert (Hlookup : ∃ y, m !! (U64 1) = Some y).
  { apply elem_of_dom. set_solver. }
  destruct Hlookup as [y Hlookup].
  iExists {[ (U64 1) := y ]}.
  iDestruct (big_sepM_delete with "Hdbpts") as "[Hdbpt Hdbpts]".
  { apply Hlookup. }
  iSplitL "Hdbpt".
  { unfold dbmap_ptstos. rewrite big_sepM_singleton.
    iFrame.
    iPureIntro. unfold P_WriteFreeKey.
    set_solver.
  }
  iIntros (ok) "Hdbpt".
  iMod "Hclose" as "_".
  destruct ok eqn:E.
  { (* Case COMMIT. *)
    iMod ("HinvdbC" with "[- HΦ]") as "_".
    { (* Close the invariant. *)
      iNext.
      iDestruct "Hdbpt" as (w) "[%HQ Hdbpt]".
      unfold Q_WriteFreeKey in HQ.
      unfold dbmap_ptstos.
      unfold mvcc_inv_db_def.
      set v' := Value (U64 3).
      set m' := <[(U64 1) := v']> m.
      iExists m', v.
      iDestruct (big_sepM_lookup with "Hdbpt") as "Hdbpt".
      { apply HQ. }
      (* Q: Can we directly iDestruct the LHS of an iff? *)
      iAssert (dbmap_ptstos γ m')%I with "[Hdbpt Hdbpts]" as "Hdbpts".
      { unfold dbmap_ptstos. rewrite big_sepM_insert_delete. iFrame. }
      iFrame.
      iPureIntro.
      subst m'.
      split; last set_solver.
      { rewrite -Hval. by apply lookup_insert_ne. }
    }
    iModIntro.
    iIntros "Htxn".
    wp_pures.
    by iApply "HΦ".
  }
  { (* Case ABORT. *)
    iMod ("HinvdbC" with "[- HΦ]") as "_".
    { (* Close the invariant. *)
      iNext.
      unfold dbmap_ptstos.
      rewrite big_sepM_singleton.
      unfold mvcc_inv_db_def.
      iExists m, v.
      iAssert (dbmap_ptstos γ m)%I with "[Hdbpt Hdbpts]" as "Hdbpts".
      { unfold dbmap_ptstos.
        iApply big_sepM_delete; first apply Hlookup.
        iFrame.
      }
      iFrame.
      iPureIntro.
      split; [done | set_solver].
    }
    iModIntro.
    iIntros "Htxn".
    wp_pures.
    by iApply "HΦ".
  }
Qed.

End program.
