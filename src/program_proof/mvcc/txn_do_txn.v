From Perennial.program_proof.mvcc Require Import mvcc_inv txn_common txn_begin txn_abort txn_acquire txn_commit.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition spec_body (body : val) (txn :loc) tid r P Q γ τ : iProp Σ :=
  {{{ own_txn txn tid r γ τ ∗ ⌜P r⌝ ∗ txnmap_ptstos τ r }}}
    body #txn
  {{{ w (ok : bool), RET #ok;
      own_txn txn tid r γ τ ∗
      if ok then ⌜Q r w ∧ dom r = dom w⌝ ∗ txnmap_ptstos τ w else True
  }}}.

Theorem wp_txn__DoTxn txn (body : val) (P : dbmap -> Prop) (Q : dbmap -> dbmap -> Prop) γ :
  (∀ r w, (Decision (Q r w))) ->
  ⊢ {{{ own_txn_uninit txn γ ∗ (∀ tid r τ, spec_body body txn tid r P Q γ τ) }}}
    <<< ∀∀ (r : dbmap), ⌜P r⌝ ∗ dbmap_ptstos γ r >>>
      Txn__DoTxn #txn body @ ↑mvccNSST
    <<< ∃∃ (ok : bool), if ok then (∃ w, ⌜Q r w⌝ ∗ dbmap_ptstos γ w) else dbmap_ptstos γ r >>>
    {{{ RET #ok; own_txn_uninit txn γ }}}.
Proof.
  iIntros (Hdec) "!>".
  iIntros (Φ) "[Htxn #Hbody] HAU".
  wp_call.

  (***********************************************************)
  (* txn.Begin()                                             *)
  (* cmt := body(txn)                                        *)
  (* if !cmt {                                               *)
  (*     txn.Abort()                                         *)
  (*     return false                                        *)
  (* }                                                       *)
  (*                                                         *)
  (* ok := txn.acquire()                                     *)
  (* if !ok {                                                *)
  (*     txn.Abort()                                         *)
  (*     return false                                        *)
  (* }                                                       *)
  (*                                                         *)
  (* txn.Commit()                                            *)
  (* return true                                             *)
  (***********************************************************)
  iAssert (∃ p, mvcc_inv_sst γ p)%I with "[Htxn]" as (p) "#Hinv".
  { iNamed "Htxn". eauto with iFrame. }
  wp_apply (wp_txn__Begin with "Htxn").
  iInv "Hinv" as "> HinvO" "HinvC".
  replace (⊤ ∖ ∅) with (⊤ : coPset) by set_solver.
  iMod "HAU" as (r) "[[%HP Hdbps] HAUC]".
  iModIntro.
  iNamed "HinvO".
  iExists ts.
  iFrame "Hts".
  iIntros "(%n & Hts & %Hn)".
  (* Obtain [ltuple_ptsto] over [m]. *)
  iMod (per_key_inv_ltuple_ptstos with "Hkeys") as "[Hkeys Hltuples]".
  iDestruct (dbmap_lookup_big with "Hm Hdbps") as "%Hrm". 
  (* Obtain [ltuple_ptsto] over [r]. *)
  iDestruct (big_sepM_subseteq _ _ r with "Hltuples") as "Hltuples"; first auto.
  (* Obtain [txnmap_auth] and [txnmap_ptsto]. *)
  iMod (txnmap_alloc r) as (τ) "[Htxnmap Htxnps]".
  iDestruct (fc_inv_fc_tids_lt_ts with "Hfci Hfcc Hcmt") as "%Hfctids".
  (* Do case distinction on the form of [future]. *)
  pose proof (spec_peek future ts).
  destruct (peek future ts).
  { (* Case NCA. *)
    iMod ("HAUC" $! false with "Hdbps") as "HΦ".
    (* Add [ts] to [tids_nca] and get a piece of evidence. *)
    iNamed "Hnca".
    iMod (nca_tids_insert ts with "HncaAuth") as "[HncaAuth HncaFrag]".
    { (* Prove [ts ∉ tids_nca]. *)
      intros contra. apply HncaLt in contra. lia.
    }
    iAssert (nca_inv_def _ _ _ _)%I with "[HncaAuth]" as "Hnca".
    { unfold nca_inv_def. iFrame. iPureIntro.
      split.
      - (* Prove NCA holds on the new set. *)
        apply set_Forall_union; last eauto.
        by rewrite set_Forall_singleton.
      - (* Prove new TS > every elem of the new set. *)
        apply set_Forall_union.
        { rewrite set_Forall_singleton.
          assert (Hts : (ts < ts + n)%nat) by lia.
          apply Hts.
        }
        apply (set_Forall_impl _ _ _ HncaLt). lia.
    }
    iMod ("HinvC" with "[- HΦ Hltuples Htxnmap Htxnps HncaFrag]") as "_".
    { (* Close the invariant. *)
      iNext.
      iDestruct (big_sepS_mono with "Hkeys") as "Hkeys".
      { iIntros (k) "%Helem Hkeys".
        iApply (per_key_inv_weaken_ts (ts + n)%nat with "Hkeys"). lia.
      }
      iDestruct (fa_inv_weaken_ts (ts + n)%nat with "Hfa") as "Hfa"; first lia.
      iDestruct (fci_inv_weaken_ts (ts + n)%nat with "Hfci") as "Hfci"; first lia.
      iDestruct (fcc_inv_weaken_ts (ts + n)%nat with "Hfcc") as "Hfcc"; first lia.
      iDestruct (cmt_inv_weaken_ts (ts + n)%nat with "Hcmt") as "Hcmt"; first lia.
      eauto 15 with iFrame.
    }
    iIntros "!>" (tid) "[Htxn _]".
    iAssert (own_txn txn ts r γ τ)%I with "[Hltuples Htxnmap Htxn]" as "Htxn".
    { iExists ∅. rewrite map_empty_union. by iFrame. }
    wp_pures.
    (* Give [own_txn ∗ txnmap_ptstos] to the txn body, and get the updated [txnmap_ptstos] back. *)
    wp_apply ("Hbody" with "[$Htxn $Htxnps]"); first auto.
    iIntros (w ok) "[Htxn Hpost]".
    wp_pures.
    wp_if_destruct.
    { (* Application-abort branch. *)
      wp_apply (wp_txn__Abort_false with "[$Htxn HncaFrag]"); first eauto.
      by iIntros "contra".
    }
    wp_apply (wp_txn__acquire with "Htxn").
    iIntros (ok) "Htxn".
    wp_pures.
    wp_if_destruct.
    { (* System-abort branch. *)
      wp_apply (wp_txn__Abort_false with "[$Htxn HncaFrag]"); first eauto.
      by iIntros "contra".
    }
    (* Commit branch. *)
    wp_apply (wp_txn__Commit_false with "[$Htxn HncaFrag]"); first eauto.
    by iIntros (ok) "contra".
  }
  { (* Case FA. *)
    iMod ("HAUC" $! false with "Hdbps") as "HΦ".
    (* Add [s] to [tids_fa] and get a piece of evidence. *)
    iNamed "Hfa".
    iMod (fa_tids_insert ts with "HfaAuth") as "[HfaAuth HfaFrag]".
    { (* Prove [ts ∉ tids_fa]. *)
      intros contra. apply HfaLt in contra. lia.
    }
    iAssert (fa_inv_def _ _ _ _)%I with "[HfaAuth]" as "Hfa".
    { unfold fa_inv_def. iFrame. iPureIntro.
      split.
      - (* Prove FA holds on the new set. *)
        apply set_Forall_union; last eauto.
        by rewrite set_Forall_singleton.
      - (* Prove new TS > every elem of the new set. *)
        apply set_Forall_union.
        { rewrite set_Forall_singleton.
          assert (Hts : (ts < ts + n)%nat) by lia.
          apply Hts.
        }
        apply (set_Forall_impl _ _ _ HfaLt). lia.
    }
    iMod ("HinvC" with "[- HΦ Hltuples Htxnmap Htxnps HfaFrag]") as "_".
    { (* Close the invariant. *)
      iNext.
      iDestruct (big_sepS_mono with "Hkeys") as "Hkeys".
      { iIntros (k) "%Helem Hkeys".
        iApply (per_key_inv_weaken_ts (ts + n)%nat with "Hkeys"). lia.
      }
      iDestruct (nca_inv_weaken_ts (ts + n)%nat with "Hnca") as "Hnca"; first lia.
      iDestruct (fci_inv_weaken_ts (ts + n)%nat with "Hfci") as "Hfci"; first lia.
      iDestruct (fcc_inv_weaken_ts (ts + n)%nat with "Hfcc") as "Hfcc"; first lia.
      iDestruct (cmt_inv_weaken_ts (ts + n)%nat with "Hcmt") as "Hcmt"; first lia.
      eauto 15 with iFrame.
    }
    iIntros "!>" (tid) "[Htxn _]".
    iAssert (own_txn txn ts r γ τ)%I with "[Hltuples Htxnmap Htxn]" as "Htxn".
    { iExists ∅. rewrite map_empty_union. by iFrame. }
    wp_pures.
    (* Give [own_txn ∗ txnmap_ptstos] to the txn body, and get the updated [txnmap_ptstos] back. *)
    wp_apply ("Hbody" with "[$Htxn $Htxnps]"); first auto.
    iIntros (w ok) "[Htxn Hpost]".
    wp_pures.
    wp_if_destruct.
    { (* Application-abort branch. *)
      wp_apply (wp_txn__Abort with "[$Htxn $HfaFrag]").
      iIntros "Htxn".
      wp_pures.
      (* We'll return something meaningful once [res] is added. *)
      by iApply "HΦ".
    }
    wp_apply (wp_txn__acquire with "Htxn").
    iIntros (ok) "Htxn".
    wp_pures.
    wp_if_destruct.
    { (* System-abort branch. *)
      wp_apply (wp_txn__Abort with "[$Htxn $HfaFrag]").
      iIntros "Htxn".
      wp_pures.
      (* We'll return something meaningful once [res] is added. *)
      by iApply "HΦ".
    }
    (* Commit branch. *)
    wp_apply (wp_txn__Commit_false with "[$Htxn HfaFrag]"); first eauto.
    by iIntros (ok) "contra".
  }
  { (* Case FCI. *)
    iMod ("HAUC" $! false with "Hdbps") as "HΦ".
    (* Add [(ts, mods)] to [tmods_fci] and get a piece of evidence. *)
    iNamed "Hfci".
    iMod (fci_tmods_insert (ts, mods) with "HfciAuth") as "[HfciAuth HfciFrag]".
    { (* Prove [ts ∉ tmods_fci]. *)
      intros contra. apply HfciLt in contra. simpl in contra. lia.
    }
    apply (fc_tids_unique_insert_fci ts mods) in Hfcnd; last done.
    iAssert (fci_inv_def _ _ _ _ _)%I with "[HfciAuth]" as "Hfci".
    { unfold fci_inv_def. iFrame. iPureIntro.
      split.
      - (* Prove FCI holds on the new set. *)
        apply set_Forall_union; last eauto.
        rewrite set_Forall_singleton.
        by apply first_commit_incompatible_suffix.
      - (* Prove new TS > every elem of the new set. *)
        apply set_Forall_union.
        { rewrite set_Forall_singleton.
          assert (Hts : (ts < ts + n)%nat) by lia.
          apply Hts.
        }
        apply (set_Forall_impl _ _ _ HfciLt). lia.
    }
    iMod ("HinvC" with "[- HΦ Hltuples Htxnmap Htxnps HfciFrag]") as "_".
    { (* Close the invariant. *)
      iNext.
      iDestruct (big_sepS_mono with "Hkeys") as "Hkeys".
      { iIntros (k) "%Helem Hkeys".
        iApply (per_key_inv_weaken_ts (ts + n)%nat with "Hkeys"). lia.
      }
      iDestruct (nca_inv_weaken_ts (ts + n)%nat with "Hnca") as "Hnca"; first lia.
      iDestruct (fa_inv_weaken_ts (ts + n)%nat with "Hfa") as "Hfa"; first lia.
      iDestruct (fcc_inv_weaken_ts (ts + n)%nat with "Hfcc") as "Hfcc"; first lia.
      iDestruct (cmt_inv_weaken_ts (ts + n)%nat with "Hcmt") as "Hcmt"; first lia.
      eauto 15 with iFrame.
    }
    iIntros "!>" (tid) "[Htxn _]".
    iAssert (own_txn txn ts r γ τ)%I with "[Hltuples Htxnmap Htxn]" as "Htxn".
    { iExists ∅. rewrite map_empty_union. by iFrame. }
    wp_pures.
    (* Give [own_txn ∗ txnmap_ptstos] to the txn body, and get the updated [txnmap_ptstos] back. *)
    wp_apply ("Hbody" with "[$Htxn $Htxnps]"); first auto.
    iIntros (w ok) "[Htxn Hpost]".
    wp_pures.
    wp_if_destruct.
    { (* Application-abort branch. *)
      wp_apply (wp_txn__Abort_false with "[$Htxn HfciFrag]"); first eauto 10.
      by iIntros "contra".
    }
    wp_apply (wp_txn__acquire with "Htxn").
    iIntros (ok) "Htxn".
    wp_pures.
    wp_if_destruct.
    { (* System-abort branch. *)
      wp_apply (wp_txn__Abort_false with "[$Htxn HfciFrag]"); first eauto 10.
      by iIntros "contra".
    }
    (* Commit branch. *)
    wp_apply (wp_txn__Commit_false with "[$Htxn HfciFrag]"); first eauto 10.
    by iIntros (ok) "contra".
  }
  (* We also need the subseteq relation to know which keys we're extending in CMT. *)
  destruct (decide (Q r (mods ∪ r) ∧ dom mods ⊆ dom r)); last first.
  { (* Case FCC, [Q r w] not holds. *)
    iMod ("HAUC" $! false with "Hdbps") as "HΦ".
    (* Add [(ts, mods)] to [tmods_fcc] and get a piece of evidence. *)
    iNamed "Hfcc".
    iMod (fcc_tmods_insert (ts, mods) with "HfccAuth") as "[HfccAuth HfccFrag]".
    { (* Prove [ts ∉ tmods_fcc]. *)
      intros contra. apply HfccLt in contra. simpl in contra. lia.
    }
    apply (fc_tids_unique_insert_fcc ts mods) in Hfcnd; last done.
    iAssert (fcc_inv_def _ _ _ _)%I with "[HfccAuth]" as "Hfcc".
    { unfold fcc_inv_def. iFrame. iPureIntro.
      split.
      - (* Prove FCC holds on the new set. *)
        apply set_Forall_union; last eauto.
        by rewrite set_Forall_singleton.
      - (* Prove new TS > every elem of the new set. *)
        apply set_Forall_union.
        { rewrite set_Forall_singleton.
          assert (Hts : (ts < ts + n)%nat) by lia.
          apply Hts.
        }
        apply (set_Forall_impl _ _ _ HfccLt). lia.
    }
    iMod ("HinvC" with "[- HΦ Hltuples Htxnmap Htxnps HfccFrag]") as "_".
    { (* Close the invariant. *)
      iNext.
      iDestruct (big_sepS_mono with "Hkeys") as "Hkeys".
      { iIntros (k) "%Helem Hkeys".
        iApply (per_key_inv_weaken_ts (ts + n)%nat with "Hkeys"). lia.
      }
      iDestruct (nca_inv_weaken_ts (ts + n)%nat with "Hnca") as "Hnca"; first lia.
      iDestruct (fa_inv_weaken_ts (ts + n)%nat with "Hfa") as "Hfa"; first lia.
      iDestruct (fci_inv_weaken_ts (ts + n)%nat with "Hfci") as "Hfci"; first lia.
      iDestruct (cmt_inv_weaken_ts (ts + n)%nat with "Hcmt") as "Hcmt"; first lia.
      eauto 15 with iFrame.
    }
    iIntros "!>" (tid) "[Htxn _]".
    iAssert (own_txn txn ts r γ τ)%I with "[Hltuples Htxnmap Htxn]" as "Htxn".
    { iExists ∅. rewrite map_empty_union. by iFrame. }
    wp_pures.
    (* Give [own_txn ∗ txnmap_ptstos] to the txn body, and get the updated [txnmap_ptstos] back. *)
    wp_apply ("Hbody" with "[$Htxn $Htxnps]"); first auto.
    iIntros (w ok) "[Htxn Hpost]".
    wp_pures.
    wp_if_destruct.
    { (* Application-abort branch. *)
      wp_apply (wp_txn__Abort_false with "[$Htxn HfccFrag]"); first eauto 10.
      by iIntros "contra".
    }
    wp_apply (wp_txn__acquire with "Htxn").
    iIntros (ok) "Htxn".
    wp_pures.
    wp_if_destruct.
    { (* System-abort branch. *)
      wp_apply (wp_txn__Abort_false with "[$Htxn HfccFrag]"); first eauto 10.
      by iIntros "contra".
    }
    (* Commit branch. *)
    iDestruct "Hpost" as "[[%HQ %Hdom] Htxnps]".
    wp_apply (wp_txn__Commit_false with "[$Htxn HfccFrag Htxnps]").
    { unfold commit_false_cases. do 3 iRight.
      iExists mods, w, Q.
      by iFrame.
    }
    by iIntros (ok) "contra".
  }
  { (* Case CMT, i.e. FCC and [Q r w] holds. *)
    (* Update [dbmap_ptstos γ r] to [dbmap_ptstos γ (mods ∪ r)]. *)
    destruct a as [HQ Hdom].
    iMod (per_key_inv_dbmap_ptstos_update (ts + n)%nat r mods with "Hm Hdbps Hkeys") as "(Hm & Hdbps & Hkeys)".
    { done. } { lia. }
    iMod ("HAUC" $! true with "[Hdbps]") as "HΦ".
    { iExists _. by iFrame. }
    (* Add [(ts, mods)] to [tmods] and get a piece of evidence. *)
    iNamed "Hcmt".
    iMod (cmt_tmods_insert (ts, mods) with "HcmtAuth") as "[HcmtAuth HcmtFrag]".
    { (* Prove [ts ∉ tmods_cmt]. *)
      intros contra. apply HcmtLt in contra. simpl in contra. lia.
    }
    apply (fc_tids_unique_insert_cmt ts mods) in Hfcnd; last done.
    iAssert (cmt_inv_def _ _ _ _)%I with "[HcmtAuth]" as "Hcmt".
    { unfold cmt_inv_def. iFrame. iPureIntro.
      split.
      - (* Prove CMT holds on the new set. *)
        apply set_Forall_union; last eauto.
        by rewrite set_Forall_singleton.
      - (* Prove new TS > every elem of the new set. *)
        apply set_Forall_union.
        { rewrite set_Forall_singleton.
          assert (Hts : (ts < ts + n)%nat) by lia.
          apply Hts.
        }
        apply (set_Forall_impl _ _ _ HcmtLt). lia.
    }
    iMod ("HinvC" with "[- HΦ Hltuples Htxnmap Htxnps HcmtFrag]") as "_".
    { (* Close the invariant. *)
      iNext.
      iDestruct (big_sepS_mono with "Hkeys") as "Hkeys".
      { iIntros (k) "%Helem Hkeys".
        iApply (per_key_inv_weaken_ts (ts + n)%nat with "Hkeys"). lia.
      }
      iDestruct (nca_inv_weaken_ts (ts + n)%nat with "Hnca") as "Hnca"; first lia.
      iDestruct (fa_inv_weaken_ts (ts + n)%nat with "Hfa") as "Hfa"; first lia.
      iDestruct (fci_inv_weaken_ts (ts + n)%nat with "Hfci") as "Hfci"; first lia.
      iDestruct (fcc_inv_weaken_ts (ts + n)%nat with "Hfcc") as "Hfcc"; first lia.
      eauto 15 with iFrame.
    }
    iIntros "!>" (tid) "[Htxn _]".
    iAssert (own_txn txn ts r γ τ)%I with "[Hltuples Htxnmap Htxn]" as "Htxn".
    { iExists ∅. rewrite map_empty_union. by iFrame. }
    wp_pures.
    (* Give [own_txn ∗ txnmap_ptstos] to the txn body, and get the updated [txnmap_ptstos] back. *)
    wp_apply ("Hbody" with "[$Htxn $Htxnps]"); first auto.
    iIntros (w ok) "[Htxn Hpost]".
    wp_pures.
    wp_if_destruct.
    { (* Application-abort branch. *)
      wp_apply (wp_txn__Abort_false with "[$Htxn HcmtFrag]"); first eauto 10.
      by iIntros "contra".
    }
    wp_apply (wp_txn__acquire with "Htxn").
    iIntros (ok) "Htxn".
    wp_pures.
    wp_if_destruct.
    { (* System-abort branch. *)
      wp_apply (wp_txn__Abort_false with "[$Htxn HcmtFrag]"); first eauto 10.
      by iIntros "contra".
    }
    (* Commit branch. *)
    wp_apply (wp_txn__Commit with "[$Htxn $HcmtFrag]").
    iIntros "Htxn".
    wp_pures.
    by iApply "HΦ".
  }
Qed.


Definition pre_Swap (r : dbmap) : Prop.
Admitted.
Definition post_Swap (r w : dbmap) : Prop.
Admitted.

Theorem wp_SwapSeq txn tid r γ τ :
  {{{ own_txn txn tid r γ τ ∗ ⌜pre_Swap r⌝ ∗ txnmap_ptstos τ r }}}
    SwapSeq #txn
  {{{ w (ok : bool), RET #ok;
      own_txn txn tid r γ τ ∗
      if ok then ⌜post_Swap r w ∧ dom r = dom w⌝ ∗ txnmap_ptstos τ w else True
  }}}.
Admitted.

Instance post_Swap_dec : (∀ r w, (Decision (post_Swap r w))).
Admitted.

Theorem wp_Swap (txn : loc) γ :
  ⊢ {{{ own_txn_uninit txn γ }}}
    <<< ∀∀ (r : dbmap), ⌜pre_Swap r⌝ ∗ dbmap_ptstos γ r >>>
      Swap #txn @ ↑mvccNSST
    <<< ∃∃ (ok : bool), if ok then (∃ w, ⌜post_Swap r w⌝ ∗ dbmap_ptstos γ w) else dbmap_ptstos γ r >>>
    {{{ RET #ok; own_txn_uninit txn γ }}}.
Proof.
  iIntros "!>".
  iIntros (Φ) "Htxn HAU".
  wp_call.
  wp_apply (wp_txn__DoTxn _ _ _ post_Swap with "[$Htxn]").
  { unfold spec_body.
    iIntros (tid r τ Φ') "!> Hpre HΦ'".
    iApply (wp_SwapSeq with "Hpre HΦ'").
  }
  done.
Qed.

End program.
