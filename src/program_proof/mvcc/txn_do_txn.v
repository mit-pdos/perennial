From Perennial.program_proof.mvcc Require Import
     txn_prelude txn_repr
     txn_begin txn_abort txn_acquire txn_commit.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition spec_body
           (body : val) (txn : loc) tid r
           (P : dbmap -> Prop) (Q : dbmap -> dbmap -> Prop)
           (Rc : dbmap -> dbmap -> iProp Σ) (Ra : dbmap -> iProp Σ)
           γ τ : iProp Σ :=
  ∀ Φ,
  own_txn txn tid r γ τ ∗ ⌜P r⌝ ∗ txnmap_ptstos τ r -∗
  (∀ ok : bool,
     (own_txn txn tid r γ τ ∗
      if ok
      then ∃ w, ⌜Q r w ∧ dom r = dom w⌝ ∗ (Rc r w ∧ Ra r) ∗ txnmap_ptstos τ w
      else Ra r) -∗ Φ #ok) -∗
  WP body #txn {{ v, Φ v }}.

Theorem wp_txn__DoTxn
        txn (body : val)
        (P : dbmap -> Prop) (Q : dbmap -> dbmap -> Prop)
        (Rc : dbmap -> dbmap -> iProp Σ) (Ra : dbmap -> iProp Σ)
        γ :
  (∀ r w, (Decision (Q r w))) ->
  ⊢ {{{ own_txn_uninit txn γ ∗ (∀ tid r τ, spec_body body txn tid r P Q Rc Ra γ τ) }}}
    <<< ∀∀ (r : dbmap), ⌜P r⌝ ∗ dbmap_ptstos γ 1 r >>>
      Txn__DoTxn #txn body @ ↑mvccN
    <<< ∃∃ (ok : bool) (w : dbmap), if ok then ⌜Q r w⌝ ∗ dbmap_ptstos γ 1 w else dbmap_ptstos γ 1 r >>>
    {{{ RET #ok; own_txn_uninit txn γ ∗ if ok then Rc r w else Ra r }}}.
Proof.
  iIntros (Hdec) "!>".
  iIntros (Φ) "[Htxn Hbody] HAU".
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
  iMod (ncfupd_mask_subseteq (⊤ ∖ ↑mvccN)) as "Hclose"; first solve_ndisj.
  iMod "HAU" as (r) "[[%HP Hdbps] HAUC]".
  iModIntro.
  iNamed "HinvO".
  iExists ts.
  iFrame "Hts".
  iIntros "(%ts' & Hts & %Hn)".
  (* Obtain [ltuple_ptsto] over [m]. *)
  iMod (per_key_inv_ltuple_ptstos with "Hkeys") as "[Hkeys Hltuples]".
  iDestruct (dbmap_lookup_big with "Hm Hdbps") as "%Hrm". 
  (* Obtain [ltuple_ptsto] over [r]. *)
  iDestruct (big_sepM_subseteq _ _ r with "Hltuples") as "Hltuples"; first done.
  (* Obtain [txnmap_auth] and [txnmap_ptsto]. *)
  iMod (txnmap_alloc r) as (τ) "[Htxnmap Htxnps]".
  iDestruct (fc_inv_fc_tids_lt_ts with "Hfci Hfcc Hcmt") as "%Hfctids".
  (* Do case distinction on the form of [future]. *)
  pose proof (spec_peek future ts).
  destruct (peek future ts).
  { (* Case NCA. *)
    (* Choose the will-abort branch. Use [∅] as placeholder. *)
    iMod ("HAUC" $! false ∅ with "Hdbps") as "HΦ".
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
          assert (Hts : (ts < ts')%nat) by lia.
          apply Hts.
        }
        apply (set_Forall_impl _ _ _ HncaLt). lia.
    }
    iMod "Hclose" as "_".
    iMod ("HinvC" with "[- HΦ Hltuples Htxnmap Htxnps HncaFrag Hbody]") as "_".
    { (* Close the invariant. *)
      iNext.
      iDestruct (big_sepS_mono with "Hkeys") as "Hkeys".
      { iIntros (k) "%Helem Hkeys".
        iApply (per_key_inv_weaken_ts ts' with "Hkeys"). lia.
      }
      iDestruct (fa_inv_weaken_ts ts' with "Hfa") as "Hfa"; first lia.
      iDestruct (fci_inv_weaken_ts ts' with "Hfci") as "Hfci"; first lia.
      iDestruct (fcc_inv_weaken_ts ts' with "Hfcc") as "Hfcc"; first lia.
      iDestruct (cmt_inv_weaken_ts ts' with "Hcmt") as "Hcmt"; first lia.
      eauto 15 with iFrame.
    }
    iIntros "!>" (tid wrbuf) "(Htxn & Hwrbuf & _)".
    iAssert (own_txn txn ts r γ τ)%I with "[Hltuples Htxnmap Htxn Hwrbuf]" as "Htxn".
    { iExists _, ∅. rewrite map_empty_union. by iFrame. }
    wp_pures.
    (* Give [own_txn ∗ txnmap_ptstos] to the txn body, and get the updated [txnmap_ptstos] back. *)
    wp_apply ("Hbody" with "[$Htxn $Htxnps]"); first done.
    iIntros (ok) "[Htxn Hpost]".
    wp_pures.
    wp_if_destruct.
    { (* Application-abort branch. *)
      wp_apply (wp_txn__Abort_false with "[$Htxn HncaFrag]"); first by eauto.
      by iIntros "contra".
    }
    wp_apply (wp_txn__acquire with "Htxn").
    iIntros (ok) "Htxn".
    wp_pures.
    wp_if_destruct.
    { (* System-abort branch. *)
      wp_apply (wp_txn__Abort_false with "[$Htxn HncaFrag]"); first by eauto.
      by iIntros "contra".
    }
    (* Commit branch. *)
    wp_apply (wp_txn__Commit_false with "[$Htxn HncaFrag]"); first by eauto.
    by iIntros (ok) "contra".
  }
  { (* Case FA. *)
    (* Choose the will-abort branch. Use [∅] as placeholder. *)
    iMod ("HAUC" $! false ∅ with "Hdbps") as "HΦ".
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
          assert (Hts : (ts < ts')%nat) by lia.
          apply Hts.
        }
        apply (set_Forall_impl _ _ _ HfaLt). lia.
    }
    iMod "Hclose" as "_".
    iMod ("HinvC" with "[- HΦ Hltuples Htxnmap Htxnps HfaFrag Hbody]") as "_".
    { (* Close the invariant. *)
      iNext.
      iDestruct (big_sepS_mono with "Hkeys") as "Hkeys".
      { iIntros (k) "%Helem Hkeys".
        iApply (per_key_inv_weaken_ts ts' with "Hkeys"). lia.
      }
      iDestruct (nca_inv_weaken_ts ts' with "Hnca") as "Hnca"; first lia.
      iDestruct (fci_inv_weaken_ts ts' with "Hfci") as "Hfci"; first lia.
      iDestruct (fcc_inv_weaken_ts ts' with "Hfcc") as "Hfcc"; first lia.
      iDestruct (cmt_inv_weaken_ts ts' with "Hcmt") as "Hcmt"; first lia.
      eauto 15 with iFrame.
    }
    iIntros "!>" (tid wrbuf) "(Htxn & Hwrbuf & _)".
    iAssert (own_txn txn ts r γ τ)%I with "[Hltuples Htxnmap Htxn Hwrbuf]" as "Htxn".
    { iExists _, ∅. rewrite map_empty_union. by iFrame. }
    wp_pures.
    (* Give [own_txn ∗ txnmap_ptstos] to the txn body, and get the updated [txnmap_ptstos] back. *)
    wp_apply ("Hbody" with "[$Htxn $Htxnps]"); first done.
    iIntros (ok) "[Htxn Hpost]".
    wp_pures.
    wp_if_destruct.
    { (* Application-abort branch. *)
      wp_apply (wp_txn__Abort with "[$Htxn $HfaFrag]").
      iIntros "Htxn".
      wp_pures.
      (* We'll return something meaningful once [res] is added. *)
      iApply "HΦ".
      by iFrame.
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
      iApply "HΦ".
      (* Txn body gives both [Rc] and [Ra], and we choose the latter here. *)
      iDestruct "Hpost" as (w) "(_ & [_ Ra] & _)".
      by iFrame.
    }
    (* Commit branch. *)
    wp_apply (wp_txn__Commit_false with "[$Htxn HfaFrag]"); first by eauto.
    by iIntros (ok) "contra".
  }
  { (* Case FCI. *)
    (* Choose the will-abort branch. Use [∅] as placeholder. *)
    iMod ("HAUC" $! false ∅ with "Hdbps") as "HΦ".
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
          assert (Hts : (ts < ts')%nat) by lia.
          apply Hts.
        }
        apply (set_Forall_impl _ _ _ HfciLt). lia.
    }
    iMod "Hclose" as "_".
    iMod ("HinvC" with "[- HΦ Hltuples Htxnmap Htxnps HfciFrag Hbody]") as "_".
    { (* Close the invariant. *)
      iNext.
      iDestruct (big_sepS_mono with "Hkeys") as "Hkeys".
      { iIntros (k) "%Helem Hkeys".
        iApply (per_key_inv_weaken_ts ts' with "Hkeys"). lia.
      }
      iDestruct (nca_inv_weaken_ts ts' with "Hnca") as "Hnca"; first lia.
      iDestruct (fa_inv_weaken_ts ts' with "Hfa") as "Hfa"; first lia.
      iDestruct (fcc_inv_weaken_ts ts' with "Hfcc") as "Hfcc"; first lia.
      iDestruct (cmt_inv_weaken_ts ts' with "Hcmt") as "Hcmt"; first lia.
      eauto 15 with iFrame.
    }
    iIntros "!>" (tid wrbuf) "(Htxn & Hwrbuf & _)".
    iAssert (own_txn txn ts r γ τ)%I with "[Hltuples Htxnmap Htxn Hwrbuf]" as "Htxn".
    { iExists _, ∅. rewrite map_empty_union. by iFrame. }
    wp_pures.
    (* Give [own_txn ∗ txnmap_ptstos] to the txn body, and get the updated [txnmap_ptstos] back. *)
    wp_apply ("Hbody" with "[$Htxn $Htxnps]"); first done.
    iIntros (ok) "[Htxn Hpost]".
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
    wp_apply (wp_txn__Commit_false with "[$Htxn HfciFrag]"); first by eauto 10.
    by iIntros (ok) "contra".
  }
  (* We also need the subseteq relation to know which keys we're extending in CMT. *)
  destruct (decide (Q r (mods ∪ r) ∧ dom mods ⊆ dom r)); last first.
  { (* Case FCC, [Q r w] not holds. *)
    iMod ("HAUC" $! false ∅ with "Hdbps") as "HΦ".
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
          assert (Hts : (ts < ts')%nat) by lia.
          apply Hts.
        }
        apply (set_Forall_impl _ _ _ HfccLt). lia.
    }
    iMod "Hclose" as "_".
    iMod ("HinvC" with "[- HΦ Hltuples Htxnmap Htxnps HfccFrag Hbody]") as "_".
    { (* Close the invariant. *)
      iNext.
      iDestruct (big_sepS_mono with "Hkeys") as "Hkeys".
      { iIntros (k) "%Helem Hkeys".
        iApply (per_key_inv_weaken_ts ts' with "Hkeys"). lia.
      }
      iDestruct (nca_inv_weaken_ts ts' with "Hnca") as "Hnca"; first lia.
      iDestruct (fa_inv_weaken_ts ts' with "Hfa") as "Hfa"; first lia.
      iDestruct (fci_inv_weaken_ts ts' with "Hfci") as "Hfci"; first lia.
      iDestruct (cmt_inv_weaken_ts ts' with "Hcmt") as "Hcmt"; first lia.
      eauto 15 with iFrame.
    }
    iIntros "!>" (tid wrbuf) "(Htxn & Hwrbuf & _)".
    iAssert (own_txn txn ts r γ τ)%I with "[Hltuples Htxnmap Htxn Hwrbuf]" as "Htxn".
    { iExists _, ∅. rewrite map_empty_union. by iFrame. }
    wp_pures.
    (* Give [own_txn ∗ txnmap_ptstos] to the txn body, and get the updated [txnmap_ptstos] back. *)
    wp_apply ("Hbody" with "[$Htxn $Htxnps]"); first done.
    iIntros (ok) "[Htxn Hpost]".
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
    iDestruct "Hpost" as (w) "([%HQ %Hdom] & HR & Htxnps)".
    wp_apply (wp_txn__Commit_false with "[$Htxn HfccFrag Htxnps]").
    { unfold commit_false_cases. do 3 iRight.
      iExists mods, w, Q.
      by iFrame.
    }
    by iIntros (ok) "contra".
  }
  { (* Case CMT, i.e. FCC and [Q r w] holds. *)
    (* Update [dbmap_ptstos γ 1 r] to [dbmap_ptstos γ 1 (mods ∪ r)]. *)
    destruct a as [HQ Hdom].
    iMod (per_key_inv_dbmap_ptstos_update ts' r mods with "Hm Hdbps Hkeys") as "(Hm & Hdbps & Hkeys)".
    { done. } { lia. }
    iMod ("HAUC" $! true (mods ∪ r) with "[Hdbps]") as "HΦ"; first by iFrame.
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
          assert (Hts : (ts < ts')%nat) by lia.
          apply Hts.
        }
        apply (set_Forall_impl _ _ _ HcmtLt). lia.
    }
    iMod "Hclose" as "_".
    iMod ("HinvC" with "[- HΦ Hltuples Htxnmap Htxnps HcmtFrag Hbody]") as "_".
    { (* Close the invariant. *)
      iNext.
      iDestruct (big_sepS_mono with "Hkeys") as "Hkeys".
      { iIntros (k) "%Helem Hkeys".
        iApply (per_key_inv_weaken_ts ts' with "Hkeys"). lia.
      }
      iDestruct (nca_inv_weaken_ts ts' with "Hnca") as "Hnca"; first lia.
      iDestruct (fa_inv_weaken_ts ts' with "Hfa") as "Hfa"; first lia.
      iDestruct (fci_inv_weaken_ts ts' with "Hfci") as "Hfci"; first lia.
      iDestruct (fcc_inv_weaken_ts ts' with "Hfcc") as "Hfcc"; first lia.
      eauto 15 with iFrame.
    }
    iIntros "!>" (tid wrbuf) "(Htxn & Hwrbuf & _)".
    iAssert (own_txn txn ts r γ τ)%I with "[Hltuples Htxnmap Htxn Hwrbuf]" as "Htxn".
    { iExists _, ∅. rewrite map_empty_union. by iFrame. }
    wp_pures.
    (* Give [own_txn ∗ txnmap_ptstos] to the txn body, and get the updated [txnmap_ptstos] back. *)
    wp_apply ("Hbody" with "[$Htxn $Htxnps]"); first auto.
    iIntros (ok) "[Htxn Hpost]".
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
    (* Txn body gives both [Rc] and [Ra], and we choose the latter here. *)
    iDestruct "Hpost" as (w) "([_ %Hdom'] & [HRc _] & Htxnps)".
    wp_apply (wp_txn__Commit with "[$Htxn $HcmtFrag $Htxnps]"); first done.
    iIntros "[Htxn <-]".
    wp_pures.
    iApply "HΦ".
    by iFrame.
  }
Qed.

Definition spec_body_xres
           (body : val) (txn : loc) tid r
           (P : dbmap -> Prop) (Q : dbmap -> dbmap -> Prop)
           γ τ : iProp Σ :=
  ∀ Φ,
  own_txn txn tid r γ τ ∗ ⌜P r⌝ ∗ txnmap_ptstos τ r -∗
  (∀ ok : bool,
     (own_txn txn tid r γ τ ∗
      if ok then ∃ w, ⌜Q r w ∧ dom r = dom w⌝ ∗ txnmap_ptstos τ w else True) -∗ Φ #ok) -∗
  WP body #txn {{ v, Φ v }}.

Theorem wp_txn__DoTxn_xres
        txn (body : val)
        (P : dbmap -> Prop) (Q : dbmap -> dbmap -> Prop)
        γ :
  (∀ r w, (Decision (Q r w))) ->
  ⊢ {{{ own_txn_uninit txn γ ∗ (∀ tid r τ, spec_body_xres body txn tid r P Q γ τ) }}}
    <<< ∀∀ (r : dbmap), ⌜P r⌝ ∗ dbmap_ptstos γ 1 r >>>
      Txn__DoTxn #txn body @ ↑mvccN
    <<< ∃∃ (ok : bool) (w : dbmap), if ok then ⌜Q r w⌝ ∗ dbmap_ptstos γ 1 w else dbmap_ptstos γ 1 r >>>
    {{{ RET #ok; own_txn_uninit txn γ }}}.
Proof.
  iIntros (Hdec) "!>".
  iIntros (Φ) "[Htxn Hbody] HAU".
  set Rc : dbmap -> dbmap -> iProp Σ := (λ (r w : dbmap), True)%I.
  set Ra : dbmap -> iProp Σ := (λ (r : dbmap), True)%I.
  wp_apply (wp_txn__DoTxn _ _ P Q Rc Ra with "[$Htxn Hbody]").
  { clear Φ.
    iIntros (tid r τ Φ) "(Htxn & %HP & Htxnps) HΦ".
    wp_apply ("Hbody" with "[$Htxn $Htxnps]"); first done.
    iIntros (ok) "[Htxn Hpost]".
    iApply "HΦ".
    iFrame.
    destruct ok; last done.
    iDestruct "Hpost" as (w) "[%Hdom Htxnps]".
    eauto 20 with iFrame.
  }
  iMod "HAU".
  iModIntro.
  iDestruct "HAU" as (r) "[[%HP Hdbps] HAU]".
  iExists r.
  iFrame.
  iSplit; first done.
  iIntros (ok w) "Hpost".
  iMod ("HAU" with "Hpost") as "HΦ".
  iIntros "!> [Htxn H]".
  iApply "HΦ".
  iFrame.
Qed.
  
End program.
