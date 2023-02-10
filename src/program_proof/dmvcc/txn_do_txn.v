From Perennial.program_proof.mvcc Require Export
     mvcc_prelude mvcc_action mvcc_ghost mvcc_inv.
From Perennial.program_proof.dmvcc Require Export txn_abort.
From Goose.github_com.mit_pdos.gokv.dmvcc Require Export txn.

Section proof.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Theorem wp_txn__begin txn γ :
  ⊢ {{{ own_txn_clerk_uninit txn γ }}}
    <<< ∀∀ (ts : nat), ts_auth γ ts >>>
      txn.Clerk__begin #txn @ ↑mvccNGC ∪ ↑mvccNTID
    <<< ∃∃ ts', ts_auth γ ts' ∗ ⌜(ts < ts')%nat⌝ >>>
    {{{ (tid : u64) (wrbuf : loc), RET #();
        own_txn_clerk_impl txn ∅ ts' γ
    }}}.
Proof.
  iIntros "!>" (Φ) "Htxn HAU".
  iNamed "Htxn".
  wp_call.

  (***********************************************************)
  (* tid := txn.txnMgr.activate(txn.sid)                     *)
  (***********************************************************)
  wp_loadField.
  (*
  wp_apply (wp_txnMgr__activate with "HtxnmgrRI"); first done.
  rename tid into tid_tmp.
  iMod "HAU" as (ts) "[Hts HAUC]".
  iModIntro.
  iExists ts.
  iFrame "Hts".
  iIntros "%n [H %Hlt]".
  iMod ("HAUC" with "[H]") as "HΦ"; first eauto with iFrame.
  iIntros "!>" (tid) "[Hactive %HtidNZ]".

  (***********************************************************)
  (* txn.tid = tid                                           *)
  (***********************************************************)
  wp_pures.
  wp_storeField.

  (***********************************************************)
  (* txn.wrbuf.Clear()                                       *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_wrbuf__Clear with "HwrbufRP").
  iIntros "HwrbufRP".
  wp_pures.

  iModIntro.
  iApply "HΦ". iFrame "HwrbufRP". iSplitL; last done.
  repeat iExists _. iFrame "∗#".
  iSplit; done. *)
Admitted.


Definition spec_body
           (body : val) (txn : loc) tid r
           (P : dbmap -> Prop) (Q : dbmap -> dbmap -> Prop)
           (Rc : dbmap -> dbmap -> iProp Σ) (Ra : dbmap -> iProp Σ)
           γ τ : iProp Σ :=
  ∀ Φ,
  own_txn_clerk txn tid r γ τ ∗ ⌜P r⌝ ∗ txnmap_ptstos τ r -∗
  (∀ ok : bool,
     (own_txn_clerk txn tid r γ τ ∗
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
  ⊢ {{{ own_txn_clerk_uninit txn γ ∗ (∀ tid r τ, spec_body body txn tid r P Q Rc Ra γ τ) }}}
    <<< ∀∀ (r : dbmap), ⌜P r⌝ ∗ dbmap_ptstos γ 1 r >>>
      txn.Clerk__DoTxn #txn body @ ↑mvccN
    <<< ∃∃ (ok : bool) (w : dbmap), if ok then ⌜Q r w⌝ ∗ dbmap_ptstos γ 1 w else dbmap_ptstos γ 1 r >>>
    {{{ RET #ok; if ok then Rc r w else Ra r }}}.
Proof.
  iIntros (Hdec) "!>".
  iIntros (Φ) "[Htxn Hbody] HAU".
  wp_call.

  iAssert (∃ p, mvcc_inv_sst γ p)%I with "[Htxn]" as (p) "#Hinv".
  { iNamed "Htxn". eauto with iFrame. }

  wp_apply (wp_txn__begin with "Htxn").
  iInv "Hinv" as "> HinvO" "HinvC".
  iMod (ncfupd_mask_subseteq (⊤ ∖ ↑mvccN)) as "Hclose"; first solve_ndisj.
  iMod "HAU" as (r) "[[%HP Hdbps] HAUC]".
  iModIntro.
  iNamed "HinvO".
  iExists ts.
  iFrame "Hts".
  (* From now on [ts] refers to the new TS, that is, TID of the transaction. *)
  rename ts into tsold.
  iIntros "%ts (Hts & %Hn)".
  (* Do case distinction on the form of [future]. *)
  pose proof (spec_peek future ts).
  destruct (peek future ts).
  { (* Case NCA. *)
    (* Obtain [ltuple_ptsto] over [m]. *)
    iMod (per_key_inv_ltuple_ptstos _ _ _ ts with "Hkeys") as "[Hkeys Hltuples]"; first done.
    iDestruct (dbmap_lookup_big with "Hm Hdbps") as "%Hrm".
    (* Obtain [ltuple_ptsto] over [r]. *)
    iDestruct (big_sepM_subseteq _ _ r with "Hltuples") as "Hltuples"; first done.
    (* Obtain [txnmap_auth] and [txnmap_ptsto]. *)
    iMod (txnmap_alloc r) as (τ) "[Htxnmap Htxnps]".
    iDestruct (fc_inv_fc_tids_lt_ts with "Hfci Hfcc Hcmt") as "%Hfctids".
    (* Choose the will-abort branch. Use [∅] as placeholder. *)
    iMod ("HAUC" $! false ∅ with "Hdbps") as "HΦ".
    (* Add [ts] to [tids_nca] and get a piece of evidence. *)
    iNamed "Hnca".
    iMod (nca_tids_insert ts with "HncaAuth") as "[HncaAuth HncaFrag]".
    { (* Prove [ts ∉ tids_nca]. *)
      intros contra. apply HncaLe in contra. lia.
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
          reflexivity.
        }
        apply (set_Forall_impl _ _ _ HncaLe). lia.
    }
    iMod "Hclose" as "_".
    iMod ("HinvC" with "[- HΦ Hltuples Htxnmap Htxnps HncaFrag Hbody]") as "_".
    { (* Close the invariant. *)
      iNext.
      iDestruct (big_sepS_mono with "Hkeys") as "Hkeys".
      { iIntros (k) "%Helem Hkeys".
        iApply (per_key_inv_weaken_ts ts with "Hkeys"). lia.
      }
      iDestruct (fa_inv_weaken_ts ts with "Hfa") as "Hfa"; first lia.
      iDestruct (fci_inv_weaken_ts ts with "Hfci") as "Hfci"; first lia.
      iDestruct (fcc_inv_weaken_ts ts with "Hfcc") as "Hfcc"; first lia.
      iDestruct (cmt_inv_weaken_ts ts with "Hcmt") as "Hcmt"; first lia.
      eauto 15 with iFrame.
    }
    iIntros "!>" (tid wrbuf) "Htxn".
    iAssert (own_txn_clerk txn ts r γ τ)%I with "[Hltuples Htxnmap Htxn]" as "Htxn".
    { iExists ∅. rewrite map_empty_union. by iFrame. }
    wp_pures.
    (* Give [own_txn ∗ txnmap_ptstos] to the txn body, and get the updated [txnmap_ptstos] back. *)
    wp_apply ("Hbody" with "[$Htxn $Htxnps]"); first done.
    iIntros (ok) "[Htxn Hpost]".
    wp_pures.
    wp_if_destruct.
    { (* Application-abort branch. *)
      wp_apply (wp_txn__abort_false with "[$Htxn HncaFrag]"); first by eauto.
      by iIntros "contra".
    }
    wp_loadField.
    wp_apply (wp_txn__acquire with "Htxn").
    iIntros (ok) "Htxn".
    wp_pures.
    wp_if_destruct.
    { (* System-abort branch. *)
      wp_apply (wp_txn__abort_false with "[$Htxn HncaFrag]"); first by eauto.
      by iIntros "contra".
    }
    (* Commit branch. *)
    wp_apply (wp_txn__commit_false with "[$Htxn HncaFrag]"); first by eauto.
    by iIntros (ok) "contra".
  }
  { (* Case FA. *)
    (* Obtain [ltuple_ptsto] over [m]. *)
    iMod (per_key_inv_ltuple_ptstos _ _ _ ts with "Hkeys") as "[Hkeys Hltuples]"; first done.
    iDestruct (dbmap_lookup_big with "Hm Hdbps") as "%Hrm".

End proof.
