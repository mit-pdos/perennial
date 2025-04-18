From Perennial.program_proof.tulip.invariance Require Import linearize preprepare.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.txn Require Import
  res txn_repr txn_begin txn_attach txn_cancel txn_prepare
  txn_reset txn_abort txn_commit.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Definition body_spec
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

  Theorem wp_Txn__Run
    txn (body : val)
    (P : dbmap -> Prop) (Q : dbmap -> dbmap -> Prop)
    (Rc : dbmap -> dbmap -> iProp Σ) (Ra : dbmap -> iProp Σ) γ :
    (∀ r w, (Decision (Q r w))) ->
    ⊢ {{{ own_txn_uninit txn γ ∗ (∀ tid r τ, body_spec body txn tid r P Q Rc Ra γ τ) }}}
      <<< ∀∀ (r : dbmap), ⌜P r ∧ dom r ⊆ keys_all⌝ ∗ own_db_ptstos γ r >>>
        Txn__Run #txn body @ ↑sysNS
      <<< ∃∃ (ok : bool) (w : dbmap), if ok then ⌜Q r w⌝ ∗ own_db_ptstos γ w else own_db_ptstos γ r >>>
      {{{ RET #ok; own_txn_uninit txn γ ∗ if ok then Rc r w else Ra r }}}.
  Proof.
    iIntros (Hdec) "!>".
    iIntros (Φ) "[Htxn Hbody] HAU".
    wp_rec. wp_pures.

    (*@ func (txn *Txn) Run(body func(txn *Txn) bool) bool {                    @*)
    (*@     txn.begin()                                                         @*)
    (*@                                                                         @*)
    iAssert (∃ p, know_tulip_inv_with_proph γ p)%I as (p) "#Hinv".
    { do 2 iNamed "Htxn". iFrame "Hinv". }
    wp_apply (wp_Txn__begin with "[-Hbody HAU]").
    { iFrame "∗ # %". }
    iInv "Hinv" as "> HinvO" "HinvC".
    iMod (ncfupd_mask_subseteq (⊤ ∖ ↑sysNS)) as "Hclose"; first solve_ndisj.
    iMod "HAU" as (rds) "[[[%HP %Hdomr] Hdbpts] HAUC]".
    iModIntro.
    iNamed "HinvO".
    iDestruct (txnsys_inv_expose_future_extract_ts with "Htxnsys")
      as (future ts) "[Htxnsys Hts]".
    (* Prove [key_inv] are linearizable after [ts]. *)
    iDestruct (keys_inv_before_linearize with "Hkeys Hts") as "[Hkeys Hts]".
    iExists ts.
    (* Pass [ts_auth γ ts] to the underlying layer. *)
    iFrame "Hts".
    iIntros (tid) "[Hts %Htidgt]".
    iDestruct (largest_ts_witness with "Hts") as "#Htidlb".

    pose proof (peek_spec future tid) as Hpeek.
    set form := peek _ _ in Hpeek.
    set Qr := λ m, Q rds (m ∪ rds) ∧ dom m ⊆ dom rds.
    destruct (decide (incorrect_fcc Qr form)) as [Hifcc | HQ].
    { (* Case: Abort branch. *)
      iMod (txnsys_inv_linearize_abort form Q with "Htidlb Hdbpts Htxnsys Hkeys")
        as "(Hdbpts & Htxnsys & Hkeys & Htida & Hwrsexcl & Hclients & #HQ & #Hlnrzs & #Hlnrzed)".
      { apply Hdomr. }
      { apply Htidgt. }
      { apply Hpeek. }
      { done. }
      (* Choose the will-abort branch. Use [∅] as placeholder. *)
      iMod ("HAUC" $! false ∅ with "Hdbpts") as "HΦ".
      iMod "Hclose" as "_".
      iMod ("HinvC" with "[Hts Htxnsys Hkeys Hgroups Hrgs]") as "_".
      { iNamed "Htxnsys". iFrame "∗ # %". }
      (* Allocate transaction local view [txnmap_ptstos τ r]. *)
      iMod (txnmap_alloc rds) as (τ) "[Htxnmap Htxnpts]".
      iIntros "!> Htxn".
      wp_pures.
      wp_apply (wp_Txn__attach with "[$Hclients $Htxn]").
      iIntros "Htxn".
      iAssert (own_txn txn tid rds γ τ)%I with "[Htxn Htxnmap]" as "Htxn".
      { iClear "Hinv". do 2 iNamed "Htxn".
        iExists _, ∅.
        rewrite map_empty_union.
        by iFrame "∗ # %".
      }

      (*@     cmt := body(txn)                                                    @*)
      (*@                                                                         @*)
      wp_apply ("Hbody" with "[$Htxn $Htxnpts]"); first done.
      iIntros (cmt) "[Htxn Hpts]".

      (*@     if !cmt {                                                           @*)
      (*@         // This transaction has not really requested to prepare yet, so no @*)
      (*@         // cleanup tasks are required.                                  @*)
      (*@         txn.cancel()                                                    @*)
      (*@         return false                                                    @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      wp_if_destruct.
      { wp_apply (wp_Txn__cancel with "[$Htxn $Htida $Hwrsexcl]").
        iIntros "Htxn".
        wp_pures.
        iApply "HΦ".
        by iFrame.
      }

      (*@     status := txn.prepare()                                             @*)
      (*@                                                                         @*)
      iDestruct "Hpts" as (w) "([%HQ %Hdomw] & [_ HRa] & Hpts)".
      iAssert (|={⊤}=> ∃ wrst, own_txn_stable txn tid rds wrst γ τ)%I
        with "[Htxn Hwrsexcl Hpts]" as "Htxn".
      { iClear "Hinv". iNamed "Htxn".
        iDestruct (txnmap_subseteq with "Htxnmap Hpts") as %Hsubseteq.
        unshelve epose proof (subseteq_dom_eq _ _ Hsubseteq _) as Heq.
        { clear -Hincl Hdomw. set_solver. }
        subst w.
        iInv "Hinv" as "> HinvO" "HinvC".
        iNamed "HinvO".
        iMod (txnsys_inv_preprepare with "HQ Hwrsexcl Htxnsys") as "[Htxnsys Hwrsrcpt]".
        { apply Hvts. }
        { apply Hvwrs. }
        { done. }
        iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
        iFrame "∗ # %".
        do 2 iNamed "Hwrs".
        iFrame "∗ %".
        rewrite -big_sepM2_fupd.
        iApply (big_sepM2_mono with "Hpwrsm").
        iIntros (g r m Hr Hm) "Hm".
        by iMod (own_map_persist with "Hm") as "Hm".
      }
      iMod "Htxn" as (wrst) "Htxn".
      wp_apply (wp_Txn__prepare with "Htxn").
      iIntros (status) "[Htxn Hstatus]".

      (*@     if status == TXN_COMMITTED {                                        @*)
      (*@         // A backup coordinator must have committed this transaction, so simply @*)
      (*@         // reset the write-set here.                                    @*)
      (*@         txn.reset()                                                     @*)
      (*@         return true                                                     @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      wp_if_destruct.
      { destruct status eqn:Hstatus; [done | | done]. clear Heqb.
        subst status.
        iDestruct "Hstatus" as (wrs) "Hcmt".
        (* Obtain a contradiction from [Hcmt] and [Htida]. *)
        iApply fupd_wp.
        iInv "Hinv" as "> HinvO" "HinvC".
        iNamed "HinvO". do 2 iNamed "Htxnsys".
        iDestruct (txn_res_lookup with "Hresm Hcmt") as %Hcmt.
        iDestruct (wabt_tid_elem_of with "Htidas Htida") as %Hwabt.
        rewrite -Htidas in Hwabt.
        iDestruct (elem_of_tmodas_partitioned_tids with "Hpart") as %[_ Hnotin].
        { apply Hwabt. }
        by specialize (Hnotin _ Hcmt).
      }
      rename Heqb into Hstatusnc.

      (*@     if status == TXN_ABORTED {                                          @*)
      (*@         // Ghost action: Abort this transaction.                        @*)
      (*@         txn.abort()                                                     @*)
      (*@         return false                                                    @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      wp_if_destruct.
      { destruct status eqn:Hstatus; [done | done |]. clear Heqb.
        subst status.
        wp_apply (wp_Txn__abort with "Hstatus [$Htxn $Htida]").
        iIntros "Htxn".
        wp_pures.
        iApply "HΦ".
        by iFrame.
      }
      rename Heqb into Hstatusna.

      (*@     // Ghost action: Commit this transaction.                           @*)
      (*@     txn.commit()                                                        @*)
      (*@     return true                                                         @*)
      (*@ }                                                                       @*)
      destruct status; [| done | done]. simpl. clear Hstatusnc Hstatusna.
      iDestruct "Hstatus" as (wrs) "#Hprep".
      iAssert (⌜wrst = wrs⌝)%I as %->.
      { iClear "Hinv". iNamed "Htxn".
        iDestruct "Hprep" as "[#Hwrsrcpt _]".
        by iDestruct (txn_wrs_agree with "Hwrsrcpt Htxnwrs") as %?.
      }
      wp_apply (wp_Txn__commit_in_abort_future with "Hlnrzed Hprep [$Htxn $Htida]").
      iIntros ([]).
    }
    { (* Case: Commit branch. *)
      destruct form as [| | wrs | wrs]; [done | done | done |].
      apply dec_stable in HQ. simpl in Hpeek.
      subst Qr.
      destruct HQ as [HQ Hdomwrs].
      iMod (txnsys_inv_linearize_commit wrs Q with "Htidlb Hdbpts Htxnsys Hkeys")
        as "(Hdbpts & Htxnsys & Hkeys & Htidc & Hwrsexcl & Hclients & #HQ & #Hlnrzs & #Hlnrzed)".
      { apply Hdomwrs. }
      { apply Hdomr. }
      { apply Htidgt. }
      { apply Hpeek. }
      (* Choose the will-commit branch. *)
      iMod ("HAUC" $! true (wrs ∪ rds) with "[$Hdbpts]") as "HΦ"; first done.
      iMod "Hclose" as "_".
      iMod ("HinvC" with "[Hts Htxnsys Hkeys Hgroups Hrgs]") as "_".
      { iNamed "Htxnsys". iFrame "∗ # %". }
      iClear "Hinv".
      (* Allocate transaction local view [txnmap_ptstos τ r]. *)
      iMod (txnmap_alloc rds) as (τ) "[Htxnmap Htxnpts]".
      iIntros "!> Htxn".
      wp_apply (wp_Txn__attach with "[$Hclients $Htxn]").
      iIntros "Htxn".
      iAssert (own_txn txn tid rds γ τ)%I with "[Htxn Htxnmap]" as "Htxn".
      { do 2 iNamed "Htxn".
        iExists _, ∅.
        rewrite map_empty_union.
        by iFrame "∗ # %".
      }

      (*@     cmt := body(txn)                                                    @*)
      (*@                                                                         @*)
      wp_apply ("Hbody" with "[$Htxn $Htxnpts]"); first done.
      iIntros (cmt) "[Htxn Hpts]".

      (*@     if !cmt {                                                           @*)
      (*@         // This transaction has not really requested to prepare yet, so no @*)
      (*@         // cleanup tasks are required.                                  @*)
      (*@         txn.cancel()                                                    @*)
      (*@         return false                                                    @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      wp_if_destruct.
      { wp_apply (wp_Txn__cancel_in_commit_future with "[$Htxn $Htidc $Hwrsexcl]").
        iIntros ([]).
      }

      (*@     status := txn.prepare()                                             @*)
      (*@                                                                         @*)
      clear HQ.
      iDestruct "Hpts" as (w) "([%HQ %Hdomw] & [HRc _] & Hpts)".
      iAssert (|={⊤}=> ∃ wrst, own_txn_stable txn tid rds wrst γ τ ∗ ⌜w = wrst ∪ rds⌝)%I
        with "[Htxn Hwrsexcl Hpts]" as "Htxn".
      { clear p.
        iDestruct "Htxn" as (p wrst) "Htxn". iNamed "Htxn".
        iDestruct (txnmap_subseteq with "Htxnmap Hpts") as %Hsubseteq.
        unshelve epose proof (subseteq_dom_eq _ _ Hsubseteq _) as Heq.
        { clear -Hincl Hdomw. set_solver. }
        subst w.
        iInv "Hinv" as "> HinvO" "HinvC".
        iNamed "HinvO".
        iMod (txnsys_inv_preprepare with "HQ Hwrsexcl Htxnsys") as "[Htxnsys Hwrsrcpt]".
        { apply Hvts. }
        { apply Hvwrs. }
        { done. }
        iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
        iFrame "∗ # %".
        do 2 iNamed "Hwrs".
        iFrame "∗ %".
        iApply fupd_sep.
        iSplitL; last done.
        rewrite -big_sepM2_fupd.
        iApply (big_sepM2_mono with "Hpwrsm").
        iIntros (g r m Hr Hm) "Hm".
        by iMod (own_map_persist with "Hm") as "Hm".
      }
      iMod "Htxn" as (wrst) "[Htxn %Heq]". subst w.
      wp_apply (wp_Txn__prepare with "Htxn").
      iIntros (status) "[Htxn Hstatus]".

      (*@     if status == TXN_COMMITTED {                                        @*)
      (*@         // A backup coordinator must have committed this transaction, so simply @*)
      (*@         // reset the write-set here.                                    @*)
      (*@         txn.reset()                                                     @*)
      (*@         return true                                                     @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      wp_if_destruct.
      { destruct status eqn:Hstatus; [done | | done]. clear Heqb.
        subst status.
        iDestruct "Hstatus" as (wrsc) "#Hwrsc".
        iNamed "Htxn".
        (* Obtain [wrsc = wrs ∧ wrst = wrs]. *)
        iAssert (|={⊤}=> own_cmt_tmod γ tid wrs ∗ ⌜wrsc = wrs ∧ wrst = wrs⌝)%I
          with "[Htidc]" as "Htidc".
        { iInv "Hinv" as "> HinvO" "HinvC".
          iNamed "HinvO". do 2 iNamed "Htxnsys".
          iDestruct (txn_res_lookup with "Hresm Hwrsc") as %Hwrsc.
          iDestruct (elem_of_committed_partitioned_tids with "Hpart") as %[Hnotinwc Hnotinwa].
          { by eauto. }
          iDestruct (cmt_tmod_lookup with "Htidcs Htidc") as %Htidc.
          apply Htidcs in Htidc.
          (* Prove [resm !! tid = Some (ResCommitted wrs)]. *)
          destruct Htidc as [Htmodcs | Hresm].
          { by rewrite not_elem_of_dom Htmodcs in Hnotinwc. }
          rewrite Hresm in Hwrsc. symmetry in Hwrsc. inv Hwrsc.
          iDestruct (big_sepM_lookup with "Hvr") as "Hr"; first apply Hresm.
          iDestruct "Hr" as "[Hrcp _]".
          iDestruct (txn_wrs_agree with "Hrcp Htxnwrs") as %->.
          iMod ("HinvC" with "[-Htidc]") as "_".
          { by iFrame "∗ # %". }
          by iFrame "∗ %".
        }
        iMod "Htidc" as "[Htidc %Heq]".
        destruct Heq as [-> ->].
        iNamed "Htxn".
        wp_apply (wp_Txn__reset with "Hwrs").
        iIntros "Hwrs".
        iAssert (own_txn_ptgs_empty txn)%I with "[Hptgs]" as "Hptgs".
        { iNamed "Hptgs". by iFrame. }
        wp_pures.
        iApply "HΦ".
        by iFrame "∗ # %".
      }
      rename Heqb into Hstatusnc.

      (*@     if status == TXN_ABORTED {                                          @*)
      (*@         // Ghost action: Abort this transaction.                        @*)
      (*@         txn.abort()                                                     @*)
      (*@         return false                                                    @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      wp_if_destruct.
      { destruct status eqn:Hstatus; [done | done |]. clear Heqb.
        subst status. simpl.
        wp_apply (wp_Txn__abort_in_commit_future with "Hstatus [$Htxn $Htidc]").
        iIntros ([]).
      }
      rename Heqb into Hstatusna.

      (*@     // Ghost action: Commit this transaction.                           @*)
      (*@     txn.commit()                                                        @*)
      (*@     return true                                                         @*)
      (*@ }                                                                       @*)
      destruct status as [| |] eqn:Hstatus; [| done | done].
      simpl. clear Hstatus Hstatusnc Hstatusna.
      iDestruct "Hstatus" as (wrsc) "#Hprep".
      iAssert (⌜wrsc = wrst⌝)%I as %->.
      { iNamed "Htxn".
        iDestruct "Hprep" as "[Hwrsrcpt _]".
        by iDestruct (txn_wrs_agree with "Htxnwrs Hwrsrcpt") as %?.
      }
      wp_apply (wp_Txn__commit with "Hlnrzed Hprep [Htxn Htidc]").
      { iFrame "∗ #". }
      iIntros "[Htxn %Heq]". subst wrst.
      wp_pures.
      iApply "HΦ".
      by iFrame.
    }
  Qed.

End program.
