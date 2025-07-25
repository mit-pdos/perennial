From RecordUpdate Require Import RecordSet.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant wal.common_proof.

Section goose_lang.
Context `{!heapGS Σ}.
Context `{!walG Σ}.

Implicit Types (v:val) (z:Z).
Implicit Types (γ: wal_names).
Implicit Types (s: log_state.t) (memLog: list update.t) (txns: list (u64 * list update.t)).
Implicit Types (pos: u64) (txn_id: nat).

Context (P: log_state.t -> iProp Σ).
Let N := walN.
Let innerN := walN .@ "wal".
Let circN := walN .@ "circ".

Theorem wal_wf_update_durable :
  relation.wf_preserved (update_durable) wal_wf.
Proof.
  intros s1 s2 [] Hwf ?; simpl in *; monad_inv.
  destruct Hwf as (Hwf1&Hwf2&Hwf3).
  destruct s1; split; unfold log_state.updates in *; simpl in *; eauto.
  split; eauto.
  lia.
Qed.

(* just an example, to work out the Flush proof without all the complications *)
Theorem wp_updateDurable (Q: iProp Σ) l γ dinit :
  {{{ is_wal P l γ dinit ∗
       (∀ σ σ' b,
         ⌜wal_wf σ⌝ -∗
         ⌜relation.denote (update_durable) σ σ' b⌝ -∗
         (P σ ={⊤ ∖ ↑N}=∗ P σ' ∗ Q))
   }}}
    Skip
  {{{ RET #(); Q}}}.
Proof.
  iIntros (Φ) "[#Hwal Hfupd] HΦ".
  iDestruct "Hwal" as "[Hwal Hcirc]".
  iInv "Hwal" as "Hinv".
  wp_rec. wp_pures.
  iDestruct "Hinv" as (σ) "(Hinner&HP)".
  iNamed "Hinner".
  iNamed "Hdisk".
  iNamed "Hdisk".
  iNamed "circ.end".
  pose proof (is_txn_bound _ _ _ Hend_txn) as Hend_bound.
  iMod (fupd_mask_subseteq (⊤ ∖ ↑N)) as "HinnerN"; first by solve_ndisj.
  iMod ("Hfupd" $! σ (set log_state.durable_lb (λ _, (σ.(log_state.durable_lb) `max` diskEnd_txn_id)%nat) σ)
          with "[% //] [%] [$HP]") as "[HP HQ]".
  { simpl.
    econstructor; monad_simpl.
    econstructor; monad_simpl; lia. }
  iMod "HinnerN" as "_".
  iSpecialize ("HΦ" with "HQ").
  iFrame "HΦ".
  iIntros "!> !>".
  iExists _; iFrame "HP".
  iSplit.
  - iPureIntro.
    eapply wal_wf_update_durable; eauto.
    { simpl; monad_simpl.
      econstructor; monad_simpl.
      econstructor; monad_simpl; lia. }
  - simpl.
    iFrame "Hmem Howncs HnextDiskEnd_inv Htxns_ctx γtxns".
    iExists installed_txn_id, _, _. simpl. iFrame (Hdaddrs_init) "Hinstalled Hdurable circ.start Hbasedisk".
    iExists _, diskEnd_txn_id.
    rewrite (Nat.max_l (_ `max` _)%nat _); last by lia.
    iFrame "# %".
    iPureIntro.
    split; first by lia.
    split; first by lia.
    destruct (decide (σ.(log_state.durable_lb) ≤ diskEnd_txn_id)).
    {
      rewrite Nat.max_r; last by lia.
      rewrite subslice_zero_length.
      apply Forall_nil_2.
    }
    rewrite Nat.max_l; last by lia.
    rewrite -(subslice_app_contig _ (S diskEnd_txn_id)) in Hdurable_nils;
      last by lia.
    apply Forall_app in Hdurable_nils.
    intuition.
Qed.

Theorem simulate_flush l γ Q σ dinit pos txn_id nextDiskEnd_txn_id mutable :
  is_circular circN (circular_pred γ) γ.(circ_name) -∗
  (is_wal_inner l γ σ dinit ∗ P σ) -∗
  diskEnd_at_least γ.(circ_name) (uint.Z pos) -∗
  txn_pos γ txn_id pos -∗
  memLog_linv_nextDiskEnd_txn_id γ mutable nextDiskEnd_txn_id -∗
  (∀ (σ σ' : log_state.t) (b : ()),
      ⌜wal_wf σ⌝
        -∗ ⌜relation.denote (log_flush pos txn_id) σ σ' b⌝ -∗ P σ ={⊤ ∖ ↑N}=∗ P σ' ∗ Q) -∗
  |NC={⊤ ∖ ↑innerN}=>
    ∃ σ' nextDiskEnd_txn_id',
      is_wal_inner l γ σ' dinit ∗ P σ' ∗ Q ∗
      memLog_linv_nextDiskEnd_txn_id γ mutable nextDiskEnd_txn_id' ∗
      ⌜nextDiskEnd_txn_id ≤ nextDiskEnd_txn_id' < length σ.(log_state.txns)⌝ ∗
      ⌜Forall (λ x, x.2 = []) (
        subslice (S nextDiskEnd_txn_id) (S nextDiskEnd_txn_id')
        σ.(log_state.txns)
      )⌝.
Proof.
  iIntros "#Hcirc Hinv #Hlb #Hpos_txn HstableSet Hfupd".
  iDestruct "Hinv" as "[Hinner HP]".
  iNamed "Hinner".
  iNamed "Hdisk".
  iNamed "Hdisk".
  iNamed "circ.end".
  iMod (is_circular_diskEnd_lb_agree with "Hlb Hcirc Howncs") as "(%Hlb&Howncs)"; first by solve_ndisj.
  iDestruct (txn_pos_valid_general with "Htxns_ctx Hpos_txn") as %His_txn.
  pose proof (is_txn_bound _ _ _ His_txn).
  pose proof (is_txn_bound _ _ _ Hend_txn).
  pose proof (wal_wf_txns_mono_pos Hwf His_txn Hend_txn) as Hpos_diskEnd.

  iMod (fupd_mask_subseteq (⊤ ∖ ↑N)) as "HinnerN"; first by solve_ndisj.
  iMod ("Hfupd" $!
    σ
    (
      set log_state.durable_lb (λ _,
        (diskEnd_txn_id `max` (σ.(log_state.durable_lb) `max` txn_id))%nat
      ) σ
    )
    with "[% //] [%] HP"
  ) as "[HP HQ]".
  { simpl; monad_simpl.
    repeat (econstructor; monad_simpl; eauto); lia.
  }
  iMod "HinnerN" as "_".
  iFrame "HQ".

  iAssert (⌜
    uint.Z pos = uint.Z diskEnd →
    Forall (λ x, x.2 = []) (
      subslice
        (S (σ.(log_state.durable_lb) `max` diskEnd_txn_id))
        (S txn_id)
        σ.(log_state.txns)
    )
  ⌝)%I with "[HstableSet HnextDiskEnd_inv]" as "%Hpos_diskEnd_nils".
  {
    iApply pure_impl_2.
    iIntros (Hpos_diskEnd_eq).
    apply word.unsigned_inj in Hpos_diskEnd_eq.
    rewrite Hpos_diskEnd_eq in His_txn.
    iPoseProof (subslice_stable_nils2 with "[HstableSet HnextDiskEnd_inv]")
      as "Hnils".
    1: eassumption.
    1: apply Hdurable_lb_pos.
    1: apply His_txn.
    {
      iSplit; first by iFrame.
      iFrame "#".
    }
    iFrame.
  }

  iAssert (|==>
    ⌜Forall (λ x, x.2 = []) (
      subslice
        (S diskEnd_txn_id)
        (S (diskEnd_txn_id `max` (txn_id)))
        σ.(log_state.txns)
    )⌝ ∗
    (diskEnd_txn_id `max` (txn_id))%nat
      [[γ.(stable_txn_ids_name)]]↦ro tt ∗
    nextDiskEnd_inv γ σ.(log_state.txns) ∗
    txns_ctx γ σ.(log_state.txns) ∗
    ∃ nextDiskEnd_txn_id',
      memLog_linv_nextDiskEnd_txn_id γ mutable nextDiskEnd_txn_id' ∗
      ⌜nextDiskEnd_txn_id ≤ nextDiskEnd_txn_id' < length σ.(log_state.txns)⌝ ∗
      ⌜Forall (λ x, x.2 = []) (
        subslice (S nextDiskEnd_txn_id) (S nextDiskEnd_txn_id')
        σ.(log_state.txns)
      )⌝
  )%I
    with "[HstableSet HnextDiskEnd_inv Htxns_ctx]"
    as "H".
  {
    destruct (decide (
      txn_id ≤ diskEnd_txn_id
    )%nat).
    { rewrite -> (max_l diskEnd_txn_id _) by lia.
      rewrite ?subslice_zero_length. iSplitR; first by done.

      iAssert (⌜nextDiskEnd_txn_id < length σ.(log_state.txns)⌝)%I as "%HnextDiskEnd_txn_bound".
      {
        iNamed "HstableSet".
        iDestruct (txn_pos_valid_general with "Htxns_ctx HnextDiskEnd_txn") as %HnextDiskEnd_txn_bound.
        eapply is_txn_bound in HnextDiskEnd_txn_bound. iPureIntro. lia.
      }
      iSplitR; first done.
      iFrame "HnextDiskEnd_inv".
      iFrame "Htxns_ctx".
      iExists nextDiskEnd_txn_id.
      rewrite ?subslice_zero_length.
      iFrame "HstableSet".
      iModIntro.
      iSplit; first by iPureIntro; lia.
      iPureIntro.
      eauto.
    }

    pose proof (wal_wf_txns_mono_pos Hwf His_txn Hend_txn).
    replace diskEnd with pos in * by word.

    iMod (stable_txn_id_advance _ _ _ txn_id
          with "HstableSet HnextDiskEnd_inv Hend_txn_stable Htxns_ctx")
      as "H"; eauto.
    { lia. }

    iDestruct "H" as "(#Hstable & HnextDiskEnd_inv & Htxns_ctx & H)".
    iDestruct "H" as (nextDiskEnd_txn_id') "(HstableSet & %Hle & %Hnils')".
    iModIntro.

    iSplit.
    {
      iDestruct (subslice_stable_nils with "[$HnextDiskEnd_inv $Hend_txn_stable]") as "%Hnils_txn".
      1: eassumption.
      2: eassumption.
      2: eapply His_txn.
      1: lia.
      iPureIntro.
      destruct (decide (diskEnd_txn_id ≤ txn_id)%nat).
      {
        rewrite Nat.max_r; last by lia.
        assumption.
      }
      rewrite Nat.max_l; last by lia.
      rewrite subslice_zero_length.
      apply Forall_nil_2.
    }

    iFrame "HnextDiskEnd_inv".
    iSplitR.
    {
      destruct (decide (diskEnd_txn_id ≤ txn_id)%nat).
      {
        rewrite (Nat.max_r _ txn_id); last by lia.
        iFrame "#".
      }
      rewrite (Nat.max_l _ txn_id); last by lia.
      iFrame "#".
    }
    iFrame "Htxns_ctx".
    iExists nextDiskEnd_txn_id'.
    iFrame "HstableSet".
    done.
  }

  iMod "H" as "(%Hnils & #Hstable & HnextDiskEnd_inv & Htxns_ctx & H)".
  iDestruct "H" as (nextDiskEnd_txn_id') "(HstableSet & %Hle & %Hnils')".

  iModIntro.
  iExists _, _; iFrame "HP".
  iFrame (Hle Hnils') "HstableSet".
  iSplit; auto.
  { iPureIntro.
    eapply wal_wf_update_durable; eauto.
    simpl; monad_simpl.
    repeat (econstructor; monad_simpl; eauto); lia.
  }
  simpl.
  iFrame "∗#".
  iSplitL.
  2: {
    iPureIntro.
    auto with lia.
  }
  iExists _, diskEnd_txn_id.
  simpl.
  iSplit; first by (iPureIntro; lia).
  iSplit; first by (iPureIntro; lia).
  iSplit.
  {
    iPureIntro.
    destruct (decide (
      (diskEnd_txn_id `max` txn_id) ≤ σ.(log_state.durable_lb)
    )%nat).
    {
      rewrite Nat.max_r; last by lia.
      rewrite Nat.max_l; last by lia.
      destruct (decide (S diskEnd_txn_id ≤ txn_id)%nat).
      {
        rewrite Nat.max_r in Hnils; last by lia.
        rewrite -(subslice_app_contig _ (S diskEnd_txn_id)) in Hdurable_nils;
          last by lia.
        apply Forall_app in Hdurable_nils.
        intuition.
      }
      rewrite -(subslice_app_contig _ (S diskEnd_txn_id)) in Hdurable_nils;
        last by lia.
      apply Forall_app in Hdurable_nils.
      intuition.
    }
    replace (_ `max` (_ `max` _))%nat with (diskEnd_txn_id `max` txn_id)%nat
      by lia.
    assumption.
  }
  iSplit.
  {
    iPureIntro.
    destruct (decide (uint.Z pos < uint.Z diskEnd)) as [Hcmp|Hcmp].
    {
      apply Hpos_diskEnd in Hcmp.
      replace (_ `max` _)%nat
        with (σ.(log_state.durable_lb) `max` diskEnd_txn_id)%nat
        by lia.
      eassumption.
    }
    rewrite -HdiskEnd_val in Hlb.
    assert (uint.Z pos = uint.Z diskEnd) as Hpos_diskEnd_eq by lia.
    apply word.unsigned_inj in Hpos_diskEnd_eq.
    subst pos.
    rewrite Nat.max_l; last by lia.
    destruct (decide
      ((σ.(log_state.durable_lb) `max` diskEnd_txn_id) ≤ txn_id)%nat
    ).
    {
      rewrite Nat.max_r; last by lia.
      rewrite Nat.max_r; last by lia.
      assumption.
    }
    replace (_ `max` _)%nat
      with (σ.(log_state.durable_lb) `max` diskEnd_txn_id)%nat; last by lia.
    assumption.
  }
  iSplit; first by (iPureIntro; assumption).
  iSplit; first by (iPureIntro; assumption).
  destruct (decide (
    txn_id ≤ (σ.(log_state.durable_lb) `max` diskEnd_txn_id)
  )%nat).
  {
    replace ((_ `max` _) `max` _)%nat
      with (σ.(log_state.durable_lb) `max` diskEnd_txn_id)%nat;
      last by lia.
    iFrame "#".
  }
  replace ((_ `max` _) `max` _)%nat
    with (diskEnd_txn_id `max` txn_id)%nat; last by lia.
  iFrame "#".

  Unshelve.
  all: try constructor.
Qed.

(* this is a dumb memory safety proof for loading nextDiskEnd when its value
doesn't matter for correctness *)
Theorem wp_load_some_nextDiskEnd st γ :
  {{{ wal_linv st γ }}}
        struct.loadF sliding "mutable"
          (struct.loadF WalogState "memLog" #st)
  {{{ (nextDiskEnd:u64), RET #nextDiskEnd; wal_linv st γ }}}.
Proof.
  iIntros (Φ) "Hinv HΦ".
  iNamed "Hinv".
  iNamed "Hfields".
  iNamed "Hfield_ptsto".
  wp_loadField.
  (* this is very bad, breaks sliding abstraction boundary *)
  iNamed "His_memLog"; iNamed "Hinv". wp_loadField.
  iApply "HΦ".
  by iFrame "∗#".
Qed.

Theorem wp_Walog__Flush (Q: iProp Σ) l γ dinit txn_id pos :
  {{{ is_wal P l γ dinit ∗
      txn_pos γ txn_id pos ∗
       (∀ σ σ' b,
         ⌜wal_wf σ⌝ -∗
         ⌜relation.denote (log_flush pos txn_id) σ σ' b⌝ -∗
         (P σ ={⊤ ∖ ↑N}=∗ P σ' ∗ Q))
   }}}
    Walog__Flush #l #pos
  {{{ RET #(); Q}}}.
Proof.
  iIntros (Φ) "(#Hwal & #Hpos_txn & Hfupd) HΦ".
  destruct_is_wal.

  wp_apply util_proof.wp_DPrintf.
  wp_loadField.
  wp_apply (wp_Mutex__Lock with "lk"). iIntros "(Hlocked&Hlkinv)".
  wp_loadField.
  wp_apply (wp_Cond__Broadcast with "cond_logger").
  wp_loadField.

  wp_apply (wp_load_some_nextDiskEnd with "Hlkinv"); iIntros (x) "Hlkinv".
  wp_pures.

  wp_apply (wp_If_optional with "[] [Hlkinv Hlocked]"); [ | iAccu | ].
  {
    iIntros (Φ') "(Hlkinv&Hlocked) HΦ".
    wp_loadField.
    wp_apply (wp_endGroupTxn with "Hlkinv").
    iIntros "Hlkinv".
    wp_pures.
    iApply ("HΦ" with "[$]").
  }
  iIntros "(Hlkinv&Hlocked)".
  wp_pures.

  wp_bind (For _ _ _).
  wp_apply (wp_forBreak_cond (λ b,
    wal_linv σₛ.(wal_st) γ ∗ locked #σₛ.(memLock) ∗
    if b then ⊤ else diskEnd_at_least γ.(circ_name) (uint.Z pos)
  )%I with "[] [$Hlkinv $Hlocked]").
  { iIntros "!>" (Φ') "(Hlkinv&Hlocked&_) HΦ".
    wp_loadField.
    iNamed "Hlkinv".
    iNamed "Hfields".
    iNamed "Hfield_ptsto".
    wp_loadField.
    wp_pures.
    wp_if_destruct.
    - wp_loadField.
      wp_apply (wp_Cond__Wait with "[-HΦ $cond_logger $lk $Hlocked]").
      { by iFrame "∗ #". }
      iIntros "(Hlocked&Hlockin)".
      wp_pures.
      iApply "HΦ"; by iFrame.
    - iApply "HΦ".
      iFrame "Hlocked".
      iNamed "HdiskEnd_circ".
      iSplitL.
      { by iFrame "∗#". }
      iApply (diskEnd_at_least_mono with "HdiskEnd_at_least"); auto.
  }

  iIntros "(Hlkinv&Hlocked&#HdiskEnd_lb)".
  do 2 wp_pure.
  wp_bind Skip.
  iDestruct "Hwal" as "[Hwal Hcirc]".
  iInv "Hwal" as "Hinv".
  iApply wp_ncfupd.
  wp_rec. wp_pures.
  iDestruct "Hinv" as (σ) "[Hinner HP]".
  iNamed "Hlkinv".
  iNamed "HmemLog_linv".

  iAssert (⌜txns = σ.(log_state.txns)⌝)%I as "%Htxnseq".
  {
    iNamed "Hinner".
    iDestruct (ghost_var_agree with "Howntxns γtxns") as "%Htxnseq".
    done.
  }
  subst.

  iMod (simulate_flush with "Hcirc [$Hinner $HP] HdiskEnd_lb Hpos_txn HnextDiskEnd Hfupd") as "H".
  iDestruct "H" as (σ' nextDiskEnd_txn_id') "(Hinner & HP & HQ & HnextDiskEnd & %Hle & %Hnils)".
  iApply fupd_ncfupd. iApply fupd_intro.
  iModIntro.

  iSplitL "Hinner HP".
  { iNext. iExists _. iFrame. }

  wp_loadField.
  wp_apply (wp_Mutex__Unlock with "[-HQ HΦ]").
  { iFrame "lk". iFrame "Hlocked". iNext. iExists _.
    iFrame "Hfields HdiskEnd_circ Hstart_circ".
    iExists _, _, _, _, _, _, _.
    iFrame "∗#%".
    iNamed "Hlinv_pers".
    iFrame "#%".
    iPureIntro.
    split; first by (intuition (eauto; try lia)).
    pose proof Htxns as [Hbnds Hregs].
    split.
    {
      intros bndry Hbndry.
      specialize (Hbnds bndry).
      apply list_elem_of_lookup in Hbndry.
      destruct Hbndry as [i Hbndry].
      do 4 (destruct i; first by (
        simpl in Hbndry; inversion Hbndry; subst bndry; clear Hbndry;
        apply Hbnds; set_solver
      )).
      destruct i.
      2: {
        destruct i; first by (
          simpl in Hbndry; inversion Hbndry; subst bndry; clear Hbndry;
          apply Hbnds; set_solver
        ).
        inversion Hbndry.
      }
      simpl in Hbndry; inversion Hbndry; subst bndry; clear Hbndry.
      simpl.
      clear Hbnds.
      pose proof Htxns as [Hbnds _].
      unshelve (epose proof (Hbnds _ _) as Hbnd).
      2: {
        apply list_elem_of_lookup.
        exists mwrb_us.
        reflexivity.
      }
      simpl in Hbnd.
      lia.
    }
    intros i bndry1 bndry2 Hbndry1 Hbndry2.
    specialize (Hregs i bndry1 bndry2).
    do 3 (destruct i; first by (
      simpl in Hbndry1; inversion Hbndry1; subst bndry1; clear Hbndry1;
      simpl in Hbndry2; inversion Hbndry2; subst bndry2; clear Hbndry2;
      simpl; apply Hregs; reflexivity
    )).
    clear Hregs.
    unshelve (epose proof (
      is_memLog_boundaries_region_consec mwrb_uss _ _ _ _ _ Htxns _ _
    ) as Hreg1).
    3-4: reflexivity.
    unshelve (epose proof (
      is_memLog_boundaries_region_consec mwrb_us _ _ _ _ _ Htxns _ _
    ) as Hreg2).
    3-4: reflexivity.
    simpl in Hreg1.
    simpl in Hreg2.
    destruct i.
    {
      simpl in Hbndry1; inversion Hbndry1; subst bndry1; clear Hbndry1;
      simpl in Hbndry2; inversion Hbndry2; subst bndry2; clear Hbndry2.
      simpl.
      split; first by lia.
      split; first by lia.
      rewrite -(subslice_app_contig _ (S nextDiskEnd_txn_id)); last by lia.
      apply is_memLog_region_append_nils; first by assumption.
      intuition.
    }
    destruct i; last by inversion Hbndry2.
    simpl in Hbndry1; inversion Hbndry1; subst bndry1; clear Hbndry1;
    simpl in Hbndry2; inversion Hbndry2; subst bndry2; clear Hbndry2.
    simpl.
    split; first by lia.
    split; first by lia.
    eapply is_memLog_region_prepend_nils; first by eassumption.
    rewrite subslice_app_contig; last by lia.
    intuition.
  }
  wp_pures. by iApply ("HΦ" with "HQ").
Qed.

End goose_lang.
