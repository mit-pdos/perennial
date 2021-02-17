From RecordUpdate Require Import RecordSet.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant wal.common_proof.

Section goose_lang.
Context `{!heapG Σ}.
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
  wp_call.
  iDestruct "Hinv" as (σ) "(Hinner&HP)".
  iNamed "Hinner".
  iNamed "Hdisk".
  iNamed "Hdisk".
  iNamed "circ.end".
  pose proof (is_txn_bound _ _ _ Hend_txn) as Hend_bound.
  iMod (fupd_mask_subseteq (⊤ ∖ ↑N)) as "HinnerN"; first by solve_ndisj.
  iMod ("Hfupd" $! σ (set log_state.durable_lb (λ _, diskEnd_txn_id) σ)
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
    iFrame.
    iExists _. iFrame "Howncs".
    iExists installed_txn_id, _. simpl. iFrame "# ∗ %".
    iExists _. iFrame "%". iPureIntro. lia.
Qed.

Theorem simulate_flush l γ Q σ dinit pos txn_id nextDiskEnd_txn_id mutable :
  is_circular circN (circular_pred γ) γ.(circ_name) -∗
  (is_wal_inner l γ σ dinit ∗ P σ) -∗
  diskEnd_at_least γ.(circ_name) (int.Z pos) -∗
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
        ⌜Forall (λ x, x.2 = []) (subslice (S nextDiskEnd_txn_id) (S nextDiskEnd_txn_id') σ.(log_state.txns))⌝.
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
  pose proof (wal_wf_txns_mono_pos Hwf His_txn Hend_txn).

  iMod (fupd_mask_subseteq (⊤ ∖ ↑N)) as "HinnerN"; first by solve_ndisj.
  iMod ("Hfupd" $! σ (set log_state.durable_lb (λ _, Nat.max σ.(log_state.durable_lb) txn_id) σ) with "[% //] [%] HP") as "[HP HQ]".
  { simpl; monad_simpl.
    repeat (econstructor; monad_simpl; eauto).
    lia. }
  iMod "HinnerN" as "_".
  iFrame "HQ".

  iAssert (|==> ⌜Forall (λ x, x.2 = []) (subslice (S diskEnd_txn_id) (S (diskEnd_txn_id `max` txn_id)) σ.(log_state.txns))⌝ ∗
           (diskEnd_txn_id `max` txn_id)%nat [[γ.(stable_txn_ids_name)]]↦ro tt ∗
           nextDiskEnd_inv γ σ.(log_state.txns) ∗
           txns_ctx γ σ.(log_state.txns) ∗
           ∃ nextDiskEnd_txn_id',
             memLog_linv_nextDiskEnd_txn_id γ mutable nextDiskEnd_txn_id' ∗
             ⌜nextDiskEnd_txn_id ≤ nextDiskEnd_txn_id' < length σ.(log_state.txns)⌝ ∗
             ⌜Forall (λ x, x.2 = []) (subslice (S nextDiskEnd_txn_id) (S nextDiskEnd_txn_id') σ.(log_state.txns))⌝
          )%I
    with "[HstableSet HnextDiskEnd_inv Htxns_ctx]"
    as "H".
  {
    destruct (decide (txn_id ≤ diskEnd_txn_id)).
    { rewrite -> (max_l diskEnd_txn_id txn_id) by lia.
      rewrite ?subslice_zero_length. iSplitR; first by done.

      iAssert (⌜nextDiskEnd_txn_id < length σ.(log_state.txns)⌝)%I as "%HnextDiskEnd_txn_bound".
      {
        iNamed "HstableSet".
        iDestruct (txn_pos_valid_general with "Htxns_ctx HnextDiskEnd_txn") as %HnextDiskEnd_txn_bound.
        eapply is_txn_bound in HnextDiskEnd_txn_bound. iPureIntro. lia.
      }

      iFrame "Hend_txn_stable".
      iFrame "HnextDiskEnd_inv".
      iFrame "Htxns_ctx".
      iExists nextDiskEnd_txn_id.
      rewrite ?subslice_zero_length.
      iFrame "HstableSet".
      iModIntro. iPureIntro. intuition eauto; try lia.
    }

    pose proof (wal_wf_txns_mono_pos Hwf His_txn Hend_txn).
    rewrite -> max_r by lia.
    replace diskEnd with pos in * by word.

    iMod (stable_txn_id_advance _ _ _ txn_id
          with "HstableSet HnextDiskEnd_inv Hend_txn_stable Htxns_ctx")
      as "H"; eauto.
    { lia. }

    iDestruct "H" as "(Hstable & HnextDiskEnd_inv & Htxns_ctx & H)".
    iDestruct "H" as (nextDiskEnd_txn_id') "(HstableSet & %Hle & %Hnils')".
    iModIntro.

    iSplit.
    {
      iDestruct (subslice_stable_nils with "[$HnextDiskEnd_inv $Hend_txn_stable]") as "H".
      1: eassumption.
      2: eassumption.
      2: eapply His_txn.
      1: lia.
      done.
    }

    iFrame "Hstable".
    iFrame "HnextDiskEnd_inv".
    iFrame "Htxns_ctx".
    iExists nextDiskEnd_txn_id'.
    iFrame "HstableSet".
    done.
  }

  iMod "H" as "(%Hnils & #Hstable & HnextDiskEnd_inv & Htxns_ctx & H)".
  iDestruct "H" as (nextDiskEnd_txn_id') "(HstableSet & %Hle & %Hnils')".

  iModIntro.
  iExists _, nextDiskEnd_txn_id'; iFrame "HP".
  iFrame "HstableSet".
  iFrame "%".
  iSplit; auto.
  { iPureIntro.
    eapply wal_wf_update_durable; eauto.
    simpl; monad_simpl.
    repeat (econstructor; monad_simpl; eauto); lia.
  }
  simpl.
  iFrame.
  iExists _; iFrame.
  iExists installed_txn_id, (Nat.max diskEnd_txn_id txn_id). iFrame "# ∗".
  iSplitL "Hinstalled".
  { iNamed "Hinstalled". iExists _, _. iFrame. iFrame "#". iPureIntro. auto with lia. }
  iSplit.
  - iNamed "Hdurable".
    iExists _, _, _, _.
    iFrame.
    iPureIntro.
    unfold circ_matches_txns in *. intuition try lia.
    rewrite -> (subslice_split_r _ (S diskEnd_txn_id) _ σ.(log_state.txns)) by lia.
    eapply has_updates_app_nils; eauto.
  - iExists diskEnd.
    iPureIntro.
    split_and!; simpl; auto.
    + eapply Nat.max_le_compat_r. lia.
    + pose proof (wal_wf_txns_mono_pos Hwf His_txn Hend_txn).
      destruct (decide (txn_id ≤ diskEnd_txn_id)).
      { rewrite max_l; last by lia. eauto. }
      rewrite max_r; last by lia.
      destruct (decide (int.Z pos = int.Z diskEnd)); try lia.
      replace diskEnd with pos; eauto.
      word.

  Unshelve.
  all: try constructor.
Qed.

(* this is a dumb memory safety proof for loading nextDiskEnd when its value
doesn't matter for correctness *)
Theorem wp_load_some_nextDiskEnd st γ :
  {{{ wal_linv st γ }}}
        struct.loadF sliding.S "mutable"
          (struct.loadF WalogState.S "memLog" #st)
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
  iExists _; iFrame "# ∗".
  iExists _; iFrame "# ∗".
  iSplit; auto.
  iSplit; auto.
  iExists _, _; iFrame "# ∗".
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
  wp_apply (acquire_spec with "lk"). iIntros "(Hlocked&Hlkinv)".
  wp_loadField.
  wp_apply (wp_condBroadcast with "cond_logger").
  wp_loadField.

  wp_apply (wp_load_some_nextDiskEnd with "Hlkinv"); iIntros (x) "Hlkinv".
  wp_pures.

  wp_apply (wp_If_optional with "[] [Hlkinv Hlocked]"); [ | iAccu | ].
  {
    iIntros (Φ') "(Hlkinv&Hlocked) HΦ".
    wp_loadField.
    wp_apply (wp_endGroupTxn with "[$Hwal $Hlkinv]").
    iIntros "Hlkinv".
    wp_pures.
    iApply ("HΦ" with "[$]").
  }
  iIntros "(Hlkinv&Hlocked)".
  wp_pures.

  wp_bind (For _ _ _).
  wp_apply (wp_forBreak_cond (λ b,
               wal_linv σₛ.(wal_st) γ ∗ locked #σₛ.(memLock) ∗
               if b then ⊤ else diskEnd_at_least γ.(circ_name) (int.Z pos))%I
           with "[] [$Hlkinv $Hlocked]").
  { iIntros "!>" (Φ') "(Hlkinv&Hlocked&_) HΦ".
    wp_loadField.
    iNamed "Hlkinv".
    iNamed "Hfields".
    iNamed "Hfield_ptsto".
    wp_loadField.
    wp_pures.
    wp_if_destruct.
    - wp_loadField.
      wp_apply (wp_condWait with "[-HΦ $cond_logger $lk $Hlocked]").
      { iExists _; iFrame "∗ #".
        iExists _; by iFrame "∗ #". }
      iIntros "(Hlocked&Hlockin)".
      wp_pures.
      iApply "HΦ"; iFrame.
    - iApply "HΦ".
      iFrame "Hlocked".
      iNamed "HdiskEnd_circ".
      iSplitL.
      { iExists _; iFrame "# ∗".
        iExists _; by iFrame "# ∗". }
      iApply (diskEnd_at_least_mono with "HdiskEnd_at_least"); auto.
  }

  iIntros "(Hlkinv&Hlocked&#HdiskEnd_lb)".
  wp_seq.
  wp_bind Skip.
  iDestruct "Hwal" as "[Hwal Hcirc]".
  iInv "Hwal" as "Hinv".
  iApply wp_ncfupd.
  wp_call.
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
  wp_apply (release_spec with "[-HQ HΦ]").
  { iFrame "lk". iFrame "Hlocked". iNext. iExists _.
    iFrame "Hfields HdiskEnd_circ Hstart_circ".
    iExists _, _, _, _, _, _, _.
    iFrame "∗#%".
    iNamed "Hlinv_pers".
    iFrame "#%".
    iNamed "Htxns".
    iFrame "%".
    iPureIntro. intuition (eauto; try lia).
    - rewrite -> (subslice_split_r _ (S nextDiskEnd_txn_id) _ σ.(log_state.txns)); try lia.
      eapply has_updates_app_nils; eauto.
    - rewrite <- (subslice_to_end _ (length σ.(log_state.txns)) σ.(log_state.txns)) by lia.
      rewrite <- (subslice_to_end _ (length σ.(log_state.txns)) σ.(log_state.txns)) in His_nextTxn by lia.
      rewrite -> (subslice_split_r _ (S nextDiskEnd_txn_id') _ σ.(log_state.txns)) in His_nextTxn by lia.
      eapply has_updates_prepend_nils in His_nextTxn; eauto.
  }
  iApply ("HΦ" with "HQ").
Qed.

End goose_lang.
