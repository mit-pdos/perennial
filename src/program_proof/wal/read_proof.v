From RecordUpdate Require Import RecordSet.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant wal.common_proof.

Section goose_lang.
Context `{!heapGS Σ}.
Context `{!walG Σ}.

Implicit Types (v:val) (z:Z).
Implicit Types (γ: wal_names).
Implicit Types (s: log_state.t) (memLog: slidingM.t) (txns: list (u64 * list update.t)).
Implicit Types (pos: u64) (txn_id: nat).

Context (P: log_state.t -> iProp Σ).
Let N := walN.
Let innerN := walN .@ "wal".
Let circN := walN .@ "circ".

Opaque struct.t.

Lemma fmap_app_split3_inv {A B} (f: A -> B) (l: list A) (l1 l2: list B) (x: B) :
  f <$> l = l1 ++ [x] ++ l2 →
  ∃ l1' x' l2',
    l1 = f <$> l1' ∧
    l2 = f <$> l2' ∧
    x = f x' ∧
    l = l1' ++ [x'] ++ l2'.
Proof.
  intros H.
  apply fmap_app_inv in H as (l1' & l2' & (?&?&?)); subst.
  symmetry in H0.
  apply fmap_app_inv in H0 as (l1'' & l2'' & (?&?&?)); subst.
  symmetry in H.
  destruct l1''; try solve [ inversion H ].
  destruct l1''; try solve [ inversion H ].
  inversion H; subst.
  eexists _, _, _; eauto.
Qed.

Theorem find_highest_index_apply_upds log u i :
  find_highest_index (update.addr <$> log) u.(update.addr) = Some i →
  log !! i = Some u →
  apply_upds log ∅ !! (uint.Z u.(update.addr)) = Some u.(update.b).
Proof.
  intros.
  apply find_highest_index_Some_split in H as (poss1 & poss2 & (Heq & Hnotin & <-)).
  apply fmap_app_split3_inv in Heq as (log1 & u' & log2 & (?&?&?&?)); subst.
  assert (u = u'); [ | subst ].
  { autorewrite with len in H0.
    rewrite -> lookup_app_r in H0 by lia.
    rewrite Nat.sub_diag /= in H0.
    congruence. }
  clear H0 H2.
  destruct u' as [a b]; simpl in *.
  rewrite apply_upds_app /=.
  rewrite apply_upds_insert_commute; auto.
  rewrite lookup_insert //.
Qed.

Lemma apply_upds_not_in_general (a: u64) log d :
    forall (Hnotin: a ∉ update.addr <$> log),
    d !! uint.Z a = None →
    apply_upds log d !! uint.Z a = None.
Proof.
  revert d.
  induction log; simpl; intros; auto.
  destruct a0 as [a' b]; simpl in *.
  fold (update.addr <$> log) in Hnotin.
  apply not_elem_of_cons in Hnotin as [Hneq Hnotin].
  rewrite IHlog; eauto.
  rewrite lookup_insert_ne //.
  apply not_inj; auto.
Qed.

Lemma apply_upds_not_in (a: u64) log :
    a ∉ update.addr <$> log →
    apply_upds log ∅ !! uint.Z a = None.
Proof.
  intros Hnotin.
  apply apply_upds_not_in_general; auto.
Qed.

Theorem wp_WalogState__readMem γ (st: loc) σ (a: u64) diskEnd_txn_id :
  {{{ wal_linv_fields st σ ∗
      memLog_linv γ σ.(memLog) σ.(diskEnd) diskEnd_txn_id }}}
    WalogState__readMem #st #a
  {{{ b_s (ok:bool), RET (slice_val b_s, #ok);
      (if ok then ∃ b, is_block b_s (DfracOwn 1) b ∗
                       ⌜apply_upds σ.(memLog).(slidingM.log) ∅ !! uint.Z a = Some b⌝
      else ⌜b_s = Slice.nil ∧ apply_upds σ.(memLog).(slidingM.log) ∅ !! uint.Z a = None⌝) ∗
      "Hfields" ∷ wal_linv_fields st σ ∗
      "HmemLog_linv" ∷ memLog_linv γ σ.(memLog) σ.(diskEnd) diskEnd_txn_id
  }}}.
Proof.
  iIntros (Φ) "(Hfields&HmemLog_inv) HΦ".
  iNamed "Hfields".
  iNamed "Hfield_ptsto".
  wp_call.
  wp_loadField.
  wp_apply (wp_sliding__posForAddr with "His_memLog").
  iIntros (pos ok) "(His_memLog&%Hlookup)".
  wp_pures.
  wp_if_destruct; subst.
  - destruct Hlookup as [Hbound Hfind].
    wp_apply util_proof.wp_DPrintf.
    wp_loadField.
    (* need to identify the update that we're looking up *)
    pose proof (find_highest_index_ok' _ _ _ Hfind) as [Hlookup Hhighest].
    rewrite list_lookup_fmap in Hlookup.
    apply fmap_Some_1 in Hlookup as [u [ Hlookup ->]].

    wp_apply (wp_sliding__get with "His_memLog"); eauto.
    { lia. }
    iIntros (uv q) "(Hu & His_memLog)".
    iDestruct "Hu" as "(%Hu&Hb)".
    wp_apply (wp_copyUpdateBlock with "Hb").
    iIntros (s') "[Hb Hb']".
    iSpecialize ("His_memLog" with "Hb").
    wp_pures.
    iApply "HΦ".
    iFrame "HmemLog_inv".
    iSplitL "Hb'".
    { iExists _; iFrame.
      iPureIntro.
      eapply find_highest_index_apply_upds; eauto. }
    iExists _; by iFrame.
  - wp_pures.
    change (slice.nil) with (slice_val Slice.nil).
    iApply "HΦ". iModIntro.
    iFrame "HmemLog_inv".
    iSplit.
    { iPureIntro.
      split; auto.
      apply find_highest_index_none_not_in in Hlookup.
      apply apply_upds_not_in; auto. }
    iExists _; by iFrame.
Qed.

Lemma txn_upds_drop : ∀ off txns, ∃ uoff,
  txn_upds (drop off txns) = drop uoff (txn_upds txns).
Proof.
  rewrite /txn_upds.
  induction off; simpl; intros.
  - exists 0%nat. rewrite ?drop_0. done.
  - destruct txns.
    + exists 0%nat. done.
    + simpl. destruct (IHoff txns). rewrite H.
      exists (length (snd p) + x)%nat.
      rewrite drop_app_add'; eauto.
Qed.

Lemma apply_upds_in : ∀ upds a d0 d1,
  a ∈ (update.addr <$> upds) ->
  apply_upds upds d0 !! uint.Z a = apply_upds upds d1 !! uint.Z a.
Proof.
  induction upds; simpl; intros.
  - inversion H.
  - destruct a. simpl in *.
    inversion H; clear H; subst; eauto.
    destruct (decide (addr ∈ update.addr <$> upds)); eauto.
    rewrite ?apply_upds_insert_commute; eauto.
    rewrite ?lookup_insert; done.
Qed.

Lemma apply_upds_drop' : ∀ off upds d (a : u64) b,
  ( ∀ d0, apply_upds (drop off upds) d0 !! uint.Z a = Some b ) ->
  apply_upds upds d !! uint.Z a = Some b.
Proof.
  induction off; simpl; intros.
  - rewrite drop_0 in H. done.
  - destruct upds; simpl in *; eauto.
Qed.

Lemma apply_upds_drop : ∀ off upds d (a : u64) b,
  apply_upds (drop off upds) ∅ !! uint.Z a = Some b ->
  apply_upds upds d !! uint.Z a = Some b.
Proof.
  intros.
  destruct (decide (a ∈ (update.addr <$> drop off upds))).
  2: { eapply apply_upds_not_in in n; congruence. }
  eapply apply_upds_drop'; intros.
  rewrite (apply_upds_in _ _ _ d0) in H; eauto.
Qed.

Lemma apply_upds_drop_txn : ∀ off txns d (a : u64) b,
  apply_upds (txn_upds (drop off txns)) ∅ !! uint.Z a = Some b ->
  apply_upds (txn_upds txns) d !! uint.Z a = Some b.
Proof.
  intros.
  destruct (txn_upds_drop off txns). rewrite H0 in H.
  eapply apply_upds_drop; eauto.
Qed.

Theorem simulate_read_cache_hit {l γ Q σ dinit memLog diskEnd diskEnd_txn_id b a} :
  apply_upds memLog.(slidingM.log) ∅ !! uint.Z a = Some b ->
  (is_wal_inner l γ σ dinit ∗ P σ) -∗
  memLog_linv γ memLog diskEnd diskEnd_txn_id -∗
  (∀ (σ σ' : log_state.t) mb,
      ⌜wal_wf σ⌝
        -∗ ⌜relation.denote (log_read_cache a) σ σ' mb⌝ -∗ P σ -∗ |NC={⊤ ∖ ↑N}=> P σ' ∗ Q mb) -∗
  |NC={⊤ ∖ ↑N}=> (is_wal_inner l γ σ dinit ∗ P σ) ∗
              "HQ" ∷ Q (Some b) ∗
              "HmemLog_linv" ∷ memLog_linv γ memLog diskEnd diskEnd_txn_id.
Proof.
  iIntros (Happly) "[Hinner HP] Hlinv Hfupd".
  iNamed "Hinner".
  iNamed "Hlinv".
  iNamed "Hlinv_pers".
  pose proof (memLog_linv_txns_combined_updates _ _ _ _ _ _ _ _ _ _ Htxns)
    as Hall_updates.
  iDestruct (ghost_var_agree with "Howntxns γtxns") as %->.

  iMod ("Hfupd" $! σ σ with "[] [] HP") as "[HP HQ]"; first by eauto.
  {
    iPureIntro.
    econstructor; simpl.
    { eapply (relation.suchThat_runs _ _ true). eauto. }
    simpl. monad_simpl. simpl.
    rewrite /last_disk /disk_at_txn_id take_ge; last by lia.
    rewrite Hall_updates in Happly.
    erewrite apply_upds_drop_txn; eauto.
    constructor. reflexivity.
  }

  by iFrame "HP HQ Hdisk ∗#%".
Qed.

Lemma apply_upds_in_not_None : ∀ upds a d,
  a ∈ update.addr <$> upds ->
  apply_upds upds d !! uint.Z a ≠ None.
Proof.
  induction upds; simpl; intros.
  { inversion H. }
  destruct a; simpl in *.
  inversion H; clear H; subst; eauto.
  destruct (decide (addr ∈ update.addr <$> upds)); eauto.
  rewrite apply_upds_insert_commute; eauto.
  rewrite lookup_insert; eauto.
Qed.

Lemma apply_upds_no_updates_since memStart (a : u64) installed txns :
  (memStart ≤ installed)%nat ->
  apply_upds (txn_upds (drop memStart txns)) ∅ !! uint.Z a = None ->
  Forall (λ u, u.(update.addr) ≠ a) (txn_upds (drop installed txns)).
Proof.
  intros.
  replace installed with (memStart + (installed-memStart))%nat by lia.
  rewrite -drop_drop.
  generalize dependent (drop memStart txns); intros txns'; intros.
  edestruct txn_upds_drop. erewrite H1.
  generalize dependent (txn_upds txns'); intros upds; intros.
  eapply Forall_drop.
  apply Forall_forall; intros.
  intro; subst.
  eapply apply_upds_in_not_None; eauto.
  set_solver.
Qed.

Theorem simulate_read_cache_miss {l γ Q σ dinit memLog diskEnd diskEnd_txn_id a} :
  apply_upds memLog.(slidingM.log) ∅ !! uint.Z a = None →
  (is_wal_inner l γ σ dinit ∗ P σ) -∗
  memLog_linv γ memLog diskEnd diskEnd_txn_id -∗
  (∀ (σ σ' : log_state.t) mb,
      ⌜wal_wf σ⌝
        -∗ ⌜relation.denote (log_read_cache a) σ σ' mb⌝ -∗ P σ -∗ |NC={⊤ ∖ ↑N}=> P σ' ∗ Q mb) -∗
  |NC={⊤ ∖ ↑N}=> (∃ σ', is_wal_inner l γ σ' dinit ∗ P σ') ∗
              "HQ" ∷ Q None ∗
              "HmemLog_linv" ∷ memLog_linv γ memLog diskEnd diskEnd_txn_id.
Proof.
  iIntros (Happly) "[Hinner HP] Hlinv Hfupd".
  iNamed "Hinner".

  iNamed "Hlinv".
  iNamed "Hlinv_pers".
  pose proof (memLog_linv_txns_combined_updates _ _ _ _ _ _ _ _ _ _ Htxns)
    as Hall_updates.
  iDestruct (ghost_var_agree with "Howntxns γtxns") as %->.

  iNamed "Hdisk".
  iNamed "Hdisk".
  iNamed "circ.end".
  iNamed "circ.start".
  iNamed "Hinstalled".

  iNamed "Howninstalled".
  iDestruct (txn_pos_valid_general with "Htxns_ctx HmemStart_txn") as %HmemStart_txn.
  iDestruct (mono_nat_lb_own_valid with "HownBeingInstalledStartTxn_walinv HinstalledTxn_lb")
    as %[_ HinstalledTxn_lb].

  iAssert (⌜
    start cs = memLog.(slidingM.start) →
    Forall (λ u, u.2 = [])
      (subslice (S installed_txn_id) (S installed_txn_id_mem) σ.(log_state.txns))
  ⌝)%I as %Hnils.
  {
    iIntros (Hstart_eq).
    rewrite -Hstart_eq in HmemStart_txn.
    iNamed "HnextDiskEnd".
    iDestruct (subslice_stable_nils2 _ _ installed_txn_id installed_txn_id_mem _ Hwf with "[HnextDiskEnd_inv HnextDiskEnd_stable]") as %Hnils; eauto.
  }

  iMod ("Hfupd" with "[] [] HP") as "[HP HQ]"; first by eauto.
  {
    iPureIntro.
    econstructor; simpl.
    { eapply (relation.suchThat_runs _ _ false). eauto. }
    simpl. monad_simpl.
    econstructor; simpl.
    { eapply (relation.suchThat_runs _ _ (
      σ.(log_state.durable_lb) `max` installed_txn_id
    )%nat).
      pose proof (is_txn_bound _ _ _ Hend_txn). lia. }
    monad_simpl.
    econstructor; simpl.
    { eapply (relation.suchThat_runs _ _ installed_txn_id).
      simpl. lia. }
    monad_simpl.
    econstructor; simpl.
    { eapply (relation.suchThat_runs _ _ tt).
      simpl.
      rewrite Hall_updates in Happly.
      rewrite /no_updates_since /set /=.

      eapply apply_upds_no_updates_since; last by apply Happly.
      lia.
    }
    monad_simpl.
  }

  iModIntro. iFrame "HQ".
  iSplitR "HnextDiskEnd HownLoggerPos_linv HownLoggerTxn_linv Howntxns
    HownInstallerPosMem_linv HownInstallerTxnMem_linv
    HownInstalledPosMem_linv HownInstalledTxnMem_linv
    HownDiskEndMem_linv HownDiskEndMemTxn_linv".
  { iExists _. iFrame "HP".
    iSplit.
    { rewrite /wal_wf in Hwf. rewrite /wal_wf. iPureIntro. simpl.
      intuition eauto; lia. } simpl.
    iFrame "Hmem Htxns_ctx γtxns HnextDiskEnd_inv Howncs Hdurable #". simpl.
    iSplit. 2: iSplit. 3: iSplit. 4: eauto.
    3: {
      replace ((_ `max` _) `max` _)%nat
        with (σ.(log_state.durable_lb) `max` diskEnd_txn_id0)%nat;
        last by lia.
      iExists diskEnd0.
      iExists (durable_lb_alt `max` installed_txn_id)%nat. iFrame "%". iFrame "#".
      iPureIntro.
      split; first by lia.
      split; first by lia.
      destruct (decide (installed_txn_id ≤ durable_lb_alt)%nat).
      {
        rewrite Nat.max_l; last by lia.
        rewrite Nat.max_l; last by lia.
        assumption.
      }
      rewrite Nat.max_r; last by lia.
      destruct (decide (installed_txn_id ≤ σ.(log_state.durable_lb))%nat).
      2: {
        rewrite Nat.max_r; last by lia.
        rewrite subslice_zero_length.
        apply Forall_nil_2.
      }
      rewrite Nat.max_l; last by lia.
      rewrite -(subslice_app_contig _ (S installed_txn_id))
        in Hdurable_nils; last by lia.
      apply Forall_app in Hdurable_nils.
      intuition.
    }
    2: { iFrame "# %". iPureIntro. lia. }
    iExists _. iFrame. iFrame "%#".
  }

  repeat iExists _. iFrame. iFrame "#". iFrame "%".
Qed.

Theorem wp_Walog__ReadMem (Q: option Block -> iProp Σ) l γ dinit a :
  {{{ is_wal P l γ dinit ∗
       (∀ σₛ σₛ' mb,
         ⌜wal_wf σₛ⌝ -∗
         ⌜relation.denote (log_read_cache a) σₛ σₛ' mb⌝ -∗
         (P σₛ -∗ |NC={⊤ ∖ ↑N}=> P σₛ' ∗ Q mb))
   }}}
    Walog__ReadMem #l #a
  {{{ (ok:bool) bl, RET (slice_val bl, #ok); if ok
                                             then ∃ b, is_block bl (DfracOwn 1) b ∗ Q (Some b)
                                             else Q None}}}.
Proof.
  iIntros (Φ) "[#Hwal Hfupd] HΦ".
  destruct_is_wal.
  wp_loadField.
  wp_apply (acquire_spec with "lk"). iIntros "(Hlocked&Hlkinv)".
  wp_loadField.
  iNamed "Hlkinv".
  wp_apply (wp_WalogState__readMem with "[$Hfields $HmemLog_linv]").
  iIntros (b_s ok) "(Hb&?&?)"; iNamed.
  (* really meant to do wp_pure until wp_bind Skip succeeds *)
  do 8 wp_pure1; wp_bind Skip.
  iDestruct "Hwal" as "[Hwal Hcirc]".
  iInv "Hwal" as (σs) "[Hinner HP]".
  iApply wp_ncfupd.
  wp_call.
  iModIntro.

  wp_pures.
  destruct ok.
  - iDestruct "Hb" as (b) "[Hb %HmemLog_lookup]".
    iMod (ncfupd_mask_subseteq (⊤ ∖ ↑N)) as "HinnerN"; first by solve_ndisj.
    iMod (simulate_read_cache_hit HmemLog_lookup with "[$Hinner $HP] HmemLog_linv Hfupd")
      as "([Hinner HP]&?&?)"; iNamed.
    iMod "HinnerN" as "_".
    iModIntro.
    iSplitL "Hinner HP".
    { iExists _. iFrame. }
    wp_loadField.
    wp_apply (release_spec with "[$lk $Hlocked HmemLog_linv Hfields HdiskEnd_circ Hstart_circ]").
    { iExists _; iFrame. }
    wp_pures.
    iApply "HΦ".
    iExists _; by iFrame.
  - iDestruct "Hb" as "[-> %HmemLog_lookup]".
    iMod (fupd_mask_subseteq (⊤ ∖ ↑N)) as "HinnerN"; first by solve_ndisj.
    iMod (simulate_read_cache_miss HmemLog_lookup with "[$Hinner $HP] HmemLog_linv Hfupd")
      as "(Hinv&?&?)"; iNamed.
    iMod "HinnerN" as "_".
    iModIntro.
    iFrame "Hinv".
    wp_loadField.
    wp_apply (release_spec with "[$lk $Hlocked HmemLog_linv Hfields HdiskEnd_circ Hstart_circ]").
    { iExists _; iFrame. }
    wp_pures.
    iApply "HΦ".
    by iFrame.
Qed.

End goose_lang.
