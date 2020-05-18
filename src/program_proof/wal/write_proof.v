From RecordUpdate Require Import RecordSet.

From Tactical Require Import SimplMatch.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant wal.common_proof.

Section goose_lang.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!walG Σ}.

Implicit Types (v:val) (z:Z).
Implicit Types (γ: wal_names (Σ:=Σ)).
Implicit Types (s: log_state.t) (memLog: slidingM.t) (txns: list (u64 * list update.t)).
Implicit Types (pos: u64) (txn_id: nat).

Context (P: log_state.t -> iProp Σ).
Let N := walN.
Let innerN := walN .@ "wal".
Let circN := walN .@ "circ".

Hint Unfold slidingM.memEnd : word.
Hint Unfold slidingM.endPos : word.
Hint Unfold slidingM.wf : word.
Hint Unfold slidingM.numMutable : word.

Theorem wp_WalogState__updatesOverflowU64 st σ (newUpdates: u64) :
  {{{ wal_linv_fields st σ }}}
    WalogState__updatesOverflowU64 #st #newUpdates
  {{{ (overflow:bool), RET #overflow; ⌜overflow = bool_decide (slidingM.memEnd σ.(memLog) + int.val newUpdates >= 2^64)⌝ ∗
                                      wal_linv_fields st σ
  }}}.
Proof.
  iIntros (Φ) "Hfields HΦ".
  iNamed "Hfields".
  iNamed "Hfield_ptsto".
  (* iDestruct (updates_slice_len with "His_memLog") as %HmemLog_sz. *)
  wp_call.
  rewrite /WalogState__memEnd.
  wp_loadField. wp_apply (wp_sliding__end with "His_memLog"); iIntros "His_memLog".
  wp_apply util_proof.wp_SumOverflows.
  iIntros (?) "->".
  iApply "HΦ".
  iSplit.
  { iPureIntro.
    apply bool_decide_iff.
    word. }
  iFrame.
  iExists _; by iFrame "# ∗".
Qed.

Theorem wp_WalogState__memLogHasSpace st σ (newUpdates: u64) :
  slidingM.memEnd σ.(memLog) + int.val newUpdates < 2^64 ->
  {{{ wal_linv_fields st σ }}}
    WalogState__memLogHasSpace #st #newUpdates
  {{{ (has_space:bool), RET #has_space; ⌜has_space = bool_decide (slidingM.memEnd σ.(memLog) - int.val σ.(diskEnd) + int.val newUpdates ≤ LogSz)⌝ ∗
                                        wal_linv_fields st σ
  }}}.
Proof.
  iIntros (Hnon_overflow Φ) "Hfields HΦ".
  iNamed "Hfields".
  iNamed "Hfield_ptsto".
  (* iDestruct (updates_slice_len with "His_memLog") as %HmemLog_sz. *)
  wp_call.
  rewrite /WalogState__memEnd.
  wp_loadField. wp_apply (wp_sliding__end with "His_memLog"); iIntros "His_memLog".
  wp_loadField.
  wp_pures.
  change (int.val $ word.divu (word.sub 4096 8) 8) with LogSz.
  iAssert (wal_linv_fields st σ) with "[-HΦ]" as "Hfields".
  { iFrame.
    iExists _; by iFrame "# ∗". }
  wp_if_destruct; iApply "HΦ"; iFrame; iPureIntro.
  - symmetry; apply bool_decide_eq_false.
    revert Heqb; repeat word_cleanup.
  - symmetry; apply bool_decide_eq_true.
    revert Heqb; repeat word_cleanup.
Qed.

(* TODO: this intermediate function still provides no value, since it has
essentially the same spec as sliding.memWrite *)
Theorem wp_WalogState__doMemAppend l memLog bufs upds :
  {{{ "His_memLog" ∷ is_sliding l memLog ∗
      "Hupds" ∷ updates_slice_frag bufs 1 upds
  }}}
    doMemAppend #l (slice_val bufs)
  {{{ RET #(slidingM.endPos (memWrite memLog upds));
      "His_memLog" ∷ is_sliding l (memWrite memLog upds) }}}.
Proof.
Admitted.

Lemma is_wal_wf l γ σ :
  is_wal_inner l γ σ -∗ ⌜wal_wf σ⌝.
Proof.
  by iNamed 1.
Qed.

Lemma length_singleton {A} (x: A) :
  length [x] = 1%nat.
Proof. reflexivity. Qed.

Hint Rewrite @length_singleton : len.

Lemma memWrite_one_length_bound σ u :
  length σ.(slidingM.log) ≤
  length (memWrite_one σ u).(slidingM.log) ≤
  S (length σ.(slidingM.log)).
Proof.
  rewrite /memWrite_one.
  destruct matches; simpl; len.
Qed.

Lemma memWrite_length_bound σ upds :
  length σ.(slidingM.log) ≤
  length (memWrite σ upds).(slidingM.log) ≤
  length σ.(slidingM.log) + length upds.
Proof.
  revert σ.
  induction upds; simpl; len; intros.
  pose proof (IHupds (memWrite_one σ a)).
  pose proof (memWrite_one_length_bound σ a).
  lia.
Qed.

Lemma memWrite_memEnd_bound σ upds :
  slidingM.memEnd σ ≤
  slidingM.memEnd (memWrite σ upds) ≤
  slidingM.memEnd σ + length upds.
Proof.
  pose proof (memWrite_length_bound σ upds).
  rewrite /slidingM.memEnd.
  rewrite memWrite_same_start.
  lia.
Qed.

Lemma is_mem_memLog_endpos_highest σ txns start_txn_id upds :
  is_mem_memLog σ txns start_txn_id ->
  (forall pos txn_id, is_txn txns txn_id pos -> int.val pos ≤ slidingM.memEnd (memWrite σ upds)).
Proof.
  pose proof (memWrite_length_bound σ upds) as Hσ'len.
  destruct 1 as [Hupds Hhighest].
  rewrite /is_txn; intros.
  rewrite -list_lookup_fmap in H.
  apply (Forall_lookup_1 _ _ _ _ Hhighest) in H; eauto.
  rewrite /slidingM.memEnd in H |- *.
  rewrite memWrite_same_start.
  lia.
Qed.

Theorem memWrite_one_wf σ u :
  int.val σ.(slidingM.start) + S (length σ.(slidingM.log)) < 2^64 ->
  slidingM.wf σ ->
  slidingM.wf (memWrite_one σ u).
Proof.
  rewrite /slidingM.wf.
  intros.
  pose proof (memWrite_one_length_bound σ u).
  destruct_and!; split_and!;
              rewrite ?memWrite_one_same_mutable ?memWrite_one_same_start;
    auto; lia.
Qed.

Theorem memWrite_wf σ upds :
  int.val σ.(slidingM.start) + length σ.(slidingM.log) + length upds < 2^64 ->
  slidingM.wf σ ->
  slidingM.wf (memWrite σ upds).
Proof.
  rewrite /slidingM.wf.
  intros.
  pose proof (memWrite_length_bound σ upds).
  destruct_and!; split_and!;
              rewrite ?memWrite_same_mutable ?memWrite_same_start;
    auto; lia.
Qed.

Lemma set_txns_d f σ :
  (set log_state.txns f σ).(log_state.d) = σ.(log_state.d).
Proof. auto. Qed.

Lemma set_txns_installed_lb f σ :
  (set log_state.txns f σ).(log_state.installed_lb) = σ.(log_state.installed_lb).
Proof. auto. Qed.

Lemma set_txns_durable_lb f σ :
  (set log_state.txns f σ).(log_state.durable_lb) = σ.(log_state.durable_lb).
Proof. auto. Qed.

Lemma locked_wf_memWrite σ upds :
  slidingM.wf (memWrite σ.(memLog) upds) ->
  locked_wf σ ->
  locked_wf (set memLog (λ _, memWrite σ.(memLog) upds) σ).
Proof.
  rewrite /locked_wf; intros.
  rewrite !memWrite_same_mutable !memWrite_same_start.
  destruct_and!; split_and!; auto.
Qed.

Lemma is_mem_memLog_append (bs : list update.t) (σ : locked_state) (σs : log_state.t) (memStart_txn_id : nat) :
    slidingM.wf (memWrite σ.(memLog) bs) →
    (memStart_txn_id ≤ length σs.(log_state.txns))%nat →
    is_mem_memLog σ.(memLog) σs.(log_state.txns) memStart_txn_id →
    is_mem_memLog (memWrite σ.(memLog) bs)
                    (σs.(log_state.txns) ++ [(slidingM.endPos (memWrite σ.(memLog) bs), bs)])
                    memStart_txn_id.
Proof.
  intros Hwf HmemStart_bound.
  rewrite /is_mem_memLog /has_updates.
  intros [Hupdates Hpos_bound].
  split.
  - intros.
    rewrite -> drop_app_le by auto.
    rewrite txn_upds_app.
    rewrite memWrite_apply_upds.
    rewrite !apply_upds_app.
    simpl.
    rewrite Hupdates //.
  - rewrite fmap_app.
    apply Forall_app; split.
    + eapply Forall_impl; eauto.
      simpl; intros.
      pose proof (memWrite_memEnd_bound σ.(memLog) bs).
      word.
    + apply Forall_singleton.
      rewrite slidingM.memEnd_ok; auto.
      lia.
Qed.

Hint Rewrite memWrite_one_same_start memWrite_one_same_mutable : sliding.
Hint Rewrite memWrite_same_start memWrite_same_mutable : sliding.

Ltac sliding := autorewrite with sliding; try done.

Definition numMutableN (memLog: slidingM.t): nat :=
  (int.nat memLog.(slidingM.mutable) - int.nat memLog.(slidingM.start))%nat.

Theorem memWrite_one_same_numMutableN memLog u :
  numMutableN (memWrite_one memLog u) = numMutableN memLog.
Proof.
  rewrite /numMutableN; sliding.
Qed.

Theorem memWrite_same_numMutableN memLog upds :
  numMutableN (memWrite memLog upds) = numMutableN memLog.
Proof.
  rewrite /numMutableN; sliding.
Qed.

Lemma memWrite_one_preserves_mutable memLog u :
  slidingM.wf memLog →
  take (numMutableN (memWrite_one memLog u)) (memWrite_one memLog u).(slidingM.log) =
  take (numMutableN memLog) memLog.(slidingM.log).
Proof.
  intros Hwf.
  rewrite /memWrite_one /numMutableN.
  destruct matches; simpl.
  - rewrite -> take_insert by lia; auto.
  - rewrite -> take_app_le by word; auto.
  - rewrite -> take_app_le by word; auto.
Qed.

Lemma memWrite_preserves_mutable' memLog upds :
  slidingM.wf memLog ->
  int.val memLog.(slidingM.start) + length memLog.(slidingM.log) + length upds < 2^64 ->
  take
    (numMutableN (memWrite memLog upds))
    (memWrite memLog upds).(slidingM.log) =
  take
    (numMutableN memLog)
    memLog.(slidingM.log).
Proof.
  intros Hwf Hoverflow.
  generalize dependent memLog.
  induction upds; simpl; auto; intros.
  rewrite IHupds; sliding.
  - rewrite memWrite_one_preserves_mutable; auto.
  - eapply memWrite_one_wf; eauto; try lia.
  - pose proof (memWrite_one_length_bound memLog a); lia.
Qed.

Lemma memWrite_preserves_mutable memLog upds :
  slidingM.wf memLog ->
  int.val memLog.(slidingM.start) + length memLog.(slidingM.log) + length upds < 2^64 ->
  take
    (numMutableN memLog)
    (memWrite memLog upds).(slidingM.log) =
  take
    (numMutableN memLog)
    memLog.(slidingM.log).
Proof.
  intros Hwf Hoverflow.
  pose proof (memWrite_preserves_mutable' memLog upds) as Hwf'.
  rewrite memWrite_same_numMutableN in Hwf'; eauto.
Qed.

Lemma memWrite_preserves_mutable_suffix memLog upds diskEnd :
  slidingM.wf memLog ->
  int.val memLog.(slidingM.start) + length memLog.(slidingM.log) + length upds < 2^64 ->
  subslice (slidingM.logIndex memLog diskEnd)
           (slidingM.logIndex memLog memLog.(slidingM.mutable))
           (memWrite memLog upds).(slidingM.log) =
  subslice (slidingM.logIndex memLog diskEnd)
           (slidingM.logIndex memLog memLog.(slidingM.mutable))
           memLog.(slidingM.log).
Proof.
  intros Hwf Hoverflow.
  rewrite /subslice.
  rewrite memWrite_preserves_mutable; auto.
Qed.

Lemma numMutableN_ok memLog :
  slidingM.wf memLog ->
  int.nat (slidingM.numMutable memLog) = numMutableN memLog.
Proof.
  rewrite /numMutableN; intros; word.
Qed.

Lemma is_installed_append γ d txns txns' txn_id diskEnd_txn_id :
  is_installed γ d txns txn_id diskEnd_txn_id -∗
  is_installed γ d (txns ++ txns') txn_id diskEnd_txn_id.
Proof.
  rewrite /is_installed.
  iNamed 1.
  iExists new_installed_txn_id, being_installed.
  iFrame.
  iSplitR "Hdata".
  - iPureIntro.
    len.
  - iApply (big_sepM_mono with "Hdata"); simpl.
    intros.
    rewrite take_app_le; auto.
    destruct matches; lia.
Qed.

Lemma is_durable_append γ cs txns txns' installed_txn_id diskEnd_txn_id :
  (diskEnd_txn_id < length txns)%nat ->
  is_durable γ cs txns installed_txn_id diskEnd_txn_id -∗
  is_durable γ cs (txns ++ txns') installed_txn_id diskEnd_txn_id.
Proof.
  intros Hbound.
  rewrite /is_durable; iNamed 1.
  iPureIntro.
  rewrite /circ_matches_txns in Hcirc_matches |- *.
  rewrite -> subslice_app_1 by lia; auto.
Qed.

Theorem disk_inv_append γ σs cs pos upds :
  disk_inv γ σs cs -∗
  disk_inv γ (set log_state.txns (λ txns, txns ++ [(pos, upds)]) σs) cs.
Proof.
  rewrite /disk_inv; iNamed 1; simpl.
  iExists installed_txn_id, diskEnd_txn_id; iFrame.
  iNamed "circ.start".
  iNamed "circ.end".
  iSplitL "Hinstalled"; [ | iSplitL "Hdurable"; [ | iSplit; iPureIntro ] ].
  - iApply (is_installed_append with "[$]").
  - iApply (is_durable_append with "[$]").
    eapply is_highest_txn_bound; eauto.
  - split; try lia.
    (* TODO: oops, this is pretty tricky; we're promising to maintain the
    highest txn_id for diskEnd and installEnd in the invariant. After an append,
    can these change?

    I believe they can, at least because of empty transactions. This special
    case is definitely fine, since then we can just increase diskEnd_txn_id and
    logically incorporate the new transaction, but we need to know that it
    really is empty. Absorption is more complicated. We can't absorb into the
    durable transactions, but I'm not sure where the strict inequality comes
    from that makes that true. *)
    admit.
  - simpl.
    eexists; intuition eauto.
    admit. (* same issue *)
Admitted.

Lemma memWrite_preserves_logIndex σ upds pos :
  slidingM.logIndex (memWrite σ upds) pos =
  slidingM.logIndex σ pos.
Proof.
  rewrite /slidingM.logIndex.
  rewrite memWrite_same_start //.
Qed.

Theorem wp_Walog__MemAppend (PreQ : iProp Σ) (Q: u64 -> iProp Σ) l γ bufs bs :
  {{{ is_wal P l γ ∗
       updates_slice bufs bs ∗
       (∀ σ σ' pos,
         ⌜wal_wf σ⌝ -∗
         ⌜relation.denote (log_mem_append bs) σ σ' pos⌝ -∗
         let txn_id := length σ.(log_state.txns) in
         (P σ ={⊤ ∖↑ N}=∗ P σ' ∗ (txn_pos γ txn_id pos -∗ Q pos))) ∧ PreQ
   }}}
    Walog__MemAppend #l (slice_val bufs)
  {{{ pos (ok : bool), RET (#pos, #ok); if ok then Q pos ∗ ∃ txn_id, txn_pos γ txn_id pos else PreQ }}}.
Proof.
  iIntros (Φ) "(#Hwal & Hbufs & Hfupd) HΦ".
  wp_call.
  iDestruct (updates_slice_to_frag with "Hbufs") as "Hbufs".
  iDestruct (updates_slice_frag_len with "Hbufs") as %Hbufs_sz.
  wp_apply wp_slice_len.
  wp_pures.
  change (int.val (word.divu (word.sub 4096 8) 8)) with LogSz.
  wp_if_destruct.
  - wp_pures.
    iApply "HΦ".
    iDestruct "Hfupd" as "[_ $]".
  - wp_apply wp_ref_to; [ by val_ty | iIntros (txn_l) "txn" ].
    wp_apply wp_ref_to; [ by val_ty | iIntros (ok_l) "ok" ].
    iMod (is_wal_read_mem with "Hwal") as "#Hmem".
    wp_pures.
    iNamed "Hmem".
    iNamed "Hstfields".
    wp_loadField.
    wp_apply (acquire_spec with "lk"); iIntros "(Hlocked&Hlockinv)".
    wp_loadField.
    wp_pures.
    wp_bind (For _ _ _).
    wp_apply (wp_forBreak_cond
                (fun b =>
                   ∃ (txn: u64) (ok: bool),
                     "txn" ∷ txn_l ↦[uint64T] #txn ∗
                     "ok" ∷ ok_l ↦[boolT] #ok ∗
                     "%Hok_is" ∷ ⌜if b then ok = true else True⌝ ∗
                    "Hsim" ∷ (if b then
                               (∀ (σ σ' : log_state.t) pos,
                                ⌜wal_wf σ⌝
                                -∗ ⌜relation.denote (log_mem_append bs) σ σ' pos⌝
                                -∗ P σ
                                ={⊤ ∖ ↑N}=∗ P σ'
                                ∗ (txn_pos γ (length σ.(log_state.txns)) pos
                                -∗ Q pos)) ∧ PreQ else
                               (if ok then Q txn ∗ ∃ txn_id, txn_pos γ txn_id txn else PreQ)) ∗
                     "Hlocked" ∷ locked γ.(lock_name) ∗
                     "Hlockinv" ∷ wal_linv σₛ.(wal_st) γ ∗
                     "Hbufs" ∷ if b then updates_slice_frag bufs 1 bs else emp
                )%I
                with  "[] [-HΦ]"
             ).
    2: { iExists _, _; iFrame. auto. }
    { clear Φ.
      iIntros "!>" (Φ) "HI HΦ". iNamed "HI".
      wp_pures.
      intuition subst.
      (* hide postcondition from the IPM goal *)
      match goal with
      | |- context[Esnoc _ (INamed "HΦ") ?P] =>
        set (post:=P)
      end.
      wp_apply wp_slice_len.
      iNamed "Hlockinv".
      wp_apply (wp_WalogState__updatesOverflowU64 with "Hfields").
      iIntros (?) "[-> Hfields]".
      wp_pures.
      wp_if_destruct.
      { (* error path *)
        wp_store.
        wp_pures.
        iApply "HΦ".
        iExists _, _; iFrame.
        rewrite right_id.
        iDestruct "Hsim" as "[_ $]".
        iExists _; iFrame "# ∗". }
      wp_apply wp_slice_len.
      wp_apply (wp_WalogState__memLogHasSpace with "Hfields").
      { revert Heqb0; word. }
      iIntros (?) "[-> Hfields]".
      wp_if_destruct.
      - iNamed "Hfields". iNamed "Hfield_ptsto".
        wp_loadField.
        wp_apply (wp_WalogState__doMemAppend with "[$His_memLog $Hbufs]").
        assert (slidingM.wf σ.(memLog)).
        { destruct Hlocked_wf; auto. }
        set (memLog' := memWrite σ.(memLog) bs).
        assert (slidingM.wf memLog').
        { subst memLog'.
          apply memWrite_wf; [ word | auto ]. }
        iNamed 1.
        iDestruct "Hwal" as "[Hwal Hcirc]".
        rewrite -wp_fupd.
        wp_store.
        wp_bind Skip.
        iInv "Hwal" as (σs) "[Hinner HP]".
        wp_call.
        iDestruct (is_wal_wf with "Hinner") as %Hwal_wf.
        iDestruct "Hsim" as "[Hsim _]".
        iNamed "HmemLog_linv".
        iDestruct "HmemStart_txn" as "#HmemStart_txn".
        iDestruct "HnextDiskEnd_txn" as "#HnextDiskEnd_txn".
        iNamed "Hinner".
        (* XXX: unify_ghost doesn't rewrite everywhere *)
        iDestruct (ghost_var_agree with "γtxns Howntxns") as %Htxnseq; subst.
        iMod (txn_pos_valid with "Htxns_ctx HmemStart_txn") as (HmemStart_txn) "Htxns_ctx"; first by solve_ndisj.
        iMod (txn_pos_valid with "Htxns_ctx HnextDiskEnd_txn") as (HnextDiskEnd_txn) "Htxns_ctx"; first by solve_ndisj.
        iMod (fupd_intro_mask' _ (⊤ ∖ ↑N)) as "HinnerN"; first by solve_ndisj.
        iMod ("Hsim" $! _ (set log_state.txns (λ txns, txns ++ [(slidingM.endPos memLog', bs)]) σs)
                with "[% //] [%] [$HP]") as "[HP HQ]".
        { simpl; monad_simpl.
          eexists _ (slidingM.endPos memLog'); simpl; monad_simpl.
          econstructor; eauto.
          destruct Hlocked_wf.
          rewrite slidingM.memEnd_ok; eauto.
          eapply is_mem_memLog_endpos_highest; eauto. }
        iMod "HinnerN" as "_".
        iMod (ghost_var_update _ (σs.(log_state.txns) ++ [(slidingM.endPos memLog', bs)])
                with "γtxns Howntxns") as "[γtxns Howntxns]".
        iMod (alloc_txn_pos (slidingM.endPos memLog') bs with "Htxns_ctx") as "[Htxns_ctx #Hnew_txn]".
        iDestruct (txn_val_to_pos with "Hnew_txn") as "Hnew_txn_pos".
        iSpecialize ("HQ" with "Hnew_txn_pos").
        iModIntro.
        iSplitL "Hdisk Hmem HP γtxns Htxns_ctx".

        (* re-prove invariant *)
        {
          iNext.
          iExists _; iFrame "HP".
          iFrame.
          iSplit; [ iPureIntro | ].
          { eapply mem_append_preserves_wf; eauto.
            - admit. (* new writes should be in-bounds *)
            - rewrite slidingM.memEnd_ok; eauto.
              eapply is_mem_memLog_endpos_highest; eauto. }
          simpl.
          iDestruct "Hdisk" as (cs) "Hdisk".
          iNamed "Hdisk".
          iExists cs; iFrame.
          iApply (disk_inv_append with "Hdisk").
        }

        (* continue and prove loop invariant (lock invariant mostly) *)
        wp_pures.
        iModIntro.
        iApply "HΦ".
        iExists _, _; iFrame.
        rewrite (right_id _ bi_sep).
        iFrame "HQ".
        iSplit.
        { iExists _; iFrame "#". }
        iExists (set memLog (λ _, memLog') σ); simpl.
        rewrite memWrite_same_start.
        iFrame.
        iSplitR "HmemStart_txn HnextDiskEnd_txn Howntxns".
        { iExists _; iFrame.
          iPureIntro.
          eapply locked_wf_memWrite; eauto. }
        iExists memStart_txn_id, diskEnd_txn_id, nextDiskEnd_txn_id, _; iFrame.
        rewrite memWrite_same_start memWrite_same_mutable; iFrame "#".
        autorewrite with len.
        iFrame "%".
        iSplit.
        { iPureIntro.
          admit. (* TODO: need to somehow separate diskEnd from endPos (probably
          even after aborption for non-empty writes, must advance by at least
          one block) *)
        }
        iSplit.
        { autorewrite with len.
          rewrite Nat.add_sub.
          iFrame "#". }
        { iSplit; iPureIntro.
          - eapply is_mem_memLog_append; eauto.
            pose proof (is_txn_bound _ _ _ HmemStart_txn); lia.
          - pose proof (is_txn_bound _ _ _ HnextDiskEnd_txn).
            rewrite -> subslice_app_1 by lia.
            rewrite !memWrite_preserves_logIndex.
            rewrite memWrite_preserves_mutable_suffix; auto.
            word. }
      - wp_apply util_proof.wp_DPrintf.
        iAssert (wal_linv σₛ.(wal_st) γ) with "[Hfields HmemLog_linv HdiskEnd_circ Hstart_circ]" as "Hlockinv".
        { iExists _; iFrame. }
        wp_apply (wp_endGroupTxn with "[$Hwal $Hlockinv]").
        iIntros "Hlockinv".
        wp_loadField.
        wp_apply (wp_condBroadcast with "[$cond_logger]").
        wp_loadField.
        wp_apply (wp_condWait with "[$cond_logger $Hlocked $lk $Hlockinv]").
        iIntros "(Hlocked&Hlockinv)".
        wp_pures.
        iApply "HΦ".
        iExists _, _; by iFrame. }
    iNamed 1.
    wp_loadField.
    wp_apply (release_spec with "[$lk $Hlocked $Hlockinv]").
    wp_pures.
    wp_load. wp_load.
    wp_pures.
    iApply "HΦ".
    destruct ok; iFrame.
Admitted.

End goose_lang.
