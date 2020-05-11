From RecordUpdate Require Import RecordSet.

From Tactical Require Import SimplMatch.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant.

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
                               (if ok then Q txn else PreQ)) ∗
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
        set (memLog' := memWrite σ.(memLog) bs).
        assert (slidingM.wf memLog').
        { subst memLog'.
          apply memWrite_wf; [ word | ].
          destruct Hlocked_wf; auto. }
        iNamed 1.
        iDestruct "Hwal" as "[Hwal Hcirc]".
        rewrite -wp_fupd.
        wp_store.
        wp_bind Skip.
        iInv "Hwal" as (σ') "[Hinner HP]".
        wp_call.
        iDestruct (is_wal_wf with "Hinner") as %Hwal_wf.
        iDestruct "Hsim" as "[Hsim _]".
        iNamed "HmemLog_linv".
        iNamed "Hinner".
        (* XXX: unify_ghost doesn't rewrite everywhere *)
        iDestruct (ghost_var_agree with "γtxns Howntxns") as %Htxnseq; subst.
        iMod ("Hsim" $! _ (set log_state.txns (λ txns, txns ++ [(slidingM.endPos memLog', bs)]) σ') with "[% //] [%] [$HP]") as "[HP HQ]".
        { simpl; monad_simpl.
          eexists _ (slidingM.endPos memLog'); simpl; monad_simpl.
          econstructor; eauto.
          destruct Hlocked_wf.
          rewrite slidingM.memEnd_ok; eauto.
          eapply is_mem_memLog_endpos_highest; eauto. }
        (* TODO: now need to update at least the two copies of txns in ghost
        state, if not other ghost variables *)
        iMod (ghost_var_update _ (σ'.(log_state.txns) ++ [(slidingM.endPos memLog', bs)]) with "γtxns Howntxns")
          as "[γtxns Howntxns]".
        iMod (alloc_txn_pos (slidingM.endPos memLog') bs with "Htxns_ctx") as "[Htxns_ctx #Hnew_txn]".
        iDestruct (txn_val_to_pos with "Hnew_txn") as "Hnew_txn_pos".
        iSpecialize ("HQ" with "Hnew_txn_pos").
        iModIntro.
        iSplitL "Hdisk Hmem HP γtxns Htxns_ctx".
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
          admit. (* Hdisk is preserved by extension (can factor this out easily if the whole clause gets a definition) *)
        }
        wp_pures.
        iModIntro.
        iApply "HΦ".
        iExists _, _; iFrame.
        rewrite (right_id _ bi_sep).
        iFrame "HQ".
        iExists (set memLog (λ _, memLog') σ); simpl.
        rewrite memWrite_same_start.
        iFrame.
        iSplitR "HmemStart_txn HnextDiskEnd_txn Howntxns".
        { iExists _; iFrame.
          iPureIntro.
          eapply locked_wf_memWrite; eauto. }
        iExists memStart_txn_id, nextDiskEnd_txn_id, _; iFrame.
        rewrite memWrite_same_start memWrite_same_mutable; iFrame.
        (* TODO: should have used HmemStart_txn and HnextDiskEnd_txn to get is_pos
        facts, when we had a txn ctx *)
        admit. (* some proofs that lock invariant is stable under appending transactions *)
      - wp_apply util_proof.wp_DPrintf.
        admit.
Admitted.

End goose_lang.
