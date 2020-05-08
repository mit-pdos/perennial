From RecordUpdate Require Import RecordSet.

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

Definition memEnd (σ: locked_state): Z :=
  int.val σ.(memLog).(slidingM.start) + length σ.(memLog).(slidingM.log).

Hint Unfold memEnd : word.
Hint Unfold slidingM.endPos : word.
Hint Unfold slidingM.wf : word.
Hint Unfold slidingM.numMutable : word.

Theorem wp_WalogState__updatesOverflowU64 st σ (newUpdates: u64) :
  {{{ wal_linv_fields st σ }}}
    WalogState__updatesOverflowU64 #st #newUpdates
  {{{ (overflow:bool), RET #overflow; ⌜overflow = bool_decide (memEnd σ + int.val newUpdates >= 2^64)⌝ ∗
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
  memEnd σ + int.val newUpdates < 2^64 ->
  {{{ wal_linv_fields st σ }}}
    WalogState__memLogHasSpace #st #newUpdates
  {{{ (has_space:bool), RET #has_space; ⌜has_space = bool_decide (memEnd σ - int.val σ.(diskEnd) + int.val newUpdates ≤ LogSz)⌝ ∗
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

Definition memWrite_one memLog (u: update.t) : slidingM.t :=
  match find_highest_index (update.addr <$> memLog.(slidingM.log)) u.(update.addr) with
  | Some i => if decide (int.val memLog.(slidingM.mutable) - int.val memLog.(slidingM.start) ≤ i) then
                set slidingM.log <[i := u]> memLog
              else
                set slidingM.log (λ log, log ++ [u]) memLog
  | None => set slidingM.log (λ log, log ++ [u]) memLog
  end.

(* pure version of memWrite; equivalent to [log ++ upds], except for absorption *)
Definition memWrite memLog (upds: list update.t): slidingM.t :=
  foldl memWrite_one memLog upds.

Theorem wp_if_mutable l memLog (ok: bool) (pos: u64) :
  {{{ is_sliding l memLog }}}
    if: #ok then #pos ≥ struct.loadF sliding.S "mutable" #l else #false
  {{{ RET #(bool_decide (ok = true ∧ int.val memLog.(slidingM.mutable) ≤ int.val pos));
      is_sliding l memLog }}}.
Proof.
  iIntros (Φ) "Hs HΦ".
  wp_if_destruct.
  - iNamed "Hs".
    iNamed "Hinv".
    wp_loadField.
    wp_pures.
    iSpecialize ("HΦ" with "[-]").
    { iFrame "% ∗".
      iExists _, _; iFrame "# ∗". }
    iExactEq "HΦ".
    erewrite bool_decide_iff; eauto.
    intuition auto.
  - simpl.
    iApply ("HΦ" with "[$]").
Qed.

Lemma memWrite_same_mutable memLog upds :
  (memWrite memLog upds).(slidingM.mutable) = memLog.(slidingM.mutable).
Proof.
  revert memLog.
  induction upds; simpl; auto; intros.
  rewrite IHupds.
  rewrite /memWrite_one.
  destruct memLog as [log start mutable]; simpl.
  destruct (find_highest_index (update.addr <$> log) a.(update.addr)); simpl; auto.
  destruct (decide (int.val mutable - int.val start ≤ n)); simpl; auto.
Qed.

Lemma memWrite_same_start memLog upds :
  (memWrite memLog upds).(slidingM.start) = memLog.(slidingM.start).
Proof.
  revert memLog.
  induction upds; simpl; auto; intros.
  rewrite IHupds.
  rewrite /memWrite_one.
  destruct memLog as [log start mutable]; simpl.
  destruct (find_highest_index (update.addr <$> log) a.(update.addr)); simpl; auto.
  destruct (decide (int.val mutable - int.val start ≤ n)); simpl; auto.
Qed.

Lemma memWrite_app1 memLog upds u :
  memWrite memLog (upds ++ [u]) = memWrite_one (memWrite memLog upds) u.
Proof.
  rewrite /memWrite foldl_app //=.
Qed.

Hint Unfold slidingM.logIndex : word.

Theorem wp_memWrite l memLog bufs upds :
  {{{ is_sliding l memLog ∗ updates_slice_frag bufs 1 upds }}}
    wal.memWrite #l (slice_val bufs)
  {{{ RET #(); is_sliding l (memWrite memLog upds) }}}.
Proof.
  iIntros (Φ) "(Hs&Hupds) HΦ".
  wp_call.
  wp_apply (wp_sliding__end with "Hs"); iIntros "Hs".
  wp_apply wp_ref_to; [ val_ty | iIntros (pos_l) "pos" ].
  rewrite /LogPosition.
  wp_apply (wp_forSlicePrefix_updates_consume
              (λ done todo,
               "*" ∷ (∃ (pos_val: u64), "pos" ∷ pos_l ↦[uint64T] #pos_val) ∗
               "Hs" ∷ is_sliding l (memWrite memLog done))%I
           with "[] [$Hupds pos Hs]").
  2: {
    simpl; iFrame.
    iExists _; iFrame.
  }
  { clear Φ.
    iIntros (i uv u done todo).
    iIntros "!>" (Φ) "(Hpre&Hupd&%Hiteration) HΦ". iNamed "Hpre".
    wp_pures.
    iDestruct (is_update_addr with "Hupd") as %Haddr_eq.
    wp_apply (wp_sliding__posForAddr with "[$]").
    iIntros (pos ok) "(Hs&%Hlookup)".
    iDestruct (is_sliding_wf with "Hs") as %Hwf.
    wp_pures.
    wp_apply (wp_if_mutable with "Hs"); iIntros "Hs".
    wp_if_destruct.

    (* absorption *)
    - destruct Heqb as [-> Hpos_large].
      destruct Hlookup as (HposBound&Hlookup).
      wp_apply util_proof.wp_DPrintf.
      wp_apply (wp_sliding__update with "[$Hs $Hupd]"); auto.
      { destruct_and? Hlookup.
        apply find_highest_index_ok' in Hlookup as [Hlookup Hhighest].
        rewrite list_lookup_fmap in Hlookup.
        congruence. }
      iIntros "Hs".
      iApply "HΦ".
      iSplitL "pos".
      { iExists _; iFrame. }
      rewrite memWrite_app1.
      set (memLog':=memWrite memLog done) in *.
      iExactEq "Hs".
      rewrite /named.
      f_equal.
      rewrite /memWrite_one.
      replace u.(update.addr).
      rewrite Hlookup.
      destruct (decide
      (int.val memLog'.(slidingM.mutable) - int.val memLog'.(slidingM.start)
       ≤ slidingM.logIndex memLog' pos)); [ auto | word ].

    (* append *)
    - wp_bind (If _ _ _).
      wp_apply (wp_If_join emp).
      { iSplit.
        - iIntros "[-> Hwp]".
          wp_apply util_proof.wp_DPrintf.
          iApply "Hwp"; auto.
        - iIntros "[-> Hwp]".
          wp_apply util_proof.wp_DPrintf.
          iApply "Hwp"; auto.
      }
      iIntros "_"; wp_pures.
      wp_apply (wp_sliding_append with "[$Hs $Hupd]"); iIntros "Hs".
      wp_pures.
      wp_load.
      wp_store.
      iApply "HΦ".
      iFrame.
      iSplitL "pos".
      { iExists _; iFrame. }
      iExactEq "Hs".
      rewrite /named.
      f_equal.
      rewrite memWrite_app1.
      rewrite /memWrite_one.
      replace (u.(update.addr)).
      destruct_with_eqn (find_highest_index (update.addr <$> (memWrite memLog done).(slidingM.log)) uv.1); auto.
      destruct (decide
                  (int.val (memWrite memLog done).(slidingM.mutable) -
                  int.val (memWrite memLog done).(slidingM.start) ≤ n)); auto.
      exfalso.
      destruct ok; try congruence.
      destruct Hlookup as [? Heq]; inversion Heq; subst.
      contradiction Heqb.
      split; auto.
      word.
  }
  iIntros "HI"; iNamed "HI".
  iApply "HΦ"; iFrame.
Qed.

Theorem wp_Walog__MemAppend (PreQ : iProp Σ) (Q: u64 -> iProp Σ) l γ bufs bs :
  {{{ is_wal P l γ ∗
       updates_slice bufs bs ∗
       (∀ σ σ' pos,
         ⌜wal_wf σ⌝ -∗
         ⌜relation.denote (log_mem_append bs) σ σ' pos⌝ -∗
         (P σ ={⊤ ∖↑ N}=∗ P σ' ∗ Q pos)) ∧ PreQ
   }}}
    Walog__MemAppend #l (slice_val bufs)
  {{{ pos (ok : bool), RET (#pos, #ok); if ok then Q pos else PreQ }}}.
Proof.
  iIntros (Φ) "(#Hwal & Hbufs & Hfupd) HΦ".
  wp_call.
  iDestruct (updates_slice_len with "Hbufs") as %Hbufs_sz.
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
                     "Hsim" ∷ (if b then
                       ((∀ (σ σ' : log_state.t) pos,
                           ⌜wal_wf σ⌝
                            -∗ ⌜relation.denote (log_mem_append bs) σ σ' pos⌝
                            -∗ P σ ={⊤ ∖ ↑N}=∗ P σ' ∗ Q pos) ∧ PreQ)
                     else (if ok then Q txn else PreQ)) ∗
                     "Hlocked" ∷ locked γ.(lock_name) ∗
                     "Hlockinv" ∷ wal_linv σₛ.(wal_st) γ
                )%I
                with  "[] [-HΦ]"
             ).
    2: { iExists _, _; iFrame. }
    { clear Φ.
      iIntros "!>" (Φ) "HI HΦ". iNamed "HI".
      wp_pures.
      wp_apply wp_slice_len.
      iNamed "Hlockinv".
      wp_apply (wp_WalogState__updatesOverflowU64 with "Hfields").
      iIntros (?) "[-> Hfields]".
      wp_pures.
      wp_if_destruct.
      - wp_store.
        wp_pures.
        iApply "HΦ".
        iExists _, _; iFrame.
        iDestruct "Hsim" as "[_ $]".
        iExists _; iFrame "# ∗".
      - wp_apply wp_slice_len.
        wp_apply (wp_WalogState__memLogHasSpace with "Hfields").
        { revert Heqb0; word. }
        iIntros (?) "[-> Hfields]".
        wp_if_destruct.
        + admit.
        + wp_apply util_proof.wp_DPrintf.
          admit.
Admitted.

End goose_lang.
