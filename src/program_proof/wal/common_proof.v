From RecordUpdate Require Import RecordSet.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant.

Section goose_lang.
Context `{!heapG Σ}.
Context `{!walG Σ}.

Implicit Types (γ: wal_names).

Context (P: log_state.t -> iProp Σ).

Hint Unfold slidingM.wf : word.
Hint Unfold slidingM.numMutable : word.

Lemma logIndex_set_mutable f σ pos :
  slidingM.logIndex (set slidingM.mutable f σ) pos = slidingM.logIndex σ pos.
Proof.
  rewrite /slidingM.logIndex //=.
Qed.

Theorem wp_endGroupTxn l st γ :
  {{{ is_wal P l γ ∗ wal_linv st γ }}}
    WalogState__endGroupTxn #st
  {{{ RET #(); wal_linv st γ }}}.
Proof.
  iIntros (Φ) "(#Hwal & Hlkinv) HΦ".
  iNamed "Hlkinv".
  iNamed "Hfields".
  iNamed "Hfield_ptsto".
  rewrite -wp_fupd.
  iDestruct (is_sliding_wf with "His_memLog") as %Hsliding_wf.
  wp_call.
  rewrite /WalogState__memEnd.
  wp_loadField. wp_apply (wp_sliding__clearMutable with "His_memLog"); iIntros "His_memLog".

  iApply "HΦ".
  iNamed "HmemLog_linv".
  iDestruct "HmemStart_txn" as "#HmemStart_txn".
  iDestruct "HnextDiskEnd_txn" as "#HnextDiskEnd_txn".
  iDestruct "HmemEnd_txn" as "#HmemEnd_txn".
  iMod (txn_pos_valid_locked with "Hwal HmemEnd_txn Howntxns") as "(%HmemEnd_is_txn & Howntxns)".
  iModIntro.
  iDestruct (is_sliding_wf with "His_memLog") as %Hsliding_wf'.
  iExists (set memLog (λ _,
                       (set slidingM.mutable (λ _ : u64, slidingM.endPos σ.(memLog)) σ.(memLog))) σ).
  simpl.
  iFrame "# ∗".
  iSplitR "Howntxns".
  { iExists _; iFrame.
    iPureIntro.
    split_and!; simpl; auto; try word.
    rewrite /slidingM.endPos.
    unfold locked_wf, slidingM.wf in Hlocked_wf.
    word.
  }
  iExists memStart_txn_id, (length txns - 1)%nat, txns; simpl.
  iFrame "% # ∗".
  destruct_and! His_memLog.
  iPureIntro; split_and!; auto; try lia.
  - pose proof (is_highest_txn_bound HdiskEnd_txn); lia.
  - pose proof (is_txn_bound _ _ _ HmemEnd_is_txn).
    replace (S (length txns - 1)) with (length txns) by lia.
    rewrite !logIndex_set_mutable.
    admit. (* TODO: invariant needs to say mem_log after mutable has appropriate
    updates (before we got this from the has_updates for the entire memLog, but
    now we need to build it from the pieces) *)
Admitted.

End goose_lang.
