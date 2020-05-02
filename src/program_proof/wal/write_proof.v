From RecordUpdate Require Import RecordSet.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant.

Section goose_lang.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!walG Σ}.

Implicit Types (v:val) (z:Z).
Implicit Types (γ: wal_names (Σ:=Σ)).
Implicit Types (s: log_state.t) (memLog: list update.t) (txns: list (u64 * list update.t)).
Implicit Types (pos: u64) (txn_id: nat).

Context (P: log_state.t -> iProp Σ).
Let N := walN.
Let circN := walN .@ "circ".

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
      iNamed "Hlockinv".
      iNamed "Hfields".
      iNamed "Hfield_ptsto".
      wp_apply wp_slice_len.
      wp_loadField. wp_loadField.
      wp_apply util_proof.wp_SumOverflows.
      iIntros "%->".
      wp_if_destruct.
      - wp_store.
        iApply "HΦ".
        iExists _, _; iFrame.
        iDestruct "Hsim" as "[_ $]".
        iExists _; iFrame "# ∗".
        iExists _; iFrame "# ∗".
      - rewrite /WalogState__memEnd.
        wp_loadField. wp_loadField. wp_loadField.
        wp_apply wp_slice_len.
        wp_loadField. wp_loadField.
        iDestruct (updates_slice_len with "His_memLog") as %HmemLog_sz.
        wp_apply wp_slice_len.
        wp_pures.
        wp_if_destruct.
        + wp_apply util_proof.wp_DPrintf.
          wp_loadField.
Abort.
