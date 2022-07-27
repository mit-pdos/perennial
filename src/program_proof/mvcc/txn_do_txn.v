From Perennial.program_proof.mvcc Require Import mvcc_inv txn_common txn_begin txn_commit.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition txnmap_ptstos τ (m : dbmap) : iProp Σ :=
  [∗ map] k ↦ v ∈ m, txnmap_ptsto τ k v.

Definition dbmap_ptstos γ (m : dbmap) : iProp Σ :=
  [∗ map] k ↦ v ∈ m, dbmap_ptsto γ k v.

Definition spec_body (body : val) (txn :loc) r P Q τ : iProp Σ :=
  {{{ ⌜P r⌝ ∗ txnmap_ptstos τ r }}}
    body #txn
  {{{ w (ok : bool), RET #ok; if ok then ⌜Q r w⌝ ∗ txnmap_ptstos τ w else True }}}.

Theorem wp_txn__DoTxn txn (body : val) P Q γ :
  (∀ r w, (Decision (Q r w))) ->
  ⊢ {{{ own_txn_uninit txn γ ∗ (∀ r τ, spec_body body txn r P Q τ) }}}
    <<< ∀∀ (r : dbmap), ⌜P r⌝ ∗ dbmap_ptstos γ r >>>
      Txn__DoTxn #txn body @ ↑mvccNSST
    <<< ∃∃ (ok : bool), if ok then (∃ w, ⌜Q r w⌝ ∗ dbmap_ptstos γ w) else dbmap_ptstos γ r >>>
    {{{ (v : u64), RET #ok; own_txn_uninit txn γ }}}.
Proof.
  iIntros (Hdec) "!>".
  iIntros (Φ) "[Htxn Hbody] HAU".
  wp_call.

  (***********************************************************)
  (* txn.Begin()                                             *)
  (* cmt := body(txn)                                        *)
  (* if !cmt {                                               *)
  (*     txn.Abort()                                         *)
  (*     return false                                        *)
  (* }                                                       *)
  (* txn.Commit()                                            *)
  (* return true                                             *)
  (***********************************************************)
  wp_apply (wp_txn__Begin with "Htxn").
  iIntros "[%τ Htxn]".
  wp_pures.
  wp_apply ("Hbody").
  { (* TODO: Prove precondition. *) admit. }
  iIntros (w ok) "H".
  wp_pures.
  wp_if_destruct.
  { (* Abort branch. *) admit. }
  wp_apply (wp_txn__Commit with "Htxn").
  iIntros (ok) "Htxn".
  wp_pures.
Admitted.


Definition pre_Swap (r : dbmap) : Prop.
Admitted.
Definition post_Swap (r w : dbmap) : Prop.
Admitted.

Theorem wp_SwapSeq txn r τ :
  {{{ ⌜pre_Swap r⌝ ∗ txnmap_ptstos τ r }}}
    SwapSeq #txn
  {{{ w (ok : bool), RET #ok; if ok then ⌜post_Swap r w⌝ ∗ txnmap_ptstos τ w else True }}}.
Admitted.

Instance post_Swap_dec : (∀ r w, (Decision (post_Swap r w))).
Admitted.

Theorem wp_Swap (txn : loc) γ :
  ⊢ {{{ own_txn_uninit txn γ }}}
    <<< ∀∀ (r : dbmap), ⌜pre_Swap r⌝ ∗ dbmap_ptstos γ r >>>
      Swap #txn @ ↑mvccNSST
    <<< ∃∃ (ok : bool), if ok then (∃ w, ⌜post_Swap r w⌝ ∗ dbmap_ptstos γ w) else dbmap_ptstos γ r >>>
    {{{ (v : u64), RET #ok; own_txn_uninit txn γ }}}.
Proof.
  iIntros "!>".
  iIntros (Φ) "Htxn HAU".
  wp_call.
  wp_apply (wp_txn__DoTxn _ _ _ post_Swap with "[$Htxn]").
  { unfold spec_body.
    iIntros (r τ Φ') "!> Hpre HΦ'".
    iApply (wp_SwapSeq with "Hpre HΦ'").
  }
  done.
Qed.

End program.
