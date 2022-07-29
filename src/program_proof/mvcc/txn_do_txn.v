From Perennial.program_proof.mvcc Require Import mvcc_inv txn_common txn_begin txn_commit.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition spec_body (body : val) (txn :loc) r P Q γ τ : iProp Σ :=
  {{{ own_txn txn γ τ ∗ ⌜P r⌝ ∗ txnmap_ptstos τ r }}}
    body #txn
  {{{ w (ok : bool), RET #ok;
      own_txn txn γ τ ∗
      if ok then ⌜Q r w⌝ ∗ txnmap_ptstos τ w else True
  }}}.

Theorem wp_txn__DoTxn txn (body : val) P Q γ :
  (∀ r w, (Decision (Q r w))) ->
  ⊢ {{{ own_txn_uninit txn γ ∗ (∀ r τ, spec_body body txn r P Q γ τ) }}}
    <<< ∀∀ (r : dbmap), ⌜P r⌝ ∗ dbmap_ptstos γ r >>>
      Txn__DoTxn #txn body @ ↑mvccNSST
    <<< ∃∃ (ok : bool), if ok then (∃ w, ⌜Q r w⌝ ∗ dbmap_ptstos γ w) else dbmap_ptstos γ r >>>
    (* We put [v] here as a placeholder; also, there seems to be no notation for no-binder case. *)
    {{{ (v : u64), RET #ok; own_txn_uninit txn γ }}}.
Proof.
  iIntros (Hdec) "!>".
  iIntros (Φ) "[Htxn #Hbody] HAU".
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
  iAssert (∃ p, mvcc_inv_sst γ p)%I with "[Htxn]" as (p) "#Hinv".
  { iNamed "Htxn". eauto with iFrame. }
  wp_apply (wp_txn__Begin with "Htxn").
  iInv "Hinv" as "> HinvO" "HinvC".
  replace (⊤ ∖ ∅) with (⊤ : coPset) by set_solver.
  iMod "HAU" as (r) "[[%HP Hdbps] HAUC]".
  iModIntro.
  iNamed "HinvO".
  iExists ts.
  iFrame "Hts".
  iIntros "(%n & Hts & %Hn)".
  (* Obtain [ltuple_ptsto] over [m]. *)
  iMod (per_key_inv_ltuple_ptstos with "Hkeys") as "[Hkeys Hltuples]".
  iDestruct (dbmap_lookup_big with "Hm Hdbps") as "%Hrm". 
  (* Obtain [ltuple_ptsto] over [r]. *)
  iDestruct (big_sepM_subseteq _ _ r with "Hltuples") as "Hltuples"; first auto.
  (* Obtain [txnmap_auth] and [txnmap_ptsto]. *)
  iMod (txnmap_alloc r) as (τ) "[Htxnmap Htxnps]".
  pose proof (spec_peek future (U64 ts)).
  destruct (peek future (U64 ts)).
  { (* Case NCA. *)
    iMod ("HAUC" $! false with "Hdbps") as "HΦ".
    (* TODO: Add [tid] to [tmods_nca] and get a piece of evidence. *)
    iMod ("HinvC" with "[- HΦ Hltuples Htxnmap Htxnps ]") as "_".
    { (* TODO: close the inv. *) admit. }
    iIntros "!>" (tid) "[Htxn %Etid]".
    iAssert (own_txn txn γ τ)%I with "[Hltuples Htxnmap Htxn]" as "Htxn".
    { iExists _, r, ∅. rewrite map_empty_union. iFrame. }
    wp_pures.
    wp_apply ("Hbody" with "[$Htxn $Htxnps]"); first auto.
    iIntros (w ok) "[Htxn Hpost]".
    wp_pures.
    wp_if_destruct.
    { (* Abort branch. *) admit. }
    wp_apply (wp_txn__Commit with "Htxn").
    iIntros (ok) "Htxn".
    wp_pures.
    admit.
  }
  { (* Case FA. *)
    admit.
  }
  { (* Case FCI. *)
    admit.
  }
  destruct (decide (Q r (mods ∪ r))); last first.
  { (* Case FCC, [Q r (w ∪ m)] not holds. *)
    admit.
  }
  { (* Case FCC, [Q r (w ∪ m)] holds. *)
    admit.
  }
Admitted.


Definition pre_Swap (r : dbmap) : Prop.
Admitted.
Definition post_Swap (r w : dbmap) : Prop.
Admitted.

Theorem wp_SwapSeq txn r γ τ :
  {{{ own_txn txn γ τ ∗ ⌜pre_Swap r⌝ ∗ txnmap_ptstos τ r }}}
    SwapSeq #txn
  {{{ w (ok : bool), RET #ok;
      own_txn txn γ τ ∗
      if ok then ⌜post_Swap r w⌝ ∗ txnmap_ptstos τ w else True
  }}}.
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
