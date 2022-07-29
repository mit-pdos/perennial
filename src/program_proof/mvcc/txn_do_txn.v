From Perennial.program_proof.mvcc Require Import mvcc_inv txn_common txn_begin txn_abort txn_acquire txn_commit.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition spec_body (body : val) (txn :loc) tid r P Q γ τ : iProp Σ :=
  {{{ own_txn txn tid γ τ ∗ ⌜P r⌝ ∗ txnmap_ptstos τ r }}}
    body #txn
  {{{ w (ok : bool), RET #ok;
      own_txn txn tid γ τ ∗
      if ok then ⌜Q r w⌝ ∗ txnmap_ptstos τ w else True
  }}}.

Theorem wp_txn__DoTxn txn (body : val) P Q γ :
  (∀ r w, (Decision (Q r w))) ->
  ⊢ {{{ own_txn_uninit txn γ ∗ (∀ tid r τ, spec_body body txn tid r P Q γ τ) }}}
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
  (*                                                         *)
  (* ok := txn.acquire()                                     *)
  (* if !ok {                                                *)
  (*     txn.Abort()                                         *)
  (*     return false                                        *)
  (* }                                                       *)
  (*                                                         *)
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
  (* FIXME: This is ugly, and might be problematic... *)
  pose proof (spec_peek future ts).
  destruct (peek future ts).
  { (* Case NCA. *)
    iMod ("HAUC" $! false with "Hdbps") as "HΦ".
    (* Add [tid] to [tids_nca] and get a piece of evidence. *)
    iNamed "Hnca".
    iMod (nca_tids_insert ts with "HncaAuth") as "[HncaAuth HncaFrag]".
    { (* TODO: Prove [ts ∉ tids_nca]. *) admit. }
    iAssert (nca_inv_def _ _ _)%I with "[HncaAuth]" as "Hnca".
    { unfold nca_inv_def. iFrame. iPureIntro.
      apply set_Forall_union; last eauto.
      by rewrite set_Forall_singleton.
    }
    iMod ("HinvC" with "[- HΦ Hltuples Htxnmap Htxnps HncaFrag]") as "_".
    { (* Close the invariant. *)
      iNext.
      iDestruct (big_sepS_mono with "Hkeys") as "Hkeys".
      { iIntros (k) "%Helem Hkeys".
        iApply (per_key_inv_weaken_ts (ts + n)%nat with "Hkeys"). lia.
      }
      eauto 15 with iFrame.
    }
    iIntros "!>" (tid) "[Htxn _]".
    iAssert (own_txn txn ts γ τ)%I with "[Hltuples Htxnmap Htxn]" as "Htxn".
    { iExists r, ∅. rewrite map_empty_union. iFrame. }
    wp_pures.
    wp_apply ("Hbody" with "[$Htxn $Htxnps]"); first auto.
    iIntros (w ok) "[Htxn Hpost]".
    wp_pures.
    wp_if_destruct.
    { (* Application-abort branch. *)
      wp_apply (wp_txn__Abort with "Htxn").
      iIntros "Htxn".
      wp_pures.
      (* We'll return something meaningful (rather than [0]) once [res] is added. *)
      by iApply ("HΦ" $! (U64 0)).
    }
    wp_apply (wp_txn__acquire with "Htxn").
    iIntros (ok) "Htxn".
    wp_pures.
    wp_if_destruct.
    { (* System-abort branch. *)
      wp_apply (wp_txn__Abort with "Htxn").
      iIntros "Htxn".
      wp_pures.
      (* We'll return something meaningful (rather than [0]) once [res] is added. *)
      by iApply ("HΦ" $! (U64 0)).
    }
    (* Commit branch. *)
    wp_apply (wp_txn__Commit_false with "[$Htxn HncaFrag]").
    { unfold abort_cases. eauto. }
    by iIntros (ok) "%contra".
  }
  { (* Case FA. *)
    admit.
  }
  { (* Case FCI. *)
    admit.
  }
  destruct (decide (Q r (mods ∪ r))); last first.
  { (* Case FCC, [Q r w] not holds. *)
    admit.
  }
  { (* Case FCC, [Q r w] holds. *)
    admit.
  }
Admitted.


Definition pre_Swap (r : dbmap) : Prop.
Admitted.
Definition post_Swap (r w : dbmap) : Prop.
Admitted.

Theorem wp_SwapSeq txn tid r γ τ :
  {{{ own_txn txn tid γ τ ∗ ⌜pre_Swap r⌝ ∗ txnmap_ptstos τ r }}}
    SwapSeq #txn
  {{{ w (ok : bool), RET #ok;
      own_txn txn tid γ τ ∗
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
    iIntros (tid r τ Φ') "!> Hpre HΦ'".
    iApply (wp_SwapSeq with "Hpre HΦ'").
  }
  done.
Qed.

End program.
