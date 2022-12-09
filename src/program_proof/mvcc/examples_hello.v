(* [mono_nat] must go first otherwise the default scope becomes nat. *)
From iris.base_logic Require Import mono_nat.
From Perennial.program_proof Require Import
     mvcc_prelude mvcc_ghost mvcc_inv
     txnmgr_repr txnmgr_mk txnmgr_new txnmgr_activate_gc
     txn_repr txn_get txn_put txn_delete txn_do_txn.
From Goose.github_com.mit_pdos.go_mvcc Require Import examples.
From Perennial.goose_lang Require Import grove_ffi_adequacy.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition P_Hello (r : dbmap) := ∃ v, r = {[ (U64 0) := v ]}.
Definition Q_Hello (r w : dbmap) := w = {[ (U64 0) := Nil ]}.

Theorem wp_hello txn tid r γ τ :
  {{{ own_txn txn tid r γ τ ∗ ⌜P_Hello r⌝ ∗ txnmap_ptstos τ r }}}
    hello #txn
  {{{ (ok : bool), RET #ok;
      own_txn txn tid r γ τ ∗
      if ok
      then ∃ w, ⌜Q_Hello r w ∧ dom r = dom w⌝ ∗
                txnmap_ptstos τ w
      else True
  }}}.
Proof.
  iIntros (Φ) "(Htxn & %HP & Hpt) HΦ".
  wp_call.
  unfold txnmap_ptstos.
  destruct HP as [v HP].
  rewrite HP.
  rewrite big_sepM_singleton.

  (***********************************************************)
  (* txn.Put(0, "hello")                                     *)
  (* txn.Get(0)                                              *)
  (* txn.Delete(0)                                           *)
  (* return true                                             *)
  (***********************************************************)
  wp_apply (wp_txn__Put with "[$Htxn $Hpt]").
  iIntros "[Htxn Hpt]".
  wp_apply (wp_txn__Get with "[$Htxn $Hpt]").
  iIntros (u found) "[Htxn [Hpt %Hu]]".
  wp_pures.
  wp_apply (wp_txn__Delete with "[$Htxn $Hpt]").
  iIntros (ok) "[Htxn Hpt]".
  wp_pures.
  iApply "HΦ".
  iFrame.
  iModIntro.
  iExists {[ (U64 0) := Nil ]}.
  rewrite big_sepM_singleton.
  iFrame.
  iPureIntro.
  unfold Q_Hello.
  set_solver.
Qed.

Theorem wp_Hello (txn : loc) γ :
  ⊢ {{{ own_txn_uninit txn γ }}}
    <<< ∀∀ (v : dbval), dbmap_ptsto γ (U64 0) 1 v >>>
      Hello #txn @ ↑mvccN
    <<< ∃∃ (ok : bool), if ok then dbmap_ptsto γ (U64 0) 1 Nil else dbmap_ptsto γ (U64 0) 1 v >>>
    {{{ RET #(); own_txn_uninit txn γ }}}.
Proof.
  iIntros "!>".
  iIntros (Φ) "Htxn HAU".
  wp_call.

  (***********************************************************)
  (* body := func(txn *txn.Txn) bool {                       *)
  (*     return hello(txn)                                   *)
  (* }                                                       *)
  (* ok := t.DoTxn(body)                                     *)
  (***********************************************************)
  wp_apply (wp_txn__DoTxn_xres _ _ P_Hello Q_Hello with "[$Htxn]").
  { unfold Q_Hello. apply _. }
  { unfold spec_body_xres.
    clear Φ.
    iIntros (tid r τ Φ) "(Htxn & %HP & Htxnpt) HΦ".
    wp_pures.
    wp_apply (wp_hello with "[$Htxn $Htxnpt]"); first done.
    iApply "HΦ".
  }
  iMod "HAU".
  iModIntro.
  iDestruct "HAU" as (v) "[Hdbpt HAU]".
  iExists {[ (U64 0) := v ]}.
  iSplitL "Hdbpt".
  { unfold dbmap_ptstos.
    rewrite big_sepM_singleton.
    iFrame.
    iPureIntro.
    unfold P_Hello.
    by eauto.
  }
  iIntros (ok w) "Hdbpt".
  iFrame.
  destruct ok eqn:E.
  { (* Case COMMIT. *)
    unfold Q_Hello.
    iDestruct "Hdbpt" as "[%HQ Hdbpt]".
    rewrite HQ /dbmap_ptstos big_sepM_singleton.
    iMod ("HAU" $! true with "Hdbpt") as "HΦ".
    iIntros "!> Htxn".
    wp_pures.
    by iApply "HΦ".
  }
  { (* Case ABORT. *)
    rewrite /dbmap_ptstos big_sepM_singleton.
    iMod ("HAU" $! false with "Hdbpt") as "HΦ".
    iIntros "!> Htxn".
    wp_pures.
    by iApply "HΦ".
  } 
Qed.

Theorem wp_CallHello :
  {{{ True }}}
    CallHello #()
  {{{ RET #(); True }}}.
Proof using heapGS0 mvcc_ghostG0 Σ.
  iIntros (Φ) "_ HΦ".
  wp_call.

  (***********************************************************)
  (* db := txn.MkTxnMgr()                                    *)
  (* db.ActivateGC()                                         *)
  (* txn := db.New()                                         *)
  (* Hello(txn)                                              *)
  (***********************************************************)
  wp_apply wp_MkTxnMgr.
  iIntros (γ mgr) "[#Hmgr Hdbpts]".
  wp_pures.
  wp_apply (wp_txnMgr__ActivateGC with "Hmgr").
  wp_pures.
  wp_apply (wp_txnMgr__New with "Hmgr").
  iIntros (txn) "Htxn".
  wp_pures.
  wp_apply (wp_Hello with "Htxn").
  iApply ncfupd_mask_intro; first set_solver.
  iIntros "Hmask".
  iDestruct (big_sepM_lookup _ _ (U64 0) with "Hdbpts") as "Hdbpt".
  { rewrite lookup_gset_to_gmap_Some.
    split; [set_solver | reflexivity].
  }
  iExists Nil.
  iFrame.
  iIntros (ok) "Hdbpt".
  iMod "Hmask" as "_".
  iIntros "!> Htxn".
  wp_pures.
  by iApply "HΦ".
Qed.

End program.

Module closed_proof.

  Import adequacy.

  Definition helloΣ := #[heapΣ; mvcc_ghostΣ].

  Lemma hello_adequate σ g :
    σ.(world).(grove_node_files) = ∅ →
    g.(global_world).(grove_net) = ∅ →
    recovery_adequacy.adequate_failstop (CallHello #()) σ g (λ v _ _, v = #()).
  Proof.
    intros Hfiles Hnet. eapply (grove_ffi_single_node_adequacy_failstop helloΣ).
    { rewrite Hnet. done. }
    { rewrite Hfiles. done. }
    iIntros (hHeap) "_ _ !>". iApply wp_CallHello; auto.
  Qed.
End closed_proof.
