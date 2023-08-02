From Perennial.program_proof.mvcc Require Import
     mvcc_prelude mvcc_ghost mvcc_inv
     db_repr db_mk db_new_txn db_activate_gc
     txn_repr txn_read txn_write txn_delete txn_run.
From Goose.github_com.mit_pdos.vmvcc Require Import examples.
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

  (*@ func hello(txn *vmvcc.Txn) bool {                                       @*)
  (*@     txn.Write(0, "hello")                                               @*)
  (*@                                                                         @*)
  wp_apply (wp_txn__Write with "[$Htxn $Hpt]").
  iIntros "[Htxn Hpt]".
  
  (*@     txn.Read(0)                                                         @*)
  (*@                                                                         @*)
  wp_apply (wp_txn__Read with "[$Htxn $Hpt]").
  iIntros (u found) "[Htxn [Hpt %Hu]]".
  wp_pures.

  (*@     txn.Delete(0)                                                       @*)
  (*@                                                                         @*)
  wp_apply (wp_txn__Delete with "[$Htxn $Hpt]").
  iIntros (ok) "[Htxn Hpt]".
  wp_pures.

  (*@     return true                                                         @*)
  (*@ }                                                                       @*)
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

  (*@ func Hello(txno *vmvcc.Txn) {                                           @*)
  (*@     body := func(txni *vmvcc.Txn) bool {                                @*)
  (*@         return hello(txni)                                              @*)
  (*@     }                                                                   @*)
  (*@     txno.Run(body)                                                      @*)
  (*@ }                                                                       @*)
  wp_apply (wp_txn__Run_xres _ _ P_Hello Q_Hello with "[$Htxn]").
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

  (*@ func CallHello() {                                                      @*)
  (*@     db := vmvcc.MkDB()                                                  @*)
  (*@     db.ActivateGC()                                                     @*)
  (*@     txn := db.NewTxn()                                                  @*)
  (*@                                                                         @*)
  wp_apply wp_MkDB.
  iIntros (γ db) "[#Hdb Hdbpts]".
  wp_pures.
  wp_apply (wp_DB__ActivateGC with "Hdb").
  wp_pures.
  wp_apply (wp_DB__NewTxn with "Hdb").
  iIntros (txn) "Htxn".
  wp_pures.

  (*@     Hello(txn)                                                          @*)
  (*@ }                                                                       @*)
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
