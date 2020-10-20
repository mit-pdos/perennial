From Perennial.Helpers Require Import PropRestore.
From Perennial.algebra Require Import liftable liftable2 async.

From Perennial.program_proof Require Import buf.buf_proof addr.addr_proof.
From Goose.github_com.mit_pdos.goose_nfsd Require Import buftxn buftxn_replication.
From Perennial.program_proof Require Import buftxn.buftxn_proof buftxn.idealized_buftxn_spec.

From Perennial.goose_lang.lib Require Import crash_lock.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

Section goose_lang.
  Context `{!buftxnG Σ}.

  Context (N:namespace).
  Context (P: Block → iProp Σ).

  Implicit Types (l:loc) (σ:Block) (a:addr).

  Local Definition txnN := N .@ "txn".
  Local Definition lockN := N .@ "lock".

  Definition rb_rep a0 a1 σ (mapsto: addr → object → iProp Σ) : iProp Σ :=
    "Ha0" ∷ mapsto a0 (existT _ (bufBlock σ)) ∗
    "Ha1" ∷ mapsto a1 (existT _ (bufBlock σ)).

  (* stronger lifting theorem that actually extracts the non-map part of rb_rep
  rather than leaving it a wand; this makes it possible to actually update
  rb_rep to a new σ' (by running a fupd) *)
  Lemma rb_rep_lift a0 a1 σ mapsto `{!Conflicting mapsto} :
    rb_rep a0 a1 σ mapsto -∗ ∃ m, "%Hdom" ∷ ⌜dom (gset _) m = {[a0; a1]}⌝ ∗
                                  "rb_rep_m" ∷ ([∗ map] a↦v ∈ m, mapsto a v).
  Proof.
    clear P.
    iNamed 1.
    iExists (<[a0:=existT _ (bufBlock σ)]> (<[a1:=existT _ (bufBlock σ)]> ∅)).
    iDestruct (conflicting with "Ha0 Ha1") as %Hneq.
    iSplit.
    - iPureIntro.
      set_solver.
    - rewrite !big_sepM_insert.
      + rewrite big_sepM_empty.
        iFrame.
      + set_solver.
      + rewrite lookup_insert_ne //.
  Qed.

  Global Instance rb_rep_liftable a0 a1 σ : Liftable (rb_rep a0 a1 σ).
  Proof. apply _. Qed.

  Definition rb_linv l γ: iProp Σ :=
    ∃ a0 a1 σ i,
      "a0" ∷ l ↦[RepBlock.S :: "a0"] (addr2val a0) ∗
      "a1" ∷ l ↦[RepBlock.S :: "a1"] (addr2val a1) ∗
      "#rb_durable" ∷ txn_durable γ i ∗
      "rb_rep" ∷ rb_rep a0 a1 σ
                   (λ a v, modify_token γ a v ∗
                           ephemeral_val_from γ.(buftxn_async_name) i a v) ∗
      "HP" ∷ P σ.

  Definition rb_cinv a0 a1 l γ: iProp Σ :=
    ∃ σ i, rb_rep a0 a1 σ (ephemeral_val_from γ.(buftxn_async_name) i) ∗
           P σ ∗
           txn_durable γ i.

  Definition is_rep_block l: iProp Σ :=
    ∃ γ dinit (txn_l m_l: loc),
    "#txn" ∷ readonly (l ↦[RepBlock.S :: "txn"] #txn_l) ∗
    "#m" ∷ readonly (l ↦[RepBlock.S :: "m"] #m_l) ∗
    (* TODO: make this a crash lock with cinv *)
    "#His_lock" ∷ is_lock lockN #m_l (rb_linv l γ) ∗
    "#His_txn" ∷ txn_proof.is_txn txn_l γ.(buftxn_txn_names) dinit ∗
    "#Htxns" ∷ is_txn_system txnN γ.

  Theorem wp_RepBlock__Read l Q :
    {{{ "#Hrb" ∷ is_rep_block l ∗
        "Hfupd" ∷ (∀ σ, P σ ={⊤}=∗ P σ ∗ Q σ)
    }}}
      RepBlock__Read #l
    {{{ s σ (ok:bool), RET (slice_val s, #ok); is_slice s u8T 1 σ ∗ Q σ }}}.
  Proof.
    iIntros (Φ) "Hpre HΦ"; iNamed "Hpre".
    iNamed "Hrb".
    wp_call.
    wp_loadField.
    wp_apply (lock.acquire_spec with "His_lock").
    iIntros "[Hlocked Hinv]".
    iNamed "Hinv".
    wp_pures.
    wp_loadField.
    wp_apply (wp_BufTxn__Begin with "[]").
    { iFrame "#". }
    iIntros (γtxn l_txn) "Htxn".
    wp_pures.
    wp_loadField.
    change (word.mul 8 4096) with (U64 32768).
    iMod (lift_liftable_into_txn with "Htxn rb_rep") as "[rb_rep Htxn]".
    { solve_ndisj. }
    iNamed "rb_rep".
    iMod ("Hfupd" with "HP") as "[HP HQ]".
    wp_apply (wp_BufTxn__ReadBuf with "[$Htxn $Ha0]").
    { reflexivity. }
    iIntros (dirty bufptr) "[Hbuf Htxn_restore]".
    wp_pures.
    wp_apply (wp_buf_loadField_data with "Hbuf").
    simpl.
    iIntros (data_s) "[Hdata Hbuf]".
    wp_apply (util_proof.wp_CloneByteSlice with "Hdata").
    iIntros (data_s') "[Hdata Hdata_copy]".
    iDestruct (is_buf_return_data _ _ {| bufKind := KindBlock |} _ (bufBlock _) with "[Hdata $Hbuf]") as "Hbuf".
    { simpl; iFrame. }
    simpl.
    iMod ("Htxn_restore" with "Hbuf [%]") as "[Htxn Ha0]".
    { eauto. }
    wp_pures.
    iAssert (rb_rep a0 a1 σ (buftxn_maps_to γtxn)) with "[Ha0 Ha1]" as "rb_rep".
    { iFrame. }
    wp_apply (wp_BufTxn__CommitWait _ _ (rb_rep a0 a1 σ) with "[$Htxn $rb_rep]").
    { unfold txnN, invariant.walN.
      admit. (* disjointness *) }
    { admit. (* disjointness *) }
    iIntros (txn_id' ok) "Hpost".
    wp_pures.
    wp_loadField.
    destruct ok.
    - iDestruct "Hpost" as "[rb_rep #Hdurable]".
      wp_apply (release_spec with "[$His_lock $Hlocked rb_rep a0 a1 HP]").
      { iNext.
        iExists _, _, _, _.
        iFrame "∗#". }
      wp_pures.
      iApply "HΦ".
      iFrame.
    - admit. (* TODO(tej): might be doable with new buftxn spec that preserves old values *)
  Admitted.

End goose_lang.
