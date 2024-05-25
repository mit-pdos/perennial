From Perennial.Helpers Require Import PropRestore.
From Perennial.algebra Require Import liftable async.

From Perennial.program_proof Require Import buf.buf_proof addr.addr_proof.
From Goose.github_com.mit_pdos.go_journal Require Import jrnl jrnl_replication.
From Perennial.program_proof Require Import jrnl.jrnl_proof jrnl.sep_jrnl_proof obj.invariant.

From Perennial.goose_lang.lib Require Import crash_lock.
From Perennial.program_proof Require Import disk_prelude.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

Section goose_lang.
  Context `{!jrnlG Σ}.
  Context `{!heapGS Σ}.

  Context (N:namespace).
  Context (P: Block → iProp Σ).

  Implicit Types (l:loc) (σ:Block) (a:addr).

  Local Definition txnN := N .@ "txn".
  Local Definition lockN := N .@ "lock".

  Definition rb_rep a0 a1 σ (pointsto: addr → object → iProp Σ) : iProp Σ :=
    "Ha0" ∷ pointsto a0 (existT _ (bufBlock σ)) ∗
    "Ha1" ∷ pointsto a1 (existT _ (bufBlock σ)).

  (* stronger lifting theorem that actually extracts the non-map part of rb_rep
  rather than leaving it a wand; this makes it possible to actually update
  rb_rep to a new σ' (by running a fupd) *)
  Lemma rb_rep_lift a0 a1 σ pointsto `{!Conflicting pointsto} :
    rb_rep a0 a1 σ pointsto -∗ ∃ m, "%Hdom" ∷ ⌜dom m = {[a0; a1]}⌝ ∗
                                  "rb_rep_m" ∷ ([∗ map] a↦v ∈ m, pointsto a v).
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
    ∃ a0 a1 σ,
      "a0" ∷ l ↦[RepBlock :: "a0"] (addr2val a0) ∗
      "a1" ∷ l ↦[RepBlock :: "a1"] (addr2val a1) ∗
      "rb_rep" ∷ rb_rep a0 a1 σ
                   (λ a v, durable_pointsto_own γ a v) ∗
      "HP" ∷ P σ.

  Definition rb_cinv a0 a1 l γ: iProp Σ :=
    ∃ σ, rb_rep a0 a1 σ (durable_pointsto γ) ∗
         P σ.

  Definition is_rep_block l: iProp Σ :=
    ∃ γ dinit (txn_l m_l: loc),
    "#txn" ∷ readonly (l ↦[RepBlock :: "txn"] #txn_l) ∗
    "#m" ∷ readonly (l ↦[RepBlock :: "m"] #m_l) ∗
    (* TODO: make this a crash lock with cinv *)
    "#His_lock" ∷ is_lock lockN #m_l (rb_linv l γ) ∗
    "#His_txn" ∷ invariant.is_txn txn_l γ.(jrnl_txn_names) dinit ∗
    "#Htxns" ∷ is_txn_system txnN γ.

  Theorem wp_RepBlock__Read l Q :
    (* TODO: need disjointness because invariant.walN and walN are not parameters *)
    txnN ## invariant.walN →
    txnN ## invN →
    {{{ "#Hrb" ∷ is_rep_block l ∗
        "Hfupd" ∷ (∀ σ, P σ ={⊤}=∗ P σ ∗ Q σ)
    }}}
      RepBlock__Read #l
    {{{ s σ (ok:bool), RET (slice_val s, #ok); own_slice s u8T (DfracOwn 1) σ ∗ Q σ }}}.
  Proof.
    iIntros (Hdisj1 Hdisj2 Φ) "Hpre HΦ"; iNamed "Hpre".
    iNamed "Hrb".
    wp_call.
    wp_loadField.
    wp_apply (lock.acquire_spec with "His_lock").
    iIntros "[Hlocked Hinv]".
    iNamed "Hinv".
    wp_pures.
    wp_loadField.
    wp_apply (wp_Op__Begin with "[]").
    { iFrame "#". }
    iIntros (γtxn l_txn) "Htxn".
    wp_pures.
    wp_loadField.
    change (word.mul 8 4096) with (W64 32768).
    iMod (lift_liftable_into_txn with "Htxn rb_rep") as "[rb_rep Htxn]".
    { solve_ndisj. }
    { solve_ndisj. }
    { solve_ndisj. }
    iNamed "rb_rep".
    iMod ("Hfupd" with "HP") as "[HP HQ]".
    iNamed "Htxn".
    wp_apply (wp_Op__ReadBuf with "[$Hjrnl_mem $Ha0]").
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
    iMod ("Htxn_restore" with "Hbuf [%]") as "[Hjrnl_mem Ha0]".
    { eauto. }
    wp_pures.
    iAssert (rb_rep a0 a1 σ (jrnl_maps_to γtxn)) with "[Ha0 Ha1]" as "rb_rep".
    { iFrame. }
    iDestruct (is_jrnl_mem_durable with "Hjrnl_mem Hjrnl_durable") as "Htxn".
    wp_apply (wp_Op__CommitWait _ _ (rb_rep a0 a1 σ) with "[$Htxn $rb_rep]").
    { solve_ndisj. }
    { solve_ndisj. }

    iIntros (ok) "Hpost".
    wp_pures.
    wp_loadField.
    destruct ok.
    - (* iDestruct "Hpost" as (txn_id') "[rb_rep #Hdurable]". *)
      iRename "Hpost" into "rb_rep".
      wp_apply (release_spec with "[$His_lock $Hlocked rb_rep a0 a1 HP]").
      { iNext.
        iExists _, _, _.
        iFrame "∗#". }
      wp_pures.
      iApply "HΦ".
      by iFrame.
    - iRename "Hpost" into "rb_rep".
      iDestruct "rb_rep" as "[rb_rep _]".
      wp_apply (release_spec with "[$His_lock $Hlocked rb_rep a0 a1 HP]").
      { iNext.
        iExists _, _, _.
        iFrame "∗#". }
      wp_pures.
      iApply "HΦ".
      by iFrame.
  Qed.

End goose_lang.
