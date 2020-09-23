From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From iris.algebra Require Import numbers.
From Perennial.algebra Require Import deletable_heap log_heap liftable.
From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_logic Require Import ghost_var_old.

From Goose.github_com.mit_pdos.goose_nfsd Require Import addr buftxn.
From Perennial.program_proof Require Import wal.specs wal.heapspec txn.txn_proof buf.buf_proof addr.addr_proof.

Class buftxnG Σ :=
  { buftxn_txn   :> txnG Σ;
    buftxn_bufs  :> gen_heapPreG addr {K & bufDataT K} Σ;
  }.

Section heap.
Context `{!buftxnG Σ}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).
Implicit Types (mT : gmap addr {K & bufDataT K}).

Definition is_buftxn (buftx : loc)
                     (mT : gmap addr {K & bufDataT K})
                     γUnified : iProp Σ :=
  (
    ∃ (l : loc) (bufmap : loc) (gBufmap : gmap addr buf) (txid : u64),
      "Hbuftx.l" ∷ buftx ↦[BufTxn.S :: "txn"] #l ∗
      "Hbuftx.map" ∷ buftx ↦[BufTxn.S :: "bufs"] #bufmap ∗
      "#Histxn" ∷ is_txn l γUnified ∗
      "Hbufmap" ∷ is_bufmap bufmap gBufmap ∗
      "%Hbufmapelem" ∷ ⌜ (λ b, existT _ (bufData b)) <$> gBufmap ⊆ mT ⌝ ∗
      "#Hctxvalid" ∷ ( [∗ map] a ↦ v ∈ mT,
        ⌜ valid_addr a ∧ valid_off (projT1 v) a.(addrOff) ⌝ ) ∗
      "Hctxelem" ∷ ( [∗ map] a ↦ v ∈ mT,
        let dirty := match gBufmap !! a with
                     | None => false
                     | Some buf => bufDirty buf
                     end in
        if dirty then
          ∃ (v0 : bufDataT (projT1 v)),
            mapsto_txn γUnified a (existT _ v0)
        else
          mapsto_txn γUnified a v )
  )%I.

Theorem wp_buftxn_Begin l γUnified:
  {{{ is_txn l γUnified
  }}}
    Begin #l
  {{{ (buftx : loc), RET #buftx;
      is_buftxn buftx ∅ γUnified
  }}}.
Proof.
  iIntros (Φ) "#Htxn HΦ".

  wp_call.
  wp_apply (wp_MkBufMap with "[$]").
  iIntros (bufmap) "Hbufmap".
  wp_apply wp_allocStruct; eauto.
  iIntros (buftx) "Hbuftx".
  iDestruct (struct_fields_split with "Hbuftx") as "(Hbuftx.txn & Hbuftx.bufs & %)".
  wp_apply util_proof.wp_DPrintf.
  wp_pures.
  iApply "HΦ".
  iExists _, _, _, _.
  iFrame.
  rewrite big_sepM_empty. iFrame "Htxn ∗".
  iSplit; first by done.
  rewrite left_id.
  rewrite big_sepM_empty //.
  Unshelve. all: exact (U64 0).
Qed.

Theorem wp_BufTxn__ReadBuf buftx mT γUnified a (sz : u64) v :
  {{{
    is_buftxn buftx mT γUnified ∗
    ⌜ mT !! a = Some v ⌝ ∗
    ⌜ sz = bufSz (projT1 v) ⌝
  }}}
    BufTxn__ReadBuf #buftx (addr2val a) #sz
  {{{
    (bufptr : loc) dirty, RET #bufptr;
    is_buf bufptr a (Build_buf (projT1 v) (projT2 v) dirty) ∗
    ( ∀ v' dirty',
      ( ⌜ dirty' = true ∨ (dirty' = dirty ∧ projT2 v = v') ⌝ ∗
        is_buf bufptr a (Build_buf (projT1 v) v' dirty') ) ==∗
      ( is_buftxn buftx (<[a := existT _ v']> mT) γUnified ) )
  }}}.
Proof.
  iIntros (Φ) "(Htxn & %Ha & ->) HΦ".
  iNamed "Htxn".
  iDestruct (big_sepM_lookup with "Hctxvalid") as "%"; eauto.
  wp_call.
  wp_loadField.
  wp_apply (wp_BufMap__Lookup with "[$Hbufmap]"); first intuition.
  iIntros (bufptr) "Hbufptr".
  wp_pures.
  destruct (gBufmap !! a) eqn:Hbufmap_a.
  - iDestruct "Hbufptr" as "[Hbufptr Hisbufmap]".
    iDestruct (is_buf_not_null with "Hbufptr") as %Hbufptr_not_null.

    (* bufmapelem now a pure fact:

    iDestruct (big_sepM_lookup with "Hbufmapelem") as %HmT_a; eauto.

    rewrite Ha in HmT_a.
    inversion HmT_a; clear HmT_a; subst.
    destruct b; rewrite /=.

    wp_if_destruct; try congruence.
    iApply "HΦ".
    iFrame "Hbufptr".

    iIntros (v' dirty') "[% Hbufptr]".
    iDestruct ("Hisbufmap" with "Hbufptr") as "Hisbufmap".
    intuition idtac.
    + subst.
      iModIntro.
      iExists _, _, _, _.
      iFrame "# ∗".
      iDestruct (big_sepM_lookup with "Hbufmapelem") as %HmT_a; eauto.
      iSplitL "Hbufmapelem".
      {
        iDestruct (big_sepM_forall with "Hbufmapelem") as "Hbufmapelem".
        iApply big_sepM_forall.
        iIntros (k x).
        destruct (decide (a = k)).
        { subst. repeat rewrite lookup_insert.
          iPureIntro; intros. inversion H; subst; clear H.
          simpl; eauto. }
        { repeat rewrite -> lookup_insert_ne by eauto.
          eauto. }
      }

      iSplitL "Hctxvalid".
      {
        iDestruct (big_sepM_insert_acc with "Hctxvalid") as "[Ha Hctxvalid2]"; eauto.
        iApply "Hctxvalid2"; eauto.
      }

      iDestruct (big_sepM_delete with "Hctxelem") as "[Hma Hctxelem]"; eauto.
      iApply big_sepM_insert_delete.
      iSplitL "Hma".
      { rewrite lookup_insert. rewrite Hbufmap_a /=.
        destruct bufDirty; eauto. }
      iApply (big_sepM_mono with "Hctxelem").
      iIntros (k x Hkx) "Hk".
      destruct (decide (a = k)).
      { subst. rewrite lookup_delete in Hkx. congruence. }
      rewrite -> lookup_insert_ne by eauto.
      destruct (gBufmap !! k); eauto.

    + subst.
      iModIntro.
      iExists _, _, _, _.
      iFrame "# ∗".
      iDestruct (big_sepM_lookup with "Hbufmapelem") as %HmT_a; eauto.
      iSplitL "Hbufmapelem".
      {
        iDestruct (big_sepM_forall with "Hbufmapelem") as "Hbufmapelem".
        iApply big_sepM_forall.
        iIntros (k x).
        destruct (decide (a = k)).
        { subst. repeat rewrite lookup_insert.
          iPureIntro; intros. inversion H; subst; clear H.
          simpl; eauto. }
        { repeat rewrite -> lookup_insert_ne by eauto.
          eauto. }
      }

      iSplitR "Hctxelem".
      { iDestruct (big_sepM_delete with "Hctxvalid") as "[%Hca Hctxvalid']"; eauto.
        iApply big_sepM_insert_delete; iFrame "Hctxvalid'".
        eauto. }

      iDestruct (big_sepM_delete with "Hctxelem") as "[Hca Hctxelem]"; eauto.
      simpl in *.
      iApply big_sepM_insert_delete.
      rewrite lookup_insert /=.
      admit.

  - iDestruct "Hbufptr" as "[-> Hbufptr]".
    wp_if_destruct.
    2: congruence.

    wp_loadField.
    iDestruct (big_sepM_lookup_acc with "Hctxelem") as "[Hma Hctxelem]"; eauto.
    rewrite Hbufmap_a /=.

    wp_apply (wp_txn_Load with "[$Histxn $Hma]").
    iIntros (bufptr b) "(Hbuf & % & % & Hma)".
    wp_pures.
    iDestruct ("Hctxelem" with "Hma") as "Hctxelem".

    wp_loadField.
    wp_apply (wp_BufMap__Insert with "[$Hbufptr $Hbuf]").
    iIntros "Hbufptr".

    wp_loadField.
    wp_apply (wp_BufMap__Lookup with "[$Hbufptr]"); intuition.
    iIntros (bufptr2) "Hbufptr2".

    rewrite lookup_insert.
    iDestruct "Hbufptr2" as "[Hbufptr2 Hisbufmap]".

    destruct b, v. simpl in *.
    inversion H1; subst.
    apply eq_sigT_eq_dep in H1.
    apply Eqdep_dec.eq_dep_eq_dec in H1.
    2: apply bufDataKind_eq_dec.
    subst.

    iApply "HΦ".
    iFrame "Hbufptr2".

    iIntros (v' dirty') "[% Hbufptr]".
    iDestruct ("Hisbufmap" with "Hbufptr") as "Hisbufmap".
    intuition idtac.
    + subst.
      iMod (gen_heap_update with "Hctx Ha") as "[Hctx Ha]".
      iFrame "Ha".
      iModIntro.
      iExists _, _, _, _, _.
      iFrame "Hctx".
      iFrame "# ∗".

      rewrite insert_insert.
      iSplitL "Hbufmapelem".
      {
        iApply (big_sepM_insert); eauto.
        iSplitR.
        { rewrite lookup_insert. eauto. }
        iApply (big_sepM_mono with "Hbufmapelem").
        iIntros (k x0) "% %". iPureIntro.
        destruct (decide (a = k)).
        { subst; congruence. }
        repeat rewrite -> lookup_insert_ne by eauto.
        eauto.
      }

      iSplitL "Hctxvalid".
      {
        iDestruct (big_sepM_insert_acc with "Hctxvalid") as "[Ha Hctxvalid']"; eauto.
        iApply "Hctxvalid'"; eauto.
      }

      iDestruct (big_sepM_delete with "Hctxelem") as "[Hma Hctxelem]"; eauto.
      iApply big_sepM_insert_delete.
      iSplitL "Hma".
      { rewrite lookup_insert. rewrite Hbufmap_a /=.
        iExists _; iFrame. }
      iApply (big_sepM_mono with "Hctxelem").
      iIntros (k x0 Hkx0) "Hk".
      destruct (decide (a = k)).
      { subst. rewrite lookup_delete in Hkx0. congruence. }
      rewrite -> lookup_insert_ne by eauto.
      destruct (gBufmap !! k); eauto.

    + subst.
      iFrame "Ha".
      iModIntro.
      iExists _, _, _, _, _.
      iFrame "Hctx".
      iFrame "# ∗".

      rewrite insert_insert.
      iSplitL "Hbufmapelem".
      {
        iApply (big_sepM_insert); eauto.
      }

      iApply (big_sepM_mono with "Hctxelem").
      iIntros (k x0 Hkx0) "Hk".
      destruct (decide (a = k)).
      { subst. rewrite lookup_insert. rewrite Hbufmap_a.
        simpl. eauto. }
      rewrite -> lookup_insert_ne by eauto.
      destruct (gBufmap !! k); eauto.
      Unshelve.
      all: eauto.
     *)
Admitted.

Theorem wp_BufTxn__OverWrite buftx mt γUnified a v0 v (sz : u64) (vslice : Slice.t) :
  {{{
    is_buftxn buftx mt γUnified ∗
    ⌜ mt !! a = Some v0 ⌝ ∗
    is_buf_data vslice (projT2 v) a ∗
    ⌜ sz = bufSz (projT1 v) ⌝ ∗
    ⌜ projT1 v = projT1 v0 ⌝
  }}}
    BufTxn__OverWrite #buftx (addr2val a) #sz (slice_val vslice)
  {{{
    RET #();
    is_buftxn buftx (<[a := v]> mt) γUnified
  }}}.
Proof using.
  iIntros (Φ) "(Htxn & Ha & Hvslice & -> & %) HΦ".
Opaque struct.t.
  wp_call.
  iNamed "Htxn".

  (*
  iDestruct (gen_heap_valid with "Hctx Ha") as %HmT_a2.
  iDestruct (big_sepM_lookup with "Hctxvalid") as "%"; eauto.

  wp_loadField.
  wp_apply (wp_BufMap__Lookup with "[$Hbufmap]"); intuition.
  iIntros (bufptr) "Hbufmapptr".

  wp_apply wp_ref_to; first by eauto.
  iIntros (b) "Hb".
  wp_pures.

  destruct (gBufmap !! a) eqn:Hbufmap_a.
  - iDestruct "Hbufmapptr" as "[Hisbuf Hisbufmap]".
    iDestruct (is_buf_not_null with "Hisbuf") as "%".
    wp_load.
    wp_pures.
    destruct (bool_decide (#bufptr = #null)) eqn:Hbooldec.
    { apply bool_decide_eq_true_1 in Hbooldec; congruence. }
    wp_pures.
    replace (bufSz (projT1 v)) with (bufSz (projT1 v0)) by congruence.
    wp_load.
    wp_apply (wp_buf_loadField_sz with "Hisbuf"); iIntros "Hisbuf".
    iDestruct (big_sepM_lookup with "Hbufmapelem") as %HmT_a; eauto.
    rewrite HmT_a2 in HmT_a; inversion HmT_a; subst.
    rewrite /=.
    wp_pures.
    destruct (bool_decide (#(bufSz b0.(bufKind)) = #(bufSz b0.(bufKind)))) eqn:He.
    2: { apply bool_decide_eq_false_1 in He; congruence. }
    wp_pures.
    wp_load.
    wp_apply (wp_buf_storeField_data with "[$Hisbuf $Hvslice]"); eauto.
    iIntros "Hisbuf".

    iMod (gen_heap_update with "Hctx Ha") as "[Hctx Ha]".

    wp_pures.
    wp_load.
    wp_apply (wp_Buf__SetDirty with "Hisbuf"); iIntros "Hisbuf".
    iApply "HΦ".
    iFrame.

    iDestruct ("Hisbufmap" with "Hisbuf") as "Hisbufmap".

    iExists _, _, _, _, _.
    iFrame "Hctx Histxn".
    iFrame "Hisbufmap".
    iFrame.
    rewrite /=.

    iSplitL "Hbufmapelem".
    {
      iApply (big_sepM_insert_delete).
      iSplitR.
      { rewrite lookup_insert. destruct v. auto. }
      iDestruct (big_sepM_delete with "Hbufmapelem") as "[_ Hbufmapelem]"; eauto.
      iApply (big_sepM_mono with "Hbufmapelem").
      iIntros (k x0) "% %". iPureIntro.
      destruct (decide (a = k)).
      { subst. rewrite lookup_delete in H3. congruence. }
      repeat rewrite -> lookup_insert_ne by eauto.
      eauto.
    }

    iSplitL "Hctxvalid".
    {
      iDestruct (big_sepM_insert_acc with "Hctxvalid") as "[Ha Hctxvalid']"; eauto.
      iApply "Hctxvalid'".
      rewrite H. done.
    }

    iDestruct (big_sepM_delete with "Hctxelem") as "[Hma Hctxelem]"; eauto.
    iApply big_sepM_insert_delete.
    iSplitL "Hma".
    { rewrite lookup_insert. rewrite Hbufmap_a /=.
      destruct v; simpl in *; subst.
      destruct (b0.(bufDirty)).
      { iDestruct "Hma" as (v0) "Hma".
        iExists _; iFrame. }
      iExists _; iFrame.
    }
    iApply (big_sepM_mono with "Hctxelem").
    iIntros (k x0 Hkx0) "Hk".
    destruct (decide (a = k)).
    { subst. rewrite lookup_delete in Hkx0. congruence. }
    rewrite -> lookup_insert_ne by eauto.
    destruct (gBufmap !! k); eauto.

  - iDestruct "Hbufmapptr" as "[-> Hisbufmap]".
    wp_load.
    wp_pures.
    wp_apply (wp_MkBuf with "[$Hvslice]").
    { rewrite H. intuition. }
    iIntros (bufptr) "Hisbuf".
    wp_pures.
    wp_store.
    wp_pures.
    wp_load.
    wp_apply (wp_Buf__SetDirty with "Hisbuf"); iIntros "Hisbuf".
    wp_load.
    wp_loadField.

    iMod (gen_heap_update with "Hctx Ha") as "[Hctx Ha]".

    wp_apply (wp_BufMap__Insert with "[$Hisbufmap $Hisbuf]").
    iIntros "Hisbufmap".
    iApply "HΦ".
    iFrame "Ha".

    iExists _, _, _, _, _.
    iFrame "Hctx Histxn".
    iFrame.
    rewrite /=.

    iSplitL "Hbufmapelem".
    {
      iApply (big_sepM_insert); eauto.
      iSplitR.
      { rewrite lookup_insert. destruct v. auto. }
      iApply (big_sepM_mono with "Hbufmapelem").
      iIntros (k x0) "% %". iPureIntro.
      destruct (decide (a = k)).
      { subst. congruence. }
      repeat rewrite -> lookup_insert_ne by eauto.
      eauto.
    }

    iSplitL "Hctxvalid".
    {
      iDestruct (big_sepM_insert_acc with "Hctxvalid") as "[Ha Hctxvalid']"; eauto.
      iApply "Hctxvalid'".
      rewrite H. done.
    }

    iDestruct (big_sepM_delete with "Hctxelem") as "[Hma Hctxelem]"; eauto.
    iApply big_sepM_insert_delete.
    iSplitL "Hma".
    { rewrite lookup_insert. rewrite Hbufmap_a /=.
      destruct v, v0; simpl in *; subst.
      iExists _. iFrame.
    }
    iApply (big_sepM_mono with "Hctxelem").
    iIntros (k x0 Hkx0) "Hk".
    destruct (decide (a = k)).
    { subst. rewrite lookup_delete in Hkx0. congruence. }
    rewrite -> lookup_insert_ne by eauto.
    destruct (gBufmap !! k); eauto.
*)
Admitted.

Theorem BufTxn_lift_one buftx mt γUnified a v E :
  ↑invN ⊆ E ->
  (
    is_buftxn buftx mt γUnified ∗
    mapsto_txn γUnified a v
  )
    ={E}=∗
  (
    is_buftxn buftx (<[a := v]> mt) γUnified
  ).
Proof.
  iIntros (HNE) "[Htxn Ha]".
  iNamed "Htxn".

  (*
  iAssert (⌜ mT !! a = None ⌝)%I as %Hnone.
  {
    destruct (mT !! a) eqn:He; eauto.
    iDestruct (big_sepM_lookup with "Hctxelem") as "Ha2"; eauto.
    destruct (gBufmap !! a); rewrite /=.
    { destruct b.(bufDirty).
      { iDestruct "Ha2" as (v0) "Ha2".
        iDestruct (mapsto_txn_2 with "Ha Ha2") as %[]. }
      { iDestruct (mapsto_txn_2 with "Ha Ha2") as %[]. }
    }
    { iDestruct (mapsto_txn_2 with "Ha Ha2") as %[]. }
  }

  iAssert (⌜ gBufmap !! a = None ⌝)%I as %Hgnone.
  {
    destruct (gBufmap !! a) eqn:He; eauto.
    iDestruct (big_sepM_lookup with "Hbufmapelem") as %Ha2; eauto.
    rewrite Ha2 in Hnone; congruence.
  }

  iPoseProof "Histxn" as "Histxn0".
  iNamed "Histxn".
  iMod (mapsto_txn_valid with "Histxna [Ha Histxna]") as "[Ha %Havalid]"; eauto.

  iMod ((gen_heap_alloc _ _ v) with "Hctx") as "[Hctx Haa]"; eauto.
  iModIntro.
  iSplitR "Haa"; [|iFrame].

  iExists _, _, _, _, _.
  iFrame "Hctx Histxn0".
  iFrame.
  iSplitL "Hbufmapelem".
  { iApply big_sepM_mono; iFrame.
    iPureIntro; simpl; intros.
    destruct (decide (a = x)); subst.
    { rewrite Hnone in H. congruence. }
    rewrite -> lookup_insert_ne by eauto. eauto.
  }

  iSplitL "Hctxvalid".
  { iApply big_sepM_insert; eauto.
    iFrame "Hctxvalid". iPureIntro; intuition eauto. }

  iApply (big_sepM_insert); eauto.
  iFrame.
  rewrite Hgnone. iFrame.
*)
Admitted.

Instance mapsto_txn_conflicting γUnified : Conflicting (mapsto_txn γUnified).
Proof.
  rewrite /Conflicting /ConflictsWith.
  iIntros (a0 v0 a1 v1).
  iIntros "Hm1 Hm2".
  destruct (decide (a0 = a1)); eauto; subst.
  iDestruct (mapsto_txn_2 with "Hm1 Hm2") as %[].
Qed.

Instance mapsto_txn_conflicts_with γUnified : ConflictsWith (mapsto_txn γUnified) (mapsto_txn γUnified).
Proof.
  apply mapsto_txn_conflicting.
Qed.

Theorem BufTxn_lift buftx mt γUnified (m : gmap addr {K & _}) E :
  ↑invN ⊆ E ->
  (
    is_buftxn buftx mt γUnified ∗
    [∗ map] a ↦ v ∈ m, mapsto_txn γUnified a v
  )
    ={E}=∗
  (
    is_buftxn buftx (m ∪ mt) γUnified
  ).
Proof.
  iIntros (HNE) "[Htxn Ha]".
  iNamed "Htxn".

  iDestruct (big_sepM_disjoint_pred with "Hctxelem Ha") as %Hd.

  iMod (big_sepM_mono_fupd _ (fun a v => mapsto_txn γUnified a v ∗ ⌜ valid_addr a ∧ valid_off (projT1 v) a.(addrOff) ⌝)%I _ emp%I with "[] [$Ha]") as "[_ Ha]".
  { iModIntro. iIntros (???) "[_ H]".
    iNamed "Histxn".
    iMod (mapsto_txn_valid with "Histxna [H Histxna]") as "[H %Havalid]"; eauto.
    iModIntro. iFrame. intuition eauto. }
  iDestruct (big_sepM_sep with "Ha") as "[Ha Havalid]".

  (*
  iMod (gen_heap_alloc_gen with "Hctx") as "[Hctx Haa]"; eauto.
  iModIntro.
  iSplitR "Haa"; last iFrame.

  iExists _, _, _, _, _.
  iFrame "Hctx Histxn".
  iFrame.

  iSplitL "Hbufmapelem".
  { iApply big_sepM_mono; iFrame.
    iPureIntro; simpl; intros.
    erewrite lookup_union_Some_r; eauto.
  }

  iSplitL "Hctxvalid Havalid".
  { iApply big_sepM_union; eauto. }

  iApply big_sepM_union; eauto.
  iFrame.
  iApply big_sepM_mono; last iFrame.
  iIntros (???) "H".

  destruct (gBufmap !! k); last by iFrame.
  destruct b.(bufDirty); iFrame.
  destruct x.
  iExists _; iFrame.
*)
Admitted.

(*
Theorem BufTxn_lift_pred `{!Liftable P} buftx γt γUnified E :
  ↑invN ⊆ E ->
  (
    is_buftxn buftx γt γUnified ∗
    P (fun a v => mapsto_txn γUnified a v)
  )
    ={E}=∗
  (
    is_buftxn buftx γt γUnified ∗
    P (fun a v => mapsto (hG := γt) a 1 v)
  ).
Proof.
  iIntros (HNE) "(Htxn & Hp)".
  unfold Liftable in Liftable0.
  iDestruct (Liftable0 with "Hp") as (m) "[Hm Hp]".
  { iIntros (a0 v0 a1 v1) "Ha0 Ha1".
    destruct (decide (a0 = a1)); subst; eauto.
    iDestruct (mapsto_txn_2 with "Ha0 Ha1") as %[]. }
  iMod (BufTxn_lift with "[$Htxn $Hm]") as "[Htxn Hm]"; eauto.
  iFrame.
  iApply "Hp".
  by iFrame.
Qed.
*)

Theorem wp_BufTxn__CommitWait buftx mt γUnified (wait : bool) E (Q : nat -> iProp Σ) :
  {{{
    is_buftxn buftx mt γUnified ∗
    ( |={⊤ ∖ ↑walN ∖ ↑invN, E}=> ∃ (σl : async (gmap addr {K & bufDataT K})),
        "Hcrashstates_frag" ∷ own γUnified.(txn_crashstates) (◯E σl) ∗
        "Hcrashstates_fupd" ∷ (
          let σ := mt ∪ latest σl in
          own γUnified.(txn_crashstates) (◯E (async_put σ σl))
          ={E, ⊤ ∖ ↑walN ∖ ↑invN}=∗ Q (length (possible σl)) ))
  }}}
    BufTxn__CommitWait #buftx #wait
  {{{
    (ok : bool), RET #ok;
    if ok then
      ∃ txnid,
      Q txnid ∗
      (⌜wait = true⌝ -∗ own γUnified.(txn_walnames).(wal_heap_durable_lb) (◯ (MaxNat txnid))) ∗
      [∗ map] a ↦ v ∈ mt, mapsto_txn γUnified a v
    else
      [∗ map] a ↦ v ∈ mt, ∃ data, mapsto_txn γUnified a (existT (projT1 v) data)
  }}}.
Proof.
  iIntros (Φ) "(Htxn & Hfupd) HΦ".
  iNamed "Htxn".

  wp_call.
  wp_apply util_proof.wp_DPrintf.
  wp_loadField.
  wp_apply (wp_BufMap__DirtyBufs with "Hbufmap").
  iIntros (dirtyslice bufptrlist) "(Hdirtyslice & Hdirtylist)".
  wp_loadField.

  pose proof (map_union_filter
              (λ x, bufDirty <$> (gBufmap !! fst x) = Some true)
              mt) as Hmt.
  rewrite <- Hmt at 2.
  iDestruct (big_sepM_union with "Hctxelem") as "[Hctxelem0 Hctxelem1]".
  { apply map_disjoint_filter. }

  iAssert (⌜ dom (gset addr) (filter (λ x, bufDirty <$> (gBufmap !! fst x) = Some true) mt) =
             dom (gset addr) (filter (λ x, (snd x).(bufDirty) = true) gBufmap) ⌝)%I as "%Hdom".
  { admit. }

  iDestruct (big_sepM_mono with "Hctxelem1") as "Hctxelem1".
  { iIntros (k x Hkx) "H".
    eapply map_filter_lookup_Some in Hkx; simpl in Hkx; destruct Hkx.
    destruct (gBufmap !! k).
    2: iExact "H".
    simpl in H0.
    destruct b.(bufDirty); try congruence.
    iFrame. }

  iDestruct (big_sepM_mono with "Hctxelem0") as "Hctxelem0".
  { iIntros (k x Hkx) "H".
    eapply map_filter_lookup_Some in Hkx; simpl in Hkx; destruct Hkx.
    destruct (gBufmap !! k).
    { simpl in *. destruct b.(bufDirty); try congruence. iExact "H". }
    simpl in *. congruence. }
  simpl.

  replace (filter (λ x, bufDirty <$> gBufmap !! x.1 = Some true) mt)
     with ((λ b : buf, existT b.(bufKind) b.(bufData)) <$>
           (filter (λ x : addr * buf, (x.2).(bufDirty) = true) gBufmap)).
  2: { admit. }

  iPoseProof big_sepM_fmap as "[#Hfmap0 #Hfmap1]".
  iDestruct ("Hfmap0" with "Hctxelem0") as "Hctxelem0".

  wp_apply (wp_txn_CommitWait _ _ _ _ _ _ _ _
    (λ txnid,
      ( [∗ map] k↦x ∈ filter (λ v, bufDirty <$> gBufmap !! v.1 ≠ Some true) mt, mapsto_txn γUnified k x ) ∗
      Q txnid)%I
    with "[$Histxn $Hdirtyslice Hdirtylist Hctxelem0 Hctxelem1 Hfupd]").
  {
    iDestruct (big_sepML_sepM with "[$Hdirtylist $Hctxelem0]") as "Hdirtylist".
    iSplitL "Hdirtylist".
    { iApply (big_sepML_mono with "Hdirtylist").
      iPureIntro.
      iIntros (k v lv) "(Hisbuf & H)".
      iFrame. }

    iMod "Hfupd".
    iNamed "Hfupd".

    iAssert (⌜filter (λ v, bufDirty <$> gBufmap !! v.1 ≠ Some true) mt ⊆ σl.(latest) ⌝)%I as "%Hcleansubset".
    {
      (* use Hctxelem1, Hcrashstates_frag, and Histxn *)
      admit.
    }

    iModIntro.
    iExists _. iFrame.
    iIntros "[% Hcrashstates_fupd']".

    iMod ("Hcrashstates_fupd" with "[Hcrashstates_fupd']") as "HQ".
    {
      rewrite <- Hmt at 2.
      rewrite -assoc.
      setoid_rewrite -> (map_subseteq_union _ σl.(latest)) at 2; eauto.
      iExactEq "Hcrashstates_fupd'". repeat f_equal.
      admit.
    }

    iModIntro.
    iFrame.
  }
  iIntros (ok) "Hunifiedtxns".
  wp_pures.

  iApply "HΦ".
  destruct ok.
  - iDestruct "Hunifiedtxns" as "[Hq Hmapsto0]".
    iDestruct ("Hq" with "[]") as (txnid) "[Hq Hflush]".
    {
      (* need to generate an empty txn if bypassing log for read-only *)
      admit.
    }

    iDestruct "Hq" as "[Hmapsto1 Hq]".
    iExists _. iFrame.
    iDestruct (big_sepM_fmap with "Hmapsto0") as "Hmapsto0".
    iDestruct (big_sepM_union with "[$Hmapsto0 $Hmapsto1]") as "Hmapsto".
    { admit. }
    iExactEq "Hmapsto". repeat f_equal.
    admit.

  - admit.
    (* TODO: need PreQ in txn__CommitWait *)
Admitted.

(*
Theorem wp_BufTxn__CommitWait_pred `{!Liftable P} buftx γt γUnified :
  {{{
    is_buftxn buftx γt γUnified ∗
    P (fun a v => mapsto (hG := γt) a 1 v)
  }}}
    BufTxn__CommitWait #buftx #true
  {{{
    (ok: bool), RET #ok;
    if ok then
      P (fun a v => mapsto_txn γUnified a v)
    else
      (* XXX??? *) emp
  }}}.
Proof.
  iIntros (Φ) "(Htxn & Hp) HΦ".
  unfold Liftable in Liftable0.
  iDestruct (Liftable0 with "Hp") as (m) "[Hm Hp]".
  { iIntros (a0 v0 a1 v1) "Ha0 Ha1".
    destruct (decide (a0 = a1)); subst; eauto.
    iDestruct (mapsto_valid_2 with "Ha0 Ha1") as %Hf; eauto. }
  wp_apply (wp_BufTxn__CommitWait with "[$Htxn $Hm]").
  iIntros (ok) "Hm".
  iApply "HΦ".
  destruct ok.
  - iApply "Hp".
    iFrame.
  - done.
Qed.
*)

End heap.
