From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.algebra Require Import deletable_heap liftable.
From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.

From Goose.github_com.mit_pdos.goose_nfsd Require Import addr buftxn.
From Perennial.program_proof Require Import txn.specs buf.specs addr.specs.

Section heap.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!inG Σ (authR (optionUR (exclR boolO)))}.
Context `{!gen_heapPreG addr (sigT (fun K => @bufDataT K)) Σ}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Definition is_buftxn (buftx : loc)
                     (γT : gen_heapG addr (sigT (fun K => @bufDataT K)) Σ)
                     γUnified : iProp Σ :=
  (
    ∃ (l : loc) mT (bufmap : loc) (gBufmap : gmap addr buf) (txid : u64),
      buftx ↦[BufTxn.S :: "txn"] #l ∗
      buftx ↦[BufTxn.S :: "bufs"] #bufmap ∗
      buftx ↦[BufTxn.S :: "Id"] #txid ∗
      is_txn l γUnified ∗
      is_bufmap bufmap gBufmap ∗
      gen_heap_ctx (hG := γT) mT ∗
      ( [∗ map] a ↦ b ∈ gBufmap,
        ⌜ mT !! a = Some (existT _ (bufData b)) ⌝ ) ∗
      ( [∗ map] a ↦ v ∈ mT,
        ⌜ valid_addr a ⌝ ) ∗
      ( [∗ map] a ↦ v ∈ mT,
        let dirty := match gBufmap !! a with
                     | None => false
                     | Some buf => bufDirty buf
                     end in
        if dirty then
          ∃ (v0 : @bufDataT (projT1 v)),
            mapsto_txn γUnified a v0
        else
          mapsto_txn γUnified a (projT2 v) )
  )%I.

Theorem wp_buftxn_Begin l γUnified :
  {{{ is_txn l γUnified
  }}}
    Begin #l
  {{{ (buftx : loc) γt, RET #buftx;
      is_buftxn buftx γt γUnified
  }}}.
Proof using gen_heapPreG0.
  iIntros (Φ) "Htxn HΦ".

  wp_call.
  wp_apply (wp_MkBufMap with "[$]").
  iIntros (bufmap) "Hbufmap".
  iDestruct (is_txn_dup with "Htxn") as "[Htxn Htxn0]".
  wp_apply (wp_Txn__GetTransId with "Htxn0").
  iIntros (tid) "Htid".
  wp_apply wp_allocStruct; eauto.
  iIntros (buftx) "Hbuftx".
  iDestruct (struct_fields_split with "Hbuftx") as "(Hbuftx.txn & Hbuftx.bufs & Hbuftx.id & %)".
  wp_apply util_proof.wp_DPrintf.
  iMod (gen_heap_init ∅) as (γt) "Htxctx".
  wp_pures.
  iApply "HΦ".
  iExists _, _, _, _, _.
  iFrame.
  rewrite big_sepM_empty. iFrame.
  iSplit. { iApply big_sepM_empty. done. }
  iApply big_sepM_empty. done.

  Unshelve. all: eauto. (* XXX why? *)
Qed.

Theorem wp_BufTxn__ReadBuf buftx γt γUnified a sz v :
  {{{
    is_buftxn buftx γt γUnified ∗
    mapsto (hG := γt) a 1 v ∗
    ⌜ sz = bufSz (projT1 v) ⌝
  }}}
    BufTxn__ReadBuf #buftx (addr2val a) #sz
  {{{
    (bufptr : loc) dirty, RET #bufptr;
    is_buf bufptr a (Build_buf (projT1 v) (projT2 v) dirty) ∗
    ( ∀ v' dirty',
      ( ⌜ dirty' = true ∨ (dirty' = dirty ∧ projT2 v = v') ⌝ ∗
        is_buf bufptr a (Build_buf (projT1 v) v' dirty') ) ==∗
      ( mapsto (hG := γt) a 1 (existT _ v') ∗
        is_buftxn buftx γt γUnified ) )
  }}}.
Proof using gen_heapPreG0.
  iIntros (Φ) "(Htxn & Ha & ->) HΦ".
  iDestruct "Htxn" as (l mT bufmap gBufmap txid)
    "(Hl & Hbufmap & Htxid & Htxn & Hisbufmap & Hγtctx & Hbufmapt & Hvalid & Hm)".
  iDestruct (gen_heap_valid with "Hγtctx Ha") as %HmT_a2.
  iDestruct (big_sepM_lookup with "Hvalid") as "%"; eauto.
  wp_call.
  wp_loadField.
  wp_apply (wp_BufMap__Lookup with "[$Hisbufmap]"); eauto.
  iIntros (bufptr) "Hbufptr".
  wp_pures.
  destruct (gBufmap !! a) eqn:Hbufmap_a.
  - iDestruct "Hbufptr" as "[Hbufptr Hisbufmap]".
    iDestruct (is_buf_not_null with "Hbufptr") as %Hbufptr_not_null.

    iDestruct (big_sepM_lookup with "Hbufmapt") as %HmT_a; eauto.
    rewrite HmT_a2 in HmT_a.
    inversion HmT_a; clear HmT_a; subst.
    destruct b; rewrite /=.

    wp_if_destruct; try congruence.
    iApply "HΦ".
    iFrame "Hbufptr".

    iIntros (v' dirty') "[% Hbufptr]".
    iDestruct ("Hisbufmap" with "Hbufptr") as "Hisbufmap".
    intuition idtac.
    + subst.
      iMod (gen_heap_update with "Hγtctx Ha") as "[Hγtctx Ha]".
      iFrame "Ha".
      iModIntro.
      iExists _, _, _, _, _.
      iFrame.
      iDestruct (big_sepM_lookup with "Hbufmapt") as %HmT_a; eauto.
      iSplitL "Hbufmapt".
      {
        iDestruct (big_sepM_forall with "Hbufmapt") as "Hbufmapt".
        iApply big_sepM_forall.
        iIntros (k x).
        destruct (decide (a = k)).
        { subst. repeat rewrite lookup_insert.
          iPureIntro; intros. inversion H0; subst; clear H0.
          simpl; eauto. }
        { repeat rewrite -> lookup_insert_ne by eauto.
          eauto. }
      }

      iSplitL "Hvalid".
      {
        iDestruct (big_sepM_insert_acc with "Hvalid") as "[Ha Hvalid]"; eauto.
        iApply "Hvalid"; eauto.
      }

      iDestruct (big_sepM_delete with "Hm") as "[Hma Hm]"; eauto.
      iApply big_sepM_insert_delete.
      iSplitL "Hma".
      { rewrite lookup_insert. rewrite Hbufmap_a /=.
        destruct bufDirty; eauto. }
      iApply (big_sepM_mono with "Hm").
      iIntros (k x Hkx) "Hk".
      destruct (decide (a = k)).
      { subst. rewrite lookup_delete in Hkx. congruence. }
      rewrite -> lookup_insert_ne by eauto.
      destruct (gBufmap !! k); eauto.

    + subst.
      iFrame "Ha".
      iModIntro.
      iExists _, _, _, _, _.
      iFrame.
      iDestruct (big_sepM_lookup with "Hbufmapt") as %HmT_a; eauto.
      iSplitL "Hbufmapt".
      {
        iDestruct (big_sepM_forall with "Hbufmapt") as "Hbufmapt".
        iApply big_sepM_forall.
        iIntros (k x).
        destruct (decide (a = k)).
        { subst. repeat rewrite lookup_insert.
          iPureIntro; intros. inversion H0; subst; clear H0.
          simpl; eauto. }
        { repeat rewrite -> lookup_insert_ne by eauto.
          eauto. }
      }

      rewrite insert_id; eauto.

  - iDestruct "Hbufptr" as "[-> Hbufptr]".
    wp_if_destruct.
    2: congruence.

    wp_loadField.
    iDestruct (big_sepM_lookup_acc with "Hm") as "[Hma Hm]"; eauto.
    rewrite Hbufmap_a /=.

    iDestruct (is_txn_dup with "Htxn") as "[Htxn Htxn2]".
    wp_apply (wp_txn_Load with "[$Htxn $Hma]").
    iIntros (bufptr b) "(Hbuf & % & % & Hma)".
    wp_pures.
    iDestruct ("Hm" with "Hma") as "Hm".

    wp_loadField.
    wp_apply (wp_BufMap__Insert with "[$Hbufptr $Hbuf]").
    iIntros "Hbufptr".

    wp_loadField.
    wp_apply (wp_BufMap__Lookup with "[$Hbufptr]"); eauto.
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
      iMod (gen_heap_update with "Hγtctx Ha") as "[Hγtctx Ha]".
      iFrame "Ha".
      iModIntro.
      iExists _, _, _, _, _.
      iFrame.

      rewrite insert_insert.
      iSplitL "Hbufmapt".
      {
        iApply (big_sepM_insert); eauto.
        iSplitR.
        { rewrite lookup_insert. eauto. }
        iApply (big_sepM_mono with "Hbufmapt").
        iIntros (k x0) "% %". iPureIntro.
        destruct (decide (a = k)).
        { subst; congruence. }
        repeat rewrite -> lookup_insert_ne by eauto.
        eauto.
      }

      iSplitL "Hvalid".
      {
        iDestruct (big_sepM_insert_acc with "Hvalid") as "[Ha Hvalid]"; eauto.
        iApply "Hvalid"; eauto.
      }

      iDestruct (big_sepM_delete with "Hm") as "[Hma Hm]"; eauto.
      iApply big_sepM_insert_delete.
      iSplitL "Hma".
      { rewrite lookup_insert. rewrite Hbufmap_a /=.
        iExists _; iFrame. }
      iApply (big_sepM_mono with "Hm").
      iIntros (k x0 Hkx0) "Hk".
      destruct (decide (a = k)).
      { subst. rewrite lookup_delete in Hkx0. congruence. }
      rewrite -> lookup_insert_ne by eauto.
      destruct (gBufmap !! k); eauto.

    + subst.
      iFrame "Ha".
      iModIntro.
      iExists _, _, _, _, _.
      iFrame.

      rewrite insert_insert.
      iSplitL "Hbufmapt".
      {
        iApply (big_sepM_insert); eauto.
      }

      iApply (big_sepM_mono with "Hm").
      iIntros (k x0 Hkx0) "Hk".
      destruct (decide (a = k)).
      { subst. rewrite lookup_insert. rewrite Hbufmap_a.
        simpl. eauto. }
      rewrite -> lookup_insert_ne by eauto.
      destruct (gBufmap !! k); eauto.
Qed.

Theorem wp_BufTxn__OverWrite buftx γt γUnified a v0 v (sz : u64) (vslice : Slice.t) :
  {{{
    is_buftxn buftx γt γUnified ∗
    mapsto (hG := γt) a 1 v0 ∗
    is_buf_data vslice (projT2 v) a ∗
    ⌜ sz = bufSz (projT1 v) ⌝ ∗
    ⌜ projT1 v = projT1 v0 ⌝
  }}}
    BufTxn__OverWrite #buftx (addr2val a) #sz (slice_val vslice)
  {{{
    RET #();
    is_buftxn buftx γt γUnified ∗
    mapsto (hG := γt) a 1 v
  }}}.
Proof using.
  iIntros (Φ) "(Htxn & Ha & Hvslice & -> & %) HΦ".
Opaque struct.t.
  wp_call.
  iDestruct "Htxn" as (l mT bufmap gBufmap txid)
    "(Hl & Hbufmap & Htxid & Htxn & Hisbufmap & Hγtctx & Hbufmapt & Hvalid & Hm)".
  iDestruct (gen_heap_valid with "Hγtctx Ha") as %HmT_a2.
  iDestruct (big_sepM_lookup with "Hvalid") as "%"; eauto.

  wp_loadField.
  wp_apply (wp_BufMap__Lookup with "[$Hisbufmap]"); eauto.
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
    iDestruct (big_sepM_lookup with "Hbufmapt") as %HmT_a; eauto.
    rewrite HmT_a2 in HmT_a; inversion HmT_a; subst.
    rewrite /=.
    wp_pures.
    destruct (bool_decide (#(bufSz b0.(bufKind)) = #(bufSz b0.(bufKind)))) eqn:He.
    2: { apply bool_decide_eq_false_1 in He; congruence. }
    wp_pures.
    wp_load.
    wp_apply (wp_buf_storeField_data with "[$Hisbuf $Hvslice]"); eauto.
    iIntros "Hisbuf".

    iMod (gen_heap_update with "Hγtctx Ha") as "[Hγtctx Ha]".

    wp_pures.
    wp_load.
    wp_apply (wp_Buf__SetDirty with "Hisbuf"); iIntros "Hisbuf".
    iApply "HΦ".
    iFrame.

    iDestruct ("Hisbufmap" with "Hisbuf") as "Hisbufmap".

    iExists _, _, _, _, _.
    iFrame.
    rewrite /=.

    iSplitL "Hbufmapt".
    {
      iApply (big_sepM_insert_delete).
      iSplitR.
      { rewrite lookup_insert. destruct v. auto. }
      iDestruct (big_sepM_delete with "Hbufmapt") as "[_ Hbufmapt]"; eauto.
      iApply (big_sepM_mono with "Hbufmapt").
      iIntros (k x0) "% %". iPureIntro.
      destruct (decide (a = k)).
      { subst. rewrite lookup_delete in H2. congruence. }
      repeat rewrite -> lookup_insert_ne by eauto.
      eauto.
    }

    iSplitL "Hvalid".
    {
      iDestruct (big_sepM_insert_acc with "Hvalid") as "[Ha Hvalid]"; eauto.
      iApply "Hvalid"; eauto.
    }

    iDestruct (big_sepM_delete with "Hm") as "[Hma Hm]"; eauto.
    iApply big_sepM_insert_delete.
    iSplitL "Hma".
    { rewrite lookup_insert. rewrite Hbufmap_a /=.
      destruct (b0.(bufDirty)).
      { iDestruct "Hma" as (v0) "Hma". iExists _; iFrame. admit. }
      iExists _; iFrame. admit.
    }
    iApply (big_sepM_mono with "Hm").
    iIntros (k x0 Hkx0) "Hk".
    destruct (decide (a = k)).
    { subst. rewrite lookup_delete in Hkx0. congruence. }
    rewrite -> lookup_insert_ne by eauto.
    destruct (gBufmap !! k); eauto.

  - iDestruct "Hbufmapptr" as "[-> Hisbufmap]".
    wp_load.
    wp_pures.
    wp_apply (wp_MkBuf with "[$Hvslice]"); eauto.
    iIntros (bufptr) "Hisbuf".
    wp_pures.
    wp_store.
    wp_pures.
    wp_load.
    wp_apply (wp_Buf__SetDirty with "Hisbuf"); iIntros "Hisbuf".
    wp_load.
    wp_loadField.

    iMod (gen_heap_update with "Hγtctx Ha") as "[Hγtctx Ha]".

    wp_apply (wp_BufMap__Insert with "[$Hisbufmap $Hisbuf]").
    iIntros "Hisbufmap".
    iApply "HΦ".
    iFrame "Ha".

    iExists _, _, _, _, _.
    iFrame.
    rewrite /=.

    iSplitL "Hbufmapt".
    {
      iApply (big_sepM_insert); eauto.
      iSplitR.
      { rewrite lookup_insert. destruct v. auto. }
      iApply (big_sepM_mono with "Hbufmapt").
      iIntros (k x0) "% %". iPureIntro.
      destruct (decide (a = k)).
      { subst. congruence. }
      repeat rewrite -> lookup_insert_ne by eauto.
      eauto.
    }

    iSplitL "Hvalid".
    {
      iDestruct (big_sepM_insert_acc with "Hvalid") as "[Ha Hvalid]"; eauto.
      iApply "Hvalid"; eauto.
    }

    iDestruct (big_sepM_delete with "Hm") as "[Hma Hm]"; eauto.
    iApply big_sepM_insert_delete.
    iSplitL "Hma".
    { rewrite lookup_insert. rewrite Hbufmap_a /=.
      iExists _. iFrame. admit.
    }
    iApply (big_sepM_mono with "Hm").
    iIntros (k x0 Hkx0) "Hk".
    destruct (decide (a = k)).
    { subst. rewrite lookup_delete in Hkx0. congruence. }
    rewrite -> lookup_insert_ne by eauto.
    destruct (gBufmap !! k); eauto.
Admitted.

Theorem BufTxn_lift_one buftx γt γUnified a v :
  (
    is_buftxn buftx γt γUnified ∗
    mapsto_txn γUnified a (projT2 v)
  )
    ==∗
  (
    is_buftxn buftx γt γUnified ∗
    mapsto (hG := γt) a 1 v
  ).
Proof.
  iIntros "[Htxn Ha]".
  iDestruct "Htxn" as (l mT bufmap gBufmap txid)
    "(Hl & Hbufmap & Htxid & Htxn & Hisbufmap & Hγtctx & Hbufmapt & Hvalid & Hm)".

  iAssert (⌜ mT !! a = None ⌝)%I as %Hnone.
  {
    destruct (mT !! a) eqn:He; eauto.
    iDestruct (big_sepM_lookup with "Hm") as "Ha2"; eauto.
    destruct (gBufmap !! a); rewrite /=.
    { destruct b.(bufDirty).
      { iDestruct "Ha2" as (v0) "Ha2".
        (*
        iDestruct (mapsto_txn_2 with "Ha Ha2") as %Hfalse.
        exfalso; eauto.
        *)
        admit. }
      { (*
        iDestruct (mapsto_txn_2 with "Ha Ha2") as %Hfalse.
        exfalso; eauto.
        *)
        admit. }
    }
    { (*
      iDestruct (mapsto_txn_2 with "Ha Ha2") as %Hfalse.
      exfalso; eauto.
      *)
      admit. }
  }

  iAssert (⌜ gBufmap !! a = None ⌝)%I as %Hgnone.
  {
    destruct (gBufmap !! a) eqn:He; eauto.
    iDestruct (big_sepM_lookup with "Hbufmapt") as %Ha2; eauto.
    rewrite Ha2 in Hnone; congruence.
  }

  iDestruct (mapsto_txn_valid with "Ha") as %Havalid.

  iMod ((gen_heap_alloc _ _ v) with "Hγtctx") as "[Hγtctx Haa]"; eauto.
  iModIntro.
  iSplitR "Haa"; [|iFrame].

  iExists _, _, _, _, _.
  iFrame.
  iSplitL "Hbufmapt".
  { iApply big_sepM_mono; iFrame.
    iPureIntro; simpl; intros.
    destruct (decide (a = x)); subst.
    { rewrite Hnone in H. congruence. }
    rewrite -> lookup_insert_ne by eauto. eauto.
  }

  iSplitL "Hvalid".
  { iApply big_sepM_insert; eauto. }

  iApply (big_sepM_insert); eauto.
  iFrame.
  rewrite Hgnone. iFrame.
Admitted.

Theorem BufTxn_lift buftx γt γUnified (m : gmap addr (sigT _)) :
  (
    is_buftxn buftx γt γUnified ∗
    [∗ map] a ↦ v ∈ m, mapsto_txn γUnified a (projT2 v)
  )
    ==∗
  (
    is_buftxn buftx γt γUnified ∗
    [∗ map] a ↦ v ∈ m, mapsto (hG := γt) a 1 v
  ).
Proof.
  iIntros "[Htxn Ha]".
  iDestruct "Htxn" as (l mT bufmap gBufmap txid)
    "(Hl & Hbufmap & Htxid & Htxn & Hisbufmap & Hγtctx & Hbufmapt & Hvalid & Hm)".

  iDestruct (big_sepM_disjoint_pred with "Hm Ha") as %Hd.
  {
    unfold Conflicting; intros.
    iIntros "Hm1 Hm2".
    destruct (gBufmap !! a0).
    { destruct (b.(bufDirty)).
      { iDestruct "Hm1" as (?) "Hm1".
        iDestruct (mapsto_txn_2 with "[$Hm1] [Hm2]") as %Hd; eauto.
        admit. }
      { iDestruct (mapsto_txn_2 with "[$Hm1] [Hm2]") as %Hd; eauto.
        admit. }
    }
    { iDestruct (mapsto_txn_2 with "[$Hm1] [Hm2]") as %Hd; eauto.
      admit. }
  }

  iMod (gen_heap_alloc_gen with "Hγtctx") as "[Hγtctx Haa]"; eauto.
  iModIntro.
  iSplitR "Haa"; last iFrame.

  iExists _, _, _, _, _.
  iFrame.

  iDestruct (big_sepM_mono _ (fun a v => mapsto_txn γUnified a (projT2 v) ∗ ⌜ valid_addr a ⌝)%I with "Ha") as "Ha".
  { iIntros (???) "H".
    iDestruct (mapsto_txn_valid with "H") as %Hv; iFrame; done. }
  iDestruct (big_sepM_sep with "Ha") as "[Ha Havalid]".

  iSplitL "Hbufmapt".
  { iApply big_sepM_mono; iFrame.
    iPureIntro; simpl; intros.
    erewrite lookup_union_Some_r; eauto.
  }

  iSplitL "Hvalid Havalid".
  { iApply big_sepM_union; eauto. }

  iApply big_sepM_union; eauto.
  iFrame.
  iApply big_sepM_mono; last iFrame.
  iIntros (???) "H".
  (* prove that gBufmap!!k=None for all k∈m *)
  admit.
Admitted.

Theorem BufTxn_lift_pred `{!Liftable P} buftx γt γUnified :
  (
    is_buftxn buftx γt γUnified ∗
    P (fun a v => mapsto_txn γUnified a (projT2 v))
  )
    ==∗
  (
    is_buftxn buftx γt γUnified ∗
    P (fun a v => mapsto (hG := γt) a 1 v)
  ).
Proof.
  iIntros "(Htxn & Hp)".
  unfold Liftable in Liftable0.
  iDestruct (Liftable0 with "Hp") as (m) "[Hm Hp]".
  { iIntros (a0 v0 a1 v1) "Ha0 Ha1".
    destruct (decide (a0 = a1)); subst; eauto.
    iDestruct (mapsto_txn_2 with "Ha0 [Ha1]") as %Hf; eauto.
    admit. }
  iMod (BufTxn_lift with "[$Htxn $Hm]") as "[Htxn Hm]".
  iFrame.
  iApply "Hp".
  iFrame.
  done.
Admitted.

Theorem wp_BufTxn__CommitWait buftx γt γUnified mods :
  {{{
    is_buftxn buftx γt γUnified ∗
    [∗ map] a ↦ v ∈ mods, mapsto (hG := γt) a 1 v
  }}}
    BufTxn__CommitWait #buftx #true
  {{{
    RET #();
    [∗ map] a ↦ v ∈ mods, mapsto_txn γUnified a (projT2 v)
  }}}.
Proof.
  iIntros (Φ) "(Htxn & Hmods) HΦ".
Admitted.

Theorem wp_BufTxn__CommitWait_pred `{!Liftable P} buftx γt γUnified :
  {{{
    is_buftxn buftx γt γUnified ∗
    P (fun a v => mapsto (hG := γt) a 1 v)
  }}}
    BufTxn__CommitWait #buftx #true
  {{{
    RET #();
    P (fun a v => mapsto_txn γUnified a (projT2 v))
  }}}.
Proof.
  iIntros (Φ) "(Htxn & Hp) HΦ".
  unfold Liftable in Liftable0.
  iDestruct (Liftable0 with "Hp") as (m) "[Hm Hp]".
  { iIntros (a0 v0 a1 v1) "Ha0 Ha1".
    destruct (decide (a0 = a1)); subst; eauto.
    iDestruct (mapsto_valid_2 with "Ha0 Ha1") as %Hf; eauto. }
  wp_apply (wp_BufTxn__CommitWait with "[$Htxn $Hm]").
  iIntros "Hm".
  iApply "HΦ".
  iApply "Hp".
  iFrame.
Qed.

End heap.
