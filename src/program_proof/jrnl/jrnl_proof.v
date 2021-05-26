From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.algebra Require Import log_heap liftable.
From Perennial.base_logic Require Import lib.mono_nat.
From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import disk_prelude.

From Goose.github_com.mit_pdos.go_journal Require Import addr jrnl.
From Perennial.program_proof Require Import wal.specs wal.heapspec obj.obj_proof buf.buf_proof addr.addr_proof.

From Perennial.program_logic Require Import invariants_mutable.
From Perennial.program_proof Require wp_to_wpc.

Definition mkVersioned {K:bufDataKind} (c m: bufDataT K) : versioned_object :=
  existT K (c, m).

Instance object_eq_dec : EqDecision object.
Proof.
  intros o1 o2.
  destruct o1 as [K1 x1], o2 as [K2 x2].
  destruct (decide (K1 = K2)).
  - destruct e.
    destruct (decide (x1 = x2)); subst.
    + left; auto.
    + right.
      intro H.
      apply Eqdep_dec.inj_pair2_eq_dec in H; auto.
      intros. apply bufDataKind_eq_dec.
  - right; intros H%eq_sigT_fst; auto.
Qed.

Instance versioned_object_eq_dec : EqDecision versioned_object.
Proof.
  intros o1 o2.
  destruct o1 as [K1 cm1], o2 as [K2 cm2].
  destruct (decide (K1 = K2)); subst.
  - destruct (decide (cm1 = cm2)); subst.
    + left; auto.
    + right.
      intro H.
      apply Eqdep_dec.inj_pair2_eq_dec in H; auto.
      intros. apply bufDataKind_eq_dec.
  - right; intros H%eq_sigT_fst; auto.
Qed.

Definition committed (v : versioned_object) : object :=
  existT _ (fst (projT2 v)).

Definition modified (v : versioned_object) : object :=
  existT _ (snd (projT2 v)).

Lemma committed_mkVersioned {K} c m : committed (@mkVersioned K c m) = existT K c.
Proof. reflexivity. Qed.

Lemma modified_mkVersioned {K} c m : modified (@mkVersioned K c m) = existT K m.
Proof. reflexivity. Qed.

Class jrnlG Σ :=
  { jrnl_txn   :> txnG Σ;
  }.

Definition jrnlΣ : gFunctors :=
  #[ txnΣ ].

Instance subG_jrnlΣ Σ : subG jrnlΣ Σ → jrnlG Σ.
Proof. solve_inG. Qed.

Section heap.
Context `{!jrnlG Σ}.
Context `{!heapGS Σ}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).
Implicit Types (mT : gmap addr versioned_object).

Definition is_jrnl (buftx : loc)
                     mT
                     γUnified
                     dinit anydirty : iProp Σ :=
  (
    ∃ (l : loc) (bufmap : loc) (gBufmap : gmap addr buf),
      "Hbuftx.l" ∷ buftx ↦[jrnl.Op :: "log"] #l ∗
      "Hbuftx.map" ∷ buftx ↦[jrnl.Op :: "bufs"] #bufmap ∗
      "#Histxn" ∷ is_txn l γUnified dinit ∗
      "Hbufmap" ∷ is_bufmap bufmap gBufmap ∗
      "%Hbufmapelem" ∷ ⌜ (λ b, existT _ (bufData b)) <$> gBufmap ⊆ modified <$> mT ⌝ ∗
      "#Hctxvalid" ∷ ( [∗ map] a ↦ v ∈ mT,
        ⌜ valid_addr a ∧ valid_off (projT1 v) a.(addrOff) ⌝ ) ∗
      "Hctxelem" ∷ ( [∗ map] a ↦ v ∈ mT,
        mapsto_txn γUnified a (committed v) ∗
        let dirty := match gBufmap !! a with
                     | None => false
                     | Some buf => bufDirty buf
                     end in
        ⌜dirty=true ∨ committed v = modified v⌝ ) ∗
      "%Hanydirty" ∷ ⌜anydirty=false <-> filter (λ b, (snd b).(bufDirty) = true) gBufmap = ∅⌝
  )%I.

Lemma is_jrnl_to_committed_mapsto_txn buftx mT γUnified dinit anydirty :
  is_jrnl buftx mT γUnified dinit anydirty -∗
  [∗ map] a ↦ v ∈ committed <$> mT, mapsto_txn γUnified a v.
Proof.
  iNamed 1.
  rewrite big_sepM_fmap.
  iApply (big_sepM_mono with "Hctxelem").
  iIntros (a obj Hlookup) "[Ha _]". iFrame.
Qed.

Lemma is_jrnl_not_in_map buftx mT γUnified dinit anydirty a v0 :
  is_jrnl buftx mT γUnified dinit anydirty -∗
  mapsto_txn γUnified a v0 -∗
  ⌜mT !! a = None⌝.
Proof.
  rewrite is_jrnl_to_committed_mapsto_txn.
  iIntros "Hm Ha".
  destruct (mT !! a) eqn:Helem; eauto.
  iExFalso.
  iDestruct (big_sepM_lookup _ _ a with "Hm") as "Ha2".
  { rewrite lookup_fmap Helem //. }
  iDestruct (mapsto_txn_2 with "Ha Ha2") as %[].
Qed.

Theorem wp_jrnl_Begin l γUnified dinit:
  {{{ is_txn l γUnified dinit
  }}}
    jrnl.Begin #l
  {{{ (buftx : loc), RET #buftx;
      is_jrnl buftx ∅ γUnified dinit false
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
  iExists _, _, _.
  iFrame. iModIntro.
  rewrite big_sepM_empty. iFrame "Htxn ∗".
  iSplit; first by done.
  rewrite left_id.
  rewrite big_sepM_empty //.
Qed.

Theorem wp_Op__ReadBuf buftx mT γUnified dinit anydirty a (sz : u64) v :
  {{{
    is_jrnl buftx mT γUnified dinit anydirty ∗
    ⌜ mT !! a = Some v ⌝ ∗
    ⌜ sz = bufSz (projT1 v) ⌝
  }}}
    Op__ReadBuf #buftx (addr2val a) #sz
  {{{
    (bufptr : loc) dirty, RET #bufptr;
    is_buf bufptr a (Build_buf (projT1 v) (snd (projT2 v)) dirty) ∗
    ( ∀ v' dirty',
      ( ⌜ dirty' = true ∨ (dirty' = dirty ∧ snd (projT2 v) = v') ⌝ ∗
        is_buf bufptr a (Build_buf (projT1 v) v' dirty') ) ==∗
      ( is_jrnl buftx (<[a := existT _ (fst (projT2 v), v')]> mT) γUnified dinit (orb anydirty dirty') ) )
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
  wp_if_destruct.
  - destruct (gBufmap !! a) eqn:Hbufmap_a.
    {
      iDestruct "Hbufptr" as "[Hbufptr Hisbufmap]".
      iDestruct (is_buf_not_null with "Hbufptr") as %Hbufptr_not_null. congruence.
    }

    iDestruct "Hbufptr" as "[_ Hbufptr]".

    wp_loadField.
    iDestruct (big_sepM_lookup_acc with "Hctxelem") as "[[Hma %Hma] Hctxelem]"; eauto.
    rewrite Hbufmap_a /= in Hma. intuition try congruence.

    wp_apply (wp_txn_Load with "[$Histxn $Hma]").
    iIntros (bufptr b) "(Hbuf & % & % & Hma)".
    wp_pures.
    iDestruct ("Hctxelem" with "[Hma]") as "Hctxelem".
    { iFrame. rewrite Hbufmap_a. iPureIntro. intuition. }

    wp_loadField.
    wp_apply (wp_BufMap__Insert with "[$Hbufptr $Hbuf]").
    iIntros "Hbufptr".

    wp_loadField.
    wp_apply (wp_BufMap__Lookup with "[$Hbufptr]"); intuition.
    iIntros (bufptr2) "Hbufptr2".

    rewrite lookup_insert.
    iDestruct "Hbufptr2" as "[Hbufptr2 Hisbufmap]".

    destruct b, v, p. simpl in *. subst.
    unfold committed, modified in *. simpl in *.

    apply eq_sigT_eq_dep in H3.
    apply Eqdep_dec.eq_dep_eq_dec in H3.
    2: apply bufDataKind_eq_dec.

    inversion H5; clear H5; subst.
    apply eq_sigT_eq_dep in H7.
    apply Eqdep_dec.eq_dep_eq_dec in H7.
    2: apply bufDataKind_eq_dec.

    subst.

    iApply "HΦ".
    iFrame "Hbufptr2".

    iIntros (v' dirty') "[% Hbufptr]".
    iDestruct ("Hisbufmap" with "Hbufptr") as "Hisbufmap".

    rewrite insert_insert.
    iDestruct (big_sepM_delete with "Hctxvalid") as "[Ha Hctxvalid2]"; eauto.
    iDestruct (big_sepM_delete with "Hctxelem") as "[[He %He] Hctxelem]"; eauto. rewrite Hbufmap_a /= in He.

    intuition try congruence; subst.
    + iModIntro.
      iExists _, _, _.
      iFrame. iFrame "#".
      iSplit.
      { iPureIntro.
        rewrite ?fmap_insert /modified /=.
        eapply insert_mono; eauto.
      }
      iSplit.
      { iApply big_sepM_insert_delete; iFrame "#". }
      iSplit.
      {
        iApply big_sepM_insert_delete.
        rewrite lookup_insert /=.
        iSplitL "He". { iFrame. iPureIntro; eauto. }
        iApply big_sepM_mono; try iFrame.
        iIntros (xa xb Hb) "H".
        destruct (decide (a = xa)); subst.
        { rewrite lookup_delete in Hb. congruence. }
        rewrite lookup_insert_ne; eauto.
      }
      iPureIntro.
      split; intro Hx.
      { destruct anydirty; simpl in *; congruence. }
      rewrite map_filter_insert in Hx; last eauto.
      eapply insert_non_empty in Hx. exfalso; eauto.

    + iModIntro.
      iExists _, _, _.
      iFrame. iFrame "#".

      iSplit.
      { iPureIntro.
        rewrite ?fmap_insert /=.
        eapply insert_mono; eauto.
      }
      iSplit.
      { iApply big_sepM_insert_delete; iFrame "#". }
      iSplit.
      {
        iApply big_sepM_insert_delete.
        rewrite lookup_insert /=.
        iSplitL "He". { iFrame. iPureIntro. intuition congruence. }
        iApply big_sepM_mono; try iFrame.
        iIntros (xa xb Hb) "H".
        destruct (decide (a = xa)); subst.
        { rewrite lookup_delete in Hb. congruence. }
        rewrite lookup_insert_ne; eauto.
      }
      iPureIntro.
      split; intro Hx.
      { destruct anydirty; simpl in *; try congruence.
        rewrite map_filter_insert_not'; eauto.
        simpl; intros y Hy Htrue.
        assert (filter (λ (b : addr * buf), (b.2).(bufDirty) = true) gBufmap !! a = Some y) as Hz.
        { eapply map_filter_lookup_Some_2; eauto. }
        rewrite H in Hz; eauto. congruence. }
      destruct anydirty; simpl; try reflexivity.
      rewrite map_filter_insert_not_delete in Hx; last eauto.
      rewrite delete_notin in Hx; eauto.

  - destruct (gBufmap !! a) eqn:Hbufmap_a.
    2: {
      iDestruct "Hbufptr" as "[% _]". congruence.
    }

    eapply map_subseteq_spec in Hbufmapelem as Ha'.
    2: {
      rewrite lookup_fmap. erewrite Hbufmap_a. rewrite /=. reflexivity.
    }
    rewrite lookup_fmap Ha in Ha'. inversion Ha'; clear Ha'; subst.
    destruct b; simpl in *; subst.

    apply eq_sigT_eq_dep in H2.
    apply Eqdep_dec.eq_dep_eq_dec in H2.
    2: apply bufDataKind_eq_dec.
    subst.

    iDestruct "Hbufptr" as "[Hbufptr Hisbufmap]".
    iApply "HΦ". iModIntro.
    iFrame "Hbufptr".

    iIntros (v' dirty') "[% Hbufptr]".
    iDestruct ("Hisbufmap" with "Hbufptr") as "Hisbufmap".

    iDestruct (big_sepM_delete with "Hctxvalid") as "[Ha Hctxvalid2]"; eauto.
    iDestruct (big_sepM_delete with "Hctxelem") as "[[He #Hepure] Hctxelem]"; eauto.

    intuition idtac; subst.
    + iModIntro.
      iExists _, _, _.
      iFrame "# ∗".

      iSplit.
      { iPureIntro.
        rewrite ?fmap_insert /modified /=.
        eapply insert_mono; eauto.
      }
      iSplit.
      { iApply big_sepM_insert_delete; iFrame "#". }
      iSplit.
      {
        iApply big_sepM_insert_delete.
        rewrite lookup_insert /=.
        iSplitL "He". { iFrame. iPureIntro. rewrite /committed /modified /=. intuition eauto. }
        iApply big_sepM_mono; try iFrame.
        iIntros (xa xb Hb) "H".
        destruct (decide (a = xa)); subst.
        { rewrite lookup_delete in Hb. congruence. }
        rewrite lookup_insert_ne; eauto.
      }
      iPureIntro.
      split; intro Hx.
      { destruct anydirty; simpl in *; congruence. }
      rewrite map_filter_insert in Hx; last eauto.
      eapply insert_non_empty in Hx. exfalso; eauto.

    + iModIntro.
      iExists _, _, _.
      iFrame "# ∗".

      iSplit.
      { iPureIntro.
        rewrite ?fmap_insert /=.
        eapply insert_mono; eauto.
      }
      iSplit.
      { iApply big_sepM_insert_delete; iFrame "#". }
      iSplit.
      {
        iApply big_sepM_insert_delete.
        rewrite lookup_insert /=.
        iSplitL "He". { iFrame. iDestruct "Hepure" as %He. rewrite Hbufmap_a /= in He. iPureIntro. rewrite /committed /modified /=. intuition idtac. }
        iApply big_sepM_mono; try iFrame.
        iIntros (xa xb Hb) "H".
        destruct (decide (a = xa)); subst.
        { rewrite lookup_delete in Hb. congruence. }
        rewrite lookup_insert_ne; eauto.
      }
      iPureIntro.
      split; intro Hx.
      { destruct anydirty; simpl in *; try congruence. subst.
        rewrite map_filter_insert_not'; eauto.
        simpl; intros y Hy Htrue.
        assert (filter (λ (b : addr * buf), (b.2).(bufDirty) = true) gBufmap !! a = Some y) as Hz.
        { eapply map_filter_lookup_Some_2; eauto. }
        rewrite H in Hz; eauto. inversion Hz. }
      destruct anydirty; simpl.
      {
        exfalso.
        destruct bufDirty.
        {
          rewrite map_filter_insert in Hx; eauto.
          eapply insert_non_empty in Hx; eauto.
        }
        rewrite map_filter_insert_not' in Hx; eauto.
        { eapply H3 in Hx; congruence. }
        intros y Hy. rewrite Hbufmap_a in Hy. inversion Hy; subst. eauto.
      }
      destruct bufDirty; try reflexivity. exfalso.
      rewrite map_filter_insert in Hx; eauto.
      eapply insert_non_empty in Hx; eauto.
Qed.

Theorem wp_Op__OverWrite buftx mt γUnified dinit a v0 (v : {K & (bufDataT K * bufDataT K)%type}) (sz : u64) (vslice : Slice.t) anydirty :
  {{{
    is_jrnl buftx mt γUnified dinit anydirty ∗
    ⌜ mt !! a = Some v0 ⌝ ∗
    is_buf_data vslice (snd (projT2 v)) a ∗
    ⌜ sz = bufSz (projT1 v) ⌝ ∗
    ⌜ existT (projT1 v) (fst (projT2 v)) = existT (projT1 v0) (fst (projT2 v0)) ⌝
  }}}
    Op__OverWrite #buftx (addr2val a) #sz (slice_val vslice)
  {{{
    RET #();
    is_jrnl buftx (<[a := v]> mt) γUnified dinit true
  }}}.
Proof using.
  iIntros (Φ) "(Htxn & %Ha & Hvslice & -> & %) HΦ".
Opaque struct.t.
  wp_call.
  iNamed "Htxn".
  iDestruct (big_sepM_lookup with "Hctxvalid") as "%"; eauto.

  wp_loadField.
  wp_apply (wp_BufMap__Lookup with "[$Hbufmap]"); intuition.
  iIntros (bufptr) "Hbufmapptr".

  wp_apply wp_ref_to; first by eauto.
  iIntros (b) "Hb".
  wp_pures.

  destruct v, p.
  inversion H; subst.
  apply eq_sigT_eq_dep in H6.
  apply Eqdep_dec.eq_dep_eq_dec in H6.
  2: apply bufDataKind_eq_dec.
  subst.

  destruct (gBufmap !! a) eqn:Hbufmap_a.
  - iDestruct "Hbufmapptr" as "[Hisbuf Hisbufmap]".
    iDestruct (is_buf_not_null with "Hisbuf") as "%".
    wp_load.
    wp_pures.
    destruct (bool_decide (#bufptr = #null)) eqn:Hbooldec.
    { apply bool_decide_eq_true_1 in Hbooldec; congruence. }
    wp_pures.
    wp_load.
    wp_apply (wp_buf_loadField_sz with "Hisbuf"); iIntros "Hisbuf".

    eapply map_subseteq_spec in Hbufmapelem as Ha'.
    2: {
      rewrite lookup_fmap. erewrite Hbufmap_a. rewrite /=. reflexivity.
    }
    rewrite lookup_fmap Ha in Ha'. inversion Ha'; clear Ha'; subst.
    destruct b0; simpl in *.

    wp_pures.
    destruct (bool_decide (#(bufSz (projT1 v0)) = #(bufSz (projT1 v0)))) eqn:He.
    2: { apply bool_decide_eq_false_1 in He; congruence. }
    wp_pures.
    wp_load.
    wp_apply (wp_buf_storeField_data with "[$Hisbuf $Hvslice]"); eauto.
    iIntros "Hisbuf".

    wp_pures.
    wp_load.
    wp_apply (wp_Buf__SetDirty with "Hisbuf"); iIntros "Hisbuf".
    iApply "HΦ".
    iFrame.

    iDestruct ("Hisbufmap" with "Hisbuf") as "Hisbufmap".

    iDestruct (big_sepM_delete with "Hctxvalid") as "[%Ha2 Hctxvalid2]"; eauto.
    iDestruct (big_sepM_delete with "Hctxelem") as "[[He %Hedirty] Hctxelem]"; eauto. rewrite Hbufmap_a /= in Hedirty.

    iExists _, _, _.
    simpl.
    iFrame. iFrame "#".

    iSplit.
    { iPureIntro.
      rewrite ?fmap_insert /modified /=.
      eapply insert_mono; eauto.
    }
    iSplit.
    { iApply big_sepM_insert_delete; iFrame "#".
      iPureIntro; intuition. }
    iSplit.
    {
      iApply big_sepM_insert_delete.
      rewrite lookup_insert /=.
      iSplitL "He". { iFrame. intuition. }
      iApply big_sepM_mono; try iFrame.
      iIntros (xa xb Hb) "H".
      destruct (decide (a = xa)); subst.
      { rewrite lookup_delete in Hb. congruence. }
      rewrite lookup_insert_ne; eauto.
    }
    iPureIntro. split; intros Hx; try congruence.
    rewrite -> map_filter_insert in Hx by eauto.
    eapply insert_non_empty in Hx. exfalso; eauto.

  - iDestruct "Hbufmapptr" as "[-> Hisbufmap]".
    wp_load.
    wp_pures.
    wp_apply (wp_MkBuf with "[$Hvslice]").
    { intuition. }
    iIntros (bufptr) "Hisbuf".
    wp_pures.
    wp_store.
    wp_pures.
    wp_load.
    wp_apply (wp_Buf__SetDirty with "Hisbuf"); iIntros "Hisbuf".
    wp_load.
    wp_loadField.

    wp_apply (wp_BufMap__Insert with "[$Hisbufmap $Hisbuf]").
    iIntros "Hisbufmap".
    iApply "HΦ".

    iDestruct (big_sepM_delete with "Hctxvalid") as "[%Ha2 Hctxvalid2]"; eauto.
    iDestruct (big_sepM_delete with "Hctxelem") as "[[He %Hedirty] Hctxelem]"; eauto. rewrite Hbufmap_a /= in Hedirty.

    iExists _, _, _.
    simpl.
    iFrame. iFrame "#".

    iSplit.
    { iPureIntro.
      rewrite ?fmap_insert /=.
      eapply insert_mono; eauto.
    }
    iSplit.
    { iApply big_sepM_insert_delete; iFrame "#".
      iPureIntro; intuition. }
    iSplit.
    {
      iApply big_sepM_insert_delete.
      rewrite lookup_insert /=.
      iSplitL "He". { iFrame. intuition. }
      iApply big_sepM_mono; try iFrame.
      iIntros (xa xb Hb) "H".
      destruct (decide (a = xa)); subst.
      { rewrite lookup_delete in Hb. congruence. }
      rewrite lookup_insert_ne; eauto.
    }
    iPureIntro. split; intros Hx; try congruence.
    rewrite -> map_filter_insert in Hx by eauto.
    eapply insert_non_empty in Hx. exfalso; eauto.
Qed.

Theorem wp_Op__NDirty buftx mt γUnified dinit anydirty :
  {{{
    is_jrnl buftx mt γUnified dinit anydirty
  }}}
    Op__NDirty #buftx
  {{{
    (n:u64), RET #n;
    is_jrnl buftx mt γUnified dinit anydirty
  }}}.
Proof.
  iIntros (Φ) "Htxn HΦ".
  iNamed "Htxn".
  wp_call.
  wp_loadField.
  wp_apply (wp_BufMap__Ndirty with "Hbufmap").
  iIntros (n) "[%Hnval Hbufmap]".
  iApply "HΦ".
  iExists _, _, _. iFrameNamed.
Qed.

Theorem Op_lift_one' buftx mt γUnified dinit a v E anydirty k q :
  ↑invN ⊆ E ->
  (
    is_jrnl buftx mt γUnified dinit anydirty ∗
    mapsto_txn γUnified a v
  ) -∗
    NC q -∗
    |k={E}=>
  (
    is_jrnl buftx (<[a := (existT (projT1 v) (projT2 v, projT2 v))]> mt) γUnified dinit anydirty
  ) ∗
    NC q
  .
Proof.
  iIntros (HNE) "[Htxn Ha]".
  iNamed "Htxn".

  iAssert (⌜ mt !! a = None ⌝)%I as %Hnone.
  {
    destruct (mt !! a) eqn:He; eauto.
    iDestruct (big_sepM_lookup with "Hctxelem") as "[Ha2 %]"; eauto.
    destruct (gBufmap !! a); rewrite /=.
    { iDestruct (mapsto_txn_2 with "Ha Ha2") as %[]. }
    { iDestruct (mapsto_txn_2 with "Ha Ha2") as %[]. }
  }

  iAssert (⌜ gBufmap !! a = None ⌝)%I as %Hgnone.
  {
    destruct (gBufmap !! a) eqn:He; eauto.
    eapply map_subseteq_spec in Hbufmapelem as Ha'.
    { erewrite lookup_fmap in Ha'. erewrite Hnone in Ha'. simpl in Ha'. congruence. }
    rewrite lookup_fmap. erewrite He. rewrite /=. reflexivity.
  }

  iPoseProof "Histxn" as "Histxn0".
  iNamed "Histxn".
  iIntros "HNC".
  iMod (mapsto_txn_valid' with "Histxna [Ha Histxna] [$]") as "[Ha [%Havalid HNC]]"; eauto.

  iModIntro. iFrame "HNC".
  iExists _, _, _.
  iFrame. iFrame "#%".

  iSplit.
  { iPureIntro. rewrite ?fmap_insert /=. destruct v.
    etransitivity. 2: apply insert_subseteq; rewrite lookup_fmap Hnone; done.
    eauto.
  }
  iSplit.
  { iApply big_sepM_insert; eauto. iFrame "#". intuition. }
  iApply big_sepM_insert; eauto. iFrame.
  rewrite /committed Hgnone /=. destruct v. iFrame.
  rewrite /modified /=. intuition.
Qed.

Theorem Op_lift_one buftx mt γUnified dinit a v E anydirty :
  ↑invN ⊆ E ->
  (
    is_jrnl buftx mt γUnified dinit anydirty ∗
    mapsto_txn γUnified a v
  )
    -∗ |NC={E}=>
  (
    is_jrnl buftx (<[a := (existT (projT1 v) (projT2 v, projT2 v))]> mt) γUnified dinit anydirty
  ).
Proof.
  iIntros (HNE) "[Htxn Ha]".
  iNamed "Htxn".

  iAssert (⌜ mt !! a = None ⌝)%I as %Hnone.
  {
    destruct (mt !! a) eqn:He; eauto.
    iDestruct (big_sepM_lookup with "Hctxelem") as "[Ha2 %]"; eauto.
    destruct (gBufmap !! a); rewrite /=.
    { iDestruct (mapsto_txn_2 with "Ha Ha2") as %[]. }
    { iDestruct (mapsto_txn_2 with "Ha Ha2") as %[]. }
  }

  iAssert (⌜ gBufmap !! a = None ⌝)%I as %Hgnone.
  {
    destruct (gBufmap !! a) eqn:He; eauto.
    eapply map_subseteq_spec in Hbufmapelem as Ha'.
    { erewrite lookup_fmap in Ha'. erewrite Hnone in Ha'. simpl in Ha'. congruence. }
    rewrite lookup_fmap. erewrite He. rewrite /=. reflexivity.
  }

  iPoseProof "Histxn" as "Histxn0".
  iNamed "Histxn".
  iMod (mapsto_txn_valid with "Histxna [Ha Histxna]") as "[Ha %Havalid]"; eauto.

  iModIntro.
  iExists _, _, _.
  iFrame. iFrame "#%".

  iSplit.
  { iPureIntro. rewrite ?fmap_insert /=. destruct v.
    etransitivity. 2: apply insert_subseteq; rewrite lookup_fmap Hnone; done.
    eauto.
  }
  iSplit.
  { iApply big_sepM_insert; eauto. iFrame "#". intuition. }
  iApply big_sepM_insert; eauto. iFrame.
  rewrite /committed Hgnone /=. destruct v. iFrame.
  rewrite /modified /=. intuition.
Qed.

Global Instance mapsto_txn_conflicting γUnified : Conflicting (mapsto_txn γUnified).
Proof.
  rewrite /Conflicting /ConflictsWith.
  iIntros (a0 v0 a1 v1).
  iIntros "Hm1 Hm2".
  destruct (decide (a0 = a1)); eauto; subst.
  iDestruct (mapsto_txn_2 with "Hm1 Hm2") as %[].
Qed.

Global Instance mapsto_txn_conflicts_with γUnified : ConflictsWith (mapsto_txn γUnified) (mapsto_txn γUnified).
Proof.
  apply mapsto_txn_conflicting.
Qed.

Lemma gmap_fmap_disjoint {L} `{Countable L} V1 V2 (m1 m2 : gmap L V1) (f: V1 -> V2) :
  m1 ##ₘ m2 ->
  f <$> m1 ##ₘ f <$> m2.
Proof.
  rewrite !map_disjoint_dom !dom_fmap_L //.
Qed.

Theorem Op_lift buftx mt γUnified dinit (m : gmap addr {K & _}) E anydirty :
  ↑invN ⊆ E ->
  (
    is_jrnl buftx mt γUnified dinit anydirty ∗
    [∗ map] a ↦ v ∈ m, mapsto_txn γUnified a v
  )
    -∗ |NC={E}=>
  (
    is_jrnl buftx (((λ v, existT (projT1 v) (projT2 v, projT2 v)) <$> m) ∪ mt) γUnified dinit anydirty
  ).
Proof.
  iIntros (HNE) "[Htxn Ha]".
  iNamed "Htxn".

  iAssert ([∗ map] a↦v ∈ ((λ (v : {K & bufDataT K}), @existT bufDataKind (λ k, (bufDataT k * bufDataT k)%type) (projT1 v) (projT2 v, projT2 v)) <$> m),
           mapsto_txn γUnified a (@existT bufDataKind (λ k, bufDataT k) (projT1 v) (fst (projT2 (v : {K & (bufDataT K * bufDataT K)%type})))) )%I with "[Ha]" as "Ha".
  {
    rewrite big_sepM_fmap. iApply (big_sepM_mono with "Ha").
    iIntros (k x Hkx) "H". destruct x. iFrame.
  }

  iDestruct (big_sepM_disjoint_pred with "Hctxelem Ha") as %Hd.

  iMod (big_sepM_mono_ncfupd _ (fun a (v : {K : bufDataKind & (bufDataT K * bufDataT K)%type}) => mapsto_txn γUnified a (existT (projT1 v) (projT2 v).1) ∗ ⌜ valid_addr a ∧ valid_off (projT1 v) a.(addrOff) ⌝)%I _ emp%I with "[] [$Ha]") as "[_ Ha]".
  { iModIntro. iIntros (???) "[_ H]".
    iNamed "Histxn".
    iMod (mapsto_txn_valid with "Histxna [H Histxna]") as "[H %Havalid]"; eauto.
    iModIntro. iFrame. intuition eauto. }
  iDestruct (big_sepM_sep with "Ha") as "[Ha Havalid]".

  iModIntro.
  iExists _, _, _.
  iFrame. iFrame "#%".

  iSplit.
  { iPureIntro.
    etrans; [eauto|].
    rewrite map_fmap_union.
    rewrite -map_fmap_compose.
    replace ((modified ∘ (λ v : object, existT (projT1 v) (projT2 v, projT2 v)) <$> m) ∪ (modified <$> mt))
      with ((modified <$> mt) ∪ (modified ∘ (λ v : object, existT (projT1 v) (projT2 v, projT2 v)) <$> m)).
    1: apply map_union_subseteq_l.
    rewrite map_union_comm //.
    rewrite map_fmap_compose.
    eapply gmap_fmap_disjoint.
    eauto.
  }
  iSplit.
  { iApply big_sepM_union; eauto. }
  iApply big_sepM_union; eauto. iFrame.
  iApply big_sepM_mono; last iFrame "Ha".
  iIntros (???) "Hm". rewrite /committed. iFrame.
  rewrite /modified /=.
  rewrite lookup_fmap in H. destruct (m !! k); simpl in H; try congruence.
  inversion H; subst; simpl in *.
  destruct (gBufmap !! k); simpl; intuition.

Unshelve.
  rewrite /ConflictsWith.
  intros.
  iIntros "[H1 _] H2".
  destruct (gBufmap !! a0).
  2: { iApply (mapsto_txn_conflicts_with with "H1 H2"). }
  destruct b.(bufDirty).
  2: { iApply (mapsto_txn_conflicts_with with "H1 H2"). }
  iApply (mapsto_txn_conflicts_with with "H1 H2").
Qed.

Lemma map_filter_elem_of_dom {L} `{Countable L} {V} (m: gmap L V) P `{∀ x, Decision (P x)} (k: L) :
  k ∈ dom (gset _) (filter P m) ↔
  ∃ v, m !! k = Some v ∧ P (k, v).
Proof.
  rewrite !elem_of_dom.
  split.
  - destruct 1 as [x [Hlookup HP]%map_filter_lookup_Some].
    eauto.
  - destruct 1 as [v [Hlookup HP]].
    eexists.
    apply map_filter_lookup_Some; eauto.
Qed.

Theorem wp_Op__CommitWait (PreQ: iProp Σ) buftx mt γUnified dinit (wait : bool) E  (Q : nat -> iProp Σ) anydirty :
  {{{
    is_jrnl buftx mt γUnified dinit anydirty ∗
    (|NC={⊤ ∖ ↑walN ∖ ↑ invN}=> PreQ) ∧ (|NC={⊤ ∖ ↑walN ∖ ↑invN, E}=> ∃ (σl : async (gmap addr {K & bufDataT K})),
        "Hcrashstates_frag" ∷ ghost_var γUnified.(txn_crashstates) (3/4) σl ∗
        "Hcrashstates_fupd" ∷ (
          let σ := (modified <$> mt) ∪ latest σl in
          ghost_var γUnified.(txn_crashstates) (3/4) (async_put σ σl)
          -∗ |NC={E, ⊤ ∖ ↑walN ∖ ↑invN}=> Q (length (possible σl)) ))
  }}}
    Op__CommitWait #buftx #wait
  {{{
    (ok : bool), RET #ok;
    if ok then
      ((⌜anydirty=true⌝ ∗ ∃ txnid,
      Q txnid ∗
      ([∗ map] a ↦ v ∈ modified <$> mt, mapsto_txn γUnified a v) ∗
      (⌜wait = true⌝ -∗ mono_nat_lb_own γUnified.(txn_walnames).(wal_heap_durable_lb) txnid)) ∨
      (⌜anydirty=false⌝ ∗ PreQ ∗
      [∗ map] a ↦ v ∈ modified <$> mt, mapsto_txn γUnified a v))
    else
      PreQ ∗
      [∗ map] a ↦ v ∈ committed <$> mt, mapsto_txn γUnified a v
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
  { iPureIntro.
   apply dom_filter_L; intros a.
   rewrite map_filter_elem_of_dom /=.
   split.
   - intros [v [Hlookup Hdirty]].
     rewrite Hlookup /=.
     simplify_eq/=.
     eapply (f_equal (fmap _)) in Hlookup.
     rewrite -lookup_fmap in Hlookup.
     eapply lookup_weaken in Hlookup; [|apply Hbufmapelem].
     fmap_Some in Hlookup as vo.
     rewrite Hlookup.
     eexists; split; eauto.
     congruence.
   - intros [vo [Hlookup Hdirty]].
     fmap_Some in Hdirty; eauto. }

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
    { simpl in *. destruct b.(bufDirty); try congruence.
      iDestruct "H" as "[H _]". iExact "H". }
    simpl in *. congruence. }
  simpl.

  wp_apply (wp_txn_CommitWait _ _ _ _ _ _
    ((λ (o : versioned_object),
            Build_buf_and_prev_data
           (Build_buf (projT1 o) (snd (projT2 o)) true)
           (fst (projT2 o))
      ) <$>
      (filter (λ v : addr * versioned_object, bufDirty <$> gBufmap !! v.1 = Some true) mt))
    _
    E
    ((|NC={⊤ ∖ ↑walN ∖ ↑invN}=> PreQ) ∗
      ( [∗ map] k↦x ∈ filter (λ v, bufDirty <$> gBufmap !! v.1 ≠ Some true) mt,
        mapsto_txn γUnified k (committed x) ∗ ⌜false = true ∨ committed x = modified x⌝ ))%I
    (λ txn_id,
      Q txn_id ∗
      ( [∗ map] k↦x ∈ filter (λ v, bufDirty <$> gBufmap !! v.1 ≠ Some true) mt,
        mapsto_txn γUnified k (committed x) ∗ ⌜false = true ∨ committed x = modified x⌝ ))%I
    with "[$Histxn $Hdirtyslice Hdirtylist Hctxelem0 Hctxelem1 Hfupd]"); eauto.
  {
    iSplitR "Hfupd Hctxelem1".
    {
      assert (filter (λ x, (x.2).(bufDirty) = true) gBufmap =
              (λ o : versioned_object, {| bufKind := projT1 o;
                                          bufData := (projT2 o).2;
                                          bufDirty := true |}) <$>
              filter (λ v, bufDirty <$> gBufmap !! v.1 = Some true) mt) as Hgmt.
      {
        eapply map_eq; intros a.
        destruct (filter (λ x : addr * buf, (x.2).(bufDirty) = true) gBufmap !! a) eqn:Heq.
        2: {
          rewrite lookup_fmap.
          rewrite map_filter_lookup_None_2; eauto.
          eapply map_filter_lookup_None_1 in Heq. intuition.
          { right; intros; simpl. rewrite H1 in H3. done. }
          right; intros; simpl.
          eapply fmap_Some_1 in H3. destruct H3; intuition; subst.
          eapply H1; eauto.
        }
        eapply map_filter_lookup_Some in Heq; destruct Heq; simpl in *; subst.
        eapply lookup_weaken in Hbufmapelem.
        2: { rewrite lookup_fmap. erewrite H. done. }
        rewrite lookup_fmap in Hbufmapelem.
        eapply fmap_Some_1 in Hbufmapelem. destruct Hbufmapelem; intuition; subst.
        rewrite lookup_fmap.
        erewrite map_filter_lookup_Some_2; eauto.
        2: { simpl. rewrite H. simpl. congruence. }
        simpl. f_equal.
        destruct b. simpl in *.
        rewrite /modified /= in H3. inversion H3; subst.
        done.
      }
      rewrite Hgmt.

      rewrite !big_sepML_fmap.
      iDestruct (big_sepML_sepM with "[$Hdirtylist $Hctxelem0]") as "Hdirtylist".
      iApply (big_sepML_mono with "Hdirtylist").
      iPureIntro.
      iIntros (k v lv) "[Hbuf Hmapsto]".
      rewrite /is_txn_buf_pre. iFrame.
    }
    {
      iSplit.
      { iDestruct "Hfupd" as "[$ _]". iFrame. }
      iIntros "%Hempty".
      iDestruct "Hfupd" as "[_ Hfupd]".
      iMod "Hfupd" as (σl) "Hfupd". iNamed "Hfupd".
      iModIntro.
      iIntros (CP) "[Hunify HCP]".

      iDestruct (big_sepM_mono_with_inv' with "[Hunify HCP Hcrashstates_frag $Hctxelem1]")
        as "[Hx Hctxelem1]".
      3: iDestruct (big_sepM_sep with "Hctxelem1") as "[Hctxelem1 Hctxelem1']".
      2: iAccu.
      {
        iIntros (k x Hkx) "[(#Hunify & HCP & Hcrashstates_frag) [Hmapsto Hextra]]".
        intuition try congruence.
        iDestruct ("Hunify" with "[$HCP $Hcrashstates_frag $Hmapsto]") as "#Hu".
        iSplitL "HCP Hcrashstates_frag". 1: iFrame "#∗".
        iAssert (⌜committed x = modified x⌝)%I as %Heq.
        { iDestruct "Hextra" as %Hextra. intuition eauto. }
        iSplitL "Hmapsto Hextra".
        { iAccu. }
        rewrite Heq. iExact "Hu".
      }
      iDestruct "Hx" as "(_ & HCP & Hcrashstates_frag)".
      simpl.

      iAssert (⌜modified <$> filter (λ v, bufDirty <$> gBufmap !! v.1 ≠ Some true) mt ⊆ σl.(latest)⌝)%I as %Hmt_latest.
      {
        iDestruct "Hctxelem1'" as %Hx.
        iPureIntro.
        eapply map_subseteq_spec.
        intros a o Ha. rewrite lookup_fmap in Ha.
        eapply fmap_Some_1 in Ha. destruct Ha as [vo [Ha Heq]]. subst.
        eapply Hx in Ha. eauto.
      }

      iModIntro. iFrame. iExists _. iFrame.
      iIntros "H".
      iMod ("Hcrashstates_fupd" with "[H]") as "$"; last done.

      replace (modified <$> mt) with (modified <$> (filter (λ v, bufDirty <$> gBufmap !! v.1 = Some true) mt ∪
                                                    filter (λ v, bufDirty <$> gBufmap !! v.1 ≠ Some true) mt)).
      2: { rewrite map_union_filter; eauto. }
      rewrite map_fmap_union.
      rewrite -assoc.
      iExactEq "H". f_equal. f_equal. f_equal.
      { rewrite -map_fmap_compose. reflexivity. }
      rewrite map_subseteq_union; eauto.
    }
  }
  iIntros (ok) "Hunifiedtxns".
  iApply wp_ncfupd.
  wp_pures.

  iApply "HΦ".
  destruct ok.
  - iDestruct "Hunifiedtxns" as "[[Hq Hpreq] Hmapsto0]".
    destruct anydirty.
    {
      iLeft.
      iDestruct ("Hq" with "[]") as (txnid) "[Hq Hflush]".
      {
        iPureIntro. intro Hempty. eapply fmap_empty_inv in Hempty.
        assert (filter (λ b, (b.2).(bufDirty) = true) gBufmap = ∅); intuition try congruence.
        eapply map_empty; intros a.
        eapply map_filter_lookup_None.
        destruct (gBufmap !! a) eqn:He; intuition eauto. right.
        simpl. intros bb Hx Hbb. inversion Hx; clear Hx; subst.
        eapply lookup_weaken in Hbufmapelem.
        2: { rewrite lookup_fmap. erewrite He. eauto. }
        rewrite lookup_fmap /modified in Hbufmapelem.
        eapply fmap_Some_1 in Hbufmapelem; destruct Hbufmapelem as [mb [Hbufmapelem He2]].
        destruct bb; simpl in *. inversion He2; subst.
        apply eq_sigT_eq_dep in He2. apply Eqdep_dec.eq_dep_eq_dec in He2; last apply bufDataKind_eq_dec.
        subst.
        eapply map_filter_lookup_Some_2 in Hbufmapelem.
        { erewrite Hempty in Hbufmapelem. inversion Hbufmapelem. }
        simpl. rewrite He. simpl. eauto.
      }
      iDestruct "Hq" as "[Hq Hctxelem1]".
      iSplitL ""; first by done.
      iExists _.
      iFrame "Hq". iFrame "Hflush".

      rewrite big_sepM_fmap.
      iDestruct (big_sepM_union (λ k x, mapsto_txn γUnified k (modified x)) with "[Hmapsto0 Hctxelem1]") as "Hmapsto".
      2: {
        iSplitL "Hmapsto0".
        { iApply (big_sepM_mono with "Hmapsto0").
          iIntros (k x Hkx) "H".
          destruct x; rewrite /modified /=. iFrame. }
        iApply (big_sepM_mono with "Hctxelem1").
        iIntros (k x Hkx) "[H %Heq]".
        destruct Heq as [Heq | Heq]; first congruence.
        rewrite Heq; iFrame.
      }
      { eapply map_disjoint_filter. }
      rewrite map_union_filter.
      rewrite big_sepM_fmap.
      iFrame.
      eauto.
    }
    {
      iRight.
      iSplitL ""; first by done.
      iDestruct ("Hpreq" with "[]") as "[Hpreq Hctxelem1]".
      1: {
        iPureIntro.
        assert (filter (λ v : addr * versioned_object, bufDirty <$> gBufmap !! v.1 = Some true) mt = ∅) as Hz.
        {
          eapply map_empty; intros a.
          eapply map_filter_lookup_None.
          destruct (mt !! a) eqn:He; intuition eauto. right.
          simpl. intros vo Hx Hvo. inversion Hx; clear Hx; subst.
          eapply fmap_Some_1 in Hvo. destruct Hvo as [bb [Hvo He2]].
          eapply map_filter_lookup_Some_2 in Hvo.
          { erewrite H1 in Hvo. inversion Hvo. }
          simpl. eauto.
        }
        rewrite Hz. rewrite fmap_empty; auto.
      }

      rewrite big_sepM_fmap.
      iDestruct (big_sepM_union (λ k x, mapsto_txn γUnified k (modified x)) with "[Hmapsto0 Hctxelem1]") as "Hmapsto".
      2: {
        iSplitL "Hmapsto0".
        { iApply (big_sepM_mono with "Hmapsto0").
          iIntros (k x Hkx) "H".
          destruct x; rewrite /modified /=. iFrame. }
        iApply (big_sepM_mono with "Hctxelem1").
        iIntros (k x Hkx) "[H %Heq]".
        destruct Heq as [Heq | Heq]; first congruence.
        rewrite Heq; iFrame.
      }
      { eapply map_disjoint_filter. }
      rewrite map_union_filter.
      rewrite big_sepM_fmap.
      iFrame.
      iMod (ncfupd_mask_mono with "Hpreq"); auto.
    }

  - iDestruct "Hunifiedtxns" as "[Hpreq Hmapsto0]".
    iDestruct "Hpreq" as "[Hpreq Hctxelem1]".
    iMod (ncfupd_mask_mono with "Hpreq") as "Hpreq"; first auto.
    iModIntro.
    iFrame "Hpreq".

    rewrite big_sepM_fmap.
    iDestruct (big_sepM_union (λ k x, mapsto_txn γUnified k (committed x)) with "[Hmapsto0 Hctxelem1]") as "Hmapsto".
    2: {
      iSplitL "Hmapsto0".
      { iApply (big_sepM_mono with "Hmapsto0").
        iIntros (k x Hkx) "H".
        destruct x; rewrite /committed /=. iFrame. }
      iApply (big_sepM_mono with "Hctxelem1").
      iIntros (k x Hkx) "[H _]". iFrame.
    }
    { eapply map_disjoint_filter. }
    rewrite map_union_filter.
    rewrite big_sepM_fmap.
    iFrame.
Qed.

Context `{!stagedG Σ}.

Definition wpwpcN := nroot.@"temp".

Theorem wpc_Op__CommitWait (PreQ: iProp Σ) buftx mt γUnified dinit (wait : bool) E  (Q Qc : nat -> iProp Σ) {HT1: Timeless PreQ} {HT2: ∀ n, Timeless (Qc n)} anydirty k :
  {{{
    is_jrnl buftx mt γUnified dinit anydirty ∗
    <disc> PreQ ∧ ( |NC={⊤ ∖ ↑walN ∖ ↑invN ∖ ↑ wpwpcN, E}=> ∃ (σl : async (gmap addr {K & bufDataT K})),
        "Hcrashstates_frag" ∷ ghost_var γUnified.(txn_crashstates) (3/4) σl ∗
        "Hcrashstates_fupd" ∷ (
          let σ := (modified <$> mt) ∪ latest σl in
          ghost_var γUnified.(txn_crashstates) (3/4) (async_put σ σl)
          -∗ |NC={E, ⊤ ∖ ↑walN ∖ ↑invN ∖ ↑ wpwpcN}=> <disc> (▷ Qc (length (possible σl))) ∧ Q (length (possible σl)) ))
  }}}
    Op__CommitWait #buftx #wait @ (S k) ; ⊤
  {{{
    (ok : bool), RET #ok;
    if ok then
      ((⌜anydirty=true⌝ ∗ ∃ txnid,
      Q txnid ∗
      ([∗ map] a ↦ v ∈ modified <$> mt, mapsto_txn γUnified a v) ∗
      (⌜wait = true⌝ -∗ mono_nat_lb_own γUnified.(txn_walnames).(wal_heap_durable_lb) txnid)) ∨
      (⌜anydirty=false⌝ ∗ PreQ ∗
      [∗ map] a ↦ v ∈ modified <$> mt, mapsto_txn γUnified a v))
    else
      PreQ ∗
      [∗ map] a ↦ v ∈ committed <$> mt, mapsto_txn γUnified a v
  }}}
  {{{ (∃ txnid, Qc txnid) ∨ PreQ }}}.
Proof using stagedG0.
  iIntros (Φ Φc) "(His_jrnl&Hfupd) HΦc".
  rewrite bi.and_comm.
  rewrite own_discrete_fupd_eq /own_discrete_fupd_def.
  iDestruct (own_discrete_elim_conj with "Hfupd") as (Q_keep Q_inv) "(HQ_keep&HQ_inv&#Hwand1&#Hwand2)".
  iMod (pending_alloc) as (γpending) "Hpending".
  iMod (inv_mut_alloc (S k) wpwpcN _ wp_to_wpc.mysch ([
   (∃ txnid, Qc txnid) ∨ PreQ; staged_done γpending; C; staged_pending (3/4)%Qp γpending])%I [Q_inv] with "[HQ_inv]") as "(#Hinv&Hfull)".
  { rewrite wp_to_wpc.mysch_interp_strong. iLeft. iSplit; first auto.
    iMod ("Hwand1" with "[$]") as "H".
    iModIntro. iMod (fupd_level_split_level with "H") as "$".
    { lia. }
    eauto.
  }
  iDestruct (pending_split34 with "Hpending") as "(Hpend34&Hpend14)".
  iAssert (WPC _ @ S k; ⊤ {{ v, ∃ (ok: bool), ⌜ v = #ok ⌝ ∗ (staged_pending (3 / 4)%Qp γpending -∗ |NC={⊤}=>
                 (if ok
                  then
                   ⌜anydirty = true⌝
                   ∗ (∃ txnid : nat,
                        Q txnid
                        ∗ ([∗ map] a↦v ∈ (modified <$> mt), mapsto_txn γUnified a v)
                          ∗ (⌜wait = true⌝ -∗ mono_nat_lb_own γUnified.(txn_walnames).(wal_heap_durable_lb) txnid))
                   ∨ ⌜anydirty = false⌝ ∗ PreQ ∗ ([∗ map] a↦v ∈ (modified <$> mt), mapsto_txn γUnified a v)
                  else PreQ ∗ ([∗ map] a↦v ∈ (committed <$> mt), mapsto_txn γUnified a v)))}} {{ True }})%I with "[His_jrnl HQ_keep Hpend14 Hfull]" as "Hwpc";
    last first.
  {
    iApply wpc_ncfupd.
    iApply (wpc_step_strong_mono with "Hwpc"); auto.
    iSplit.
    * iNext. iIntros (?) "Hwand". iDestruct "Hwand" as (ok ->) "Hwand". iModIntro. iRight in "HΦc".
      iApply "HΦc". iApply "Hwand". by iFrame.
    * iLeft in "HΦc". iIntros "_". iIntros "HC".
      {
        iApply (fupd_level_fupd _ _ _ (S k)).
        iMod (fupd_level_mask_mono with "HΦc") as "HΦc"; first by set_solver+.
        iMod (inv_mut_acc with "Hinv") as (Qs) "(H&Hclo)"; first auto.
        rewrite wp_to_wpc.mysch_interp_weak /=.
        iDestruct "H" as "[(_&>H)|[Hfalse1|Hfalse2]]".
        * iEval (rewrite uPred_fupd_level_eq /uPred_fupd_level_def).
          iMod (fupd_split_level_intro_mask' _ ∅) as "Hclo''"; first by set_solver+.
          iMod (fupd_split_level_le with "H") as ">H"; first lia.
          iMod "Hclo''".
          iSpecialize ("Hclo" with "[HC Hpend34]").
          { iRight. iLeft. iFrame. }
          iEval (rewrite uPred_fupd_level_eq /uPred_fupd_level_def) in "Hclo".
          iMod "Hclo". iModIntro. iApply "HΦc". iApply "H".
        * iDestruct "Hfalse1" as "(>_&>?)". iDestruct (pending34_pending34 with "[$] [$]") as "[]".
        * iDestruct "Hfalse2" as ">?". iDestruct (pending_done with "[$] [$]") as "[]".
      }
  }
  iApply (wp_wpc).
  iApply wp_ncfupd.
  wp_apply (wp_Op__CommitWait (staged_pending (3/4) γpending -∗ |NC={⊤}=> PreQ) _ _ _ _ _ E
                                  (λ n, staged_pending (3/4) γpending -∗ |NC={⊤}=> Q n)%I
              with "[$His_jrnl Hfull Hpend14 HQ_keep]").
  { iSplit.
    - rewrite ncfupd_eq /ncfupd_def. iIntros (q) "HNC".
      iMod (inv_mut_full_acc with "Hfull") as "(H&Hclo)"; first auto.
      { solve_ndisj. }
      rewrite ?mysch_interp_strong.
      iDestruct "H" as "[HQ|Hfalse]"; last first.
      { iDestruct "Hfalse" as "[(>Hfalse&_)|>Hfalse]".
        * iDestruct (NC_C with "[$] [$]") as "[]".
        * iDestruct (pending_done with "[$] [$]") as "[]".
      }
      iDestruct "HQ" as "(HQ&_)".
      iMod ("Hwand2" with "[$]") as "Hfupd".
      iRight in "Hfupd".

      iEval (rewrite -(and_idem (<bdisc> _)%I)) in "Hfupd".
      iClear "Hwand1 Hwand2".
      iDestruct (own_discrete_elim_conj with "Hfupd") as (Q_keep' Q_inv')
                                                                  "(HQ_keep&HQ_inv&#Hwand1&#Hwand2)".
      iMod ("Hclo" $! [Q_inv'] with "[HQ_inv]") as "Hfull".
      { rewrite ?wp_to_wpc.mysch_interp_strong. iLeft. iSplit; first auto.
        iMod ("Hwand1" with "[$]") as "H".
        iModIntro. iMod (fupd_level_split_level with "H") as "HQc".
        { lia. }
        iModIntro. eauto.
      }
      iFrame. iModIntro.
      iIntros "Hpend34" (q1) "HNC".
      iMod (inv_mut_full_acc with "Hfull") as "(H&Hclo)"; first auto.
      rewrite ?mysch_interp_strong.
      iDestruct "H" as "[HQ|Hfalse]"; last first.
      { iDestruct "Hfalse" as "[(>Hfalse&_)|>Hfalse]".
        * iDestruct (NC_C with "[$] [$]") as "[]".
        * iDestruct (pending_done with "[$] [$]") as "[]".
      }
      iDestruct "HQ" as "(HQ&_)".
      iMod ("Hwand2" with "[$]") as "(HΦ&_)".
      iDestruct (pending_join34 with "[$]") as "Hpend".
      iMod (pending_upd_done with "Hpend") as "Hdone".
      iMod ("Hclo" $! [True]%I with "[Hdone]").
      { rewrite ?mysch_interp_strong. iRight. by iRight. }
      iFrame. eauto.
      iEval (rewrite own_discrete_elim) in "HΦ".
      iPoseProof (fupd_level_fupd with "HΦ") as "HΦ".
      iMod (fupd_mask_mono with "HΦ") as "$"; first by set_solver+.
      eauto.
    - rewrite ncfupd_eq /ncfupd_def. iIntros (q) "HNC".
      iMod (inv_mut_full_acc with "Hfull") as "(H&Hclo)"; first auto.
      { solve_ndisj. }
      rewrite ?mysch_interp_strong.
      iDestruct "H" as "[HQ|Hfalse]"; last first.
      { iDestruct "Hfalse" as "[(>Hfalse&_)|>Hfalse]".
        * iDestruct (NC_C with "[$] [$]") as "[]".
        * iDestruct (pending_done with "[$] [$]") as "[]".
      }
      iDestruct "HQ" as "(HQ&_)".
      iMod ("Hwand2" with "[$]") as "Hfupd".
      iLeft in "Hfupd".
      iMod ("Hfupd" with "[$]") as "(Hfupd&HNC)".
      iDestruct "Hfupd" as (σl) "Hfupd".
      iEval (setoid_rewrite bi.and_comm) in "Hfupd".
      iModIntro. iFrame.
      iExists _. iNamed "Hfupd". iFrame. iIntros "?".

      iIntros (q') "HNC". iMod ("Hcrashstates_fupd" with "[$] [$]") as "(Hcrashstates&HNC)".
      iClear "Hwand1 Hwand2".
      iDestruct (own_discrete_elim_conj with "Hcrashstates") as (Q_keep' Q_inv')
                                                                  "(HQ_keep&HQ_inv&#Hwand1&#Hwand2)".
      iMod ("Hclo" $! [Q_inv'] with "[HQ_inv]") as "Hfull".
      { rewrite ?wp_to_wpc.mysch_interp_strong. iLeft. iSplit; first auto.
        iMod ("Hwand1" with "[$]") as "H".
        iModIntro. iMod (fupd_level_split_level with "H") as "HQc".
        { lia. }
        iModIntro. eauto.
      }
      iFrame. iModIntro.
      iIntros "Hpend34" (q1) "HNC".
      iMod (inv_mut_full_acc with "Hfull") as "(H&Hclo)"; first auto.
      rewrite ?mysch_interp_strong.
      iDestruct "H" as "[HQ|Hfalse]"; last first.
      { iDestruct "Hfalse" as "[(>Hfalse&_)|>Hfalse]".
        * iDestruct (NC_C with "[$] [$]") as "[]".
        * iDestruct (pending_done with "[$] [$]") as "[]".
      }
      iDestruct "HQ" as "(HQ&_)".
      iMod ("Hwand2" with "[$]") as "(HΦ&_)".
      iDestruct (pending_join34 with "[$]") as "Hpend".
      iMod (pending_upd_done with "Hpend") as "Hdone".
      iMod ("Hclo" $! [True]%I with "[Hdone]").
      { rewrite ?mysch_interp_strong. iRight. by iRight. }
      iFrame. eauto.
  }

  iIntros (ok) "H".
  iIntros "!>". iExists ok; iSplit; first done. iIntros "Hpending34".
  destruct ok.
  - iDestruct "H" as "[(Hp&H)|H]".
    * iLeft. iFrame. iDestruct "H" as (txid) "(HQ&H1&H2)". iExists _; iFrame.
      by iApply "HQ".
    * iRight. iFrame. iDestruct "H" as "($&H&$)".
      by iApply "H".
  - iDestruct "H" as "(H&$)". by iApply "H".
Qed.

End heap.
