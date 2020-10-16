From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From iris.algebra Require Import numbers.
From Perennial.algebra Require Import deletable_heap log_heap liftable.
From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.

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
Implicit Types (mT : gmap addr {K & (bufDataT K * bufDataT K)%type}).

Definition committed (v : {K & (bufDataT K * bufDataT K)%type}) : {K & bufDataT K} :=
  existT _ (fst (projT2 v)).

Definition modified (v : {K & (bufDataT K * bufDataT K)%type}) : {K & bufDataT K} :=
  existT _ (snd (projT2 v)).

Definition is_buftxn (buftx : loc)
                     mT
                     γUnified : iProp Σ :=
  (
    ∃ (l : loc) (bufmap : loc) (gBufmap : gmap addr buf),
      "Hbuftx.l" ∷ buftx ↦[BufTxn.S :: "txn"] #l ∗
      "Hbuftx.map" ∷ buftx ↦[BufTxn.S :: "bufs"] #bufmap ∗
      "#Histxn" ∷ is_txn l γUnified ∗
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
        ⌜dirty=true ∨ committed v = modified v⌝ )
  )%I.

Local Lemma is_buftxn_to_get_mapsto_txn buftx mT γUnified :
  is_buftxn buftx mT γUnified -∗
  [∗ map] a ↦ v ∈ mT, mapsto_txn γUnified a (committed v).
Proof.
  iNamed 1.
  iApply (big_sepM_mono with "Hctxelem").
  iIntros (a obj Hlookup) "[Ha _]". iFrame.
Qed.

Lemma is_buftxn_not_in_map buftx mT γUnified a v0 :
  is_buftxn buftx mT γUnified -∗
  mapsto_txn γUnified a v0 -∗
  ⌜mT !! a = None⌝.
Proof.
  rewrite is_buftxn_to_get_mapsto_txn.
  iIntros "Hm Ha".
  destruct (mT !! a) eqn:Helem; eauto.
  iExFalso.
  iDestruct (big_sepM_lookup with "Hm") as "Ha2"; eauto.
  iDestruct (mapsto_txn_2 with "Ha Ha2") as %[].
Qed.

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
  iExists _, _, _.
  iFrame.
  rewrite big_sepM_empty. iFrame "Htxn ∗".
  iSplit; first by done.
  rewrite left_id.
  rewrite big_sepM_empty //.
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
    is_buf bufptr a (Build_buf (projT1 v) (snd (projT2 v)) dirty) ∗
    ( ∀ v' dirty',
      ( ⌜ dirty' = true ∨ (dirty' = dirty ∧ snd (projT2 v) = v') ⌝ ∗
        is_buf bufptr a (Build_buf (projT1 v) v' dirty') ) ==∗
      ( is_buftxn buftx (<[a := existT _ (fst (projT2 v), v')]> mT) γUnified ) )
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

    apply eq_sigT_eq_dep in H.
    apply Eqdep_dec.eq_dep_eq_dec in H.
    2: apply bufDataKind_eq_dec.

    inversion H3; clear H3; subst.
    apply eq_sigT_eq_dep in H5.
    apply Eqdep_dec.eq_dep_eq_dec in H5.
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
      iApply big_sepM_insert_delete.
      rewrite lookup_insert /=.
      iSplitL "He". { iFrame. iPureIntro; eauto. }
      iApply big_sepM_mono; try iFrame.
      iIntros (xa xb Hb) "H".
      destruct (decide (a = xa)); subst.
      { rewrite lookup_delete in Hb. congruence. }
      rewrite lookup_insert_ne; eauto.

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
      iApply big_sepM_insert_delete.
      rewrite lookup_insert /=.
      iSplitL "He". { iFrame. iPureIntro. intuition congruence. }
      iApply big_sepM_mono; try iFrame.
      iIntros (xa xb Hb) "H".
      destruct (decide (a = xa)); subst.
      { rewrite lookup_delete in Hb. congruence. }
      rewrite lookup_insert_ne; eauto.

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
    iApply "HΦ".
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
      iApply big_sepM_insert_delete.
      rewrite lookup_insert /=.
      iSplitL "He". { iFrame. iPureIntro. rewrite /committed /modified /=. intuition eauto. }
      iApply big_sepM_mono; try iFrame.
      iIntros (xa xb Hb) "H".
      destruct (decide (a = xa)); subst.
      { rewrite lookup_delete in Hb. congruence. }
      rewrite lookup_insert_ne; eauto.

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
      iApply big_sepM_insert_delete.
      rewrite lookup_insert /=.
      iSplitL "He". { iFrame. iDestruct "Hepure" as %He. rewrite Hbufmap_a /= in He. iPureIntro. rewrite /committed /modified /=. intuition idtac. }
      iApply big_sepM_mono; try iFrame.
      iIntros (xa xb Hb) "H".
      destruct (decide (a = xa)); subst.
      { rewrite lookup_delete in Hb. congruence. }
      rewrite lookup_insert_ne; eauto.
Qed.

Theorem wp_BufTxn__OverWrite buftx mt γUnified a v0 (v : {K & (bufDataT K * bufDataT K)%type}) (sz : u64) (vslice : Slice.t) :
  {{{
    is_buftxn buftx mt γUnified ∗
    ⌜ mt !! a = Some v0 ⌝ ∗
    is_buf_data vslice (snd (projT2 v)) a ∗
    ⌜ sz = bufSz (projT1 v) ⌝ ∗
    ⌜ existT (projT1 v) (fst (projT2 v)) = existT (projT1 v0) (fst (projT2 v0)) ⌝
  }}}
    BufTxn__OverWrite #buftx (addr2val a) #sz (slice_val vslice)
  {{{
    RET #();
    is_buftxn buftx (<[a := v]> mt) γUnified
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
  apply eq_sigT_eq_dep in H4.
  apply Eqdep_dec.eq_dep_eq_dec in H4.
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
    iApply big_sepM_insert_delete.
    rewrite lookup_insert /=.
    iSplitL "He". { iFrame. intuition. }
    iApply big_sepM_mono; try iFrame.
    iIntros (xa xb Hb) "H".
    destruct (decide (a = xa)); subst.
    { rewrite lookup_delete in Hb. congruence. }
    rewrite lookup_insert_ne; eauto.

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
    iApply big_sepM_insert_delete.
    rewrite lookup_insert /=.
    iSplitL "He". { iFrame. intuition. }
    iApply big_sepM_mono; try iFrame.
    iIntros (xa xb Hb) "H".
    destruct (decide (a = xa)); subst.
    { rewrite lookup_delete in Hb. congruence. }
    rewrite lookup_insert_ne; eauto.
Qed.

Theorem BufTxn_lift_one buftx mt γUnified a v E :
  ↑invN ⊆ E ->
  (
    is_buftxn buftx mt γUnified ∗
    mapsto_txn γUnified a v
  )
    ={E}=∗
  (
    is_buftxn buftx (<[a := (existT (projT1 v) (projT2 v, projT2 v))]> mt) γUnified
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
  iFrame. iFrame "#".

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

Theorem BufTxn_lift buftx mt γUnified (m : gmap addr {K & _}) E :
  ↑invN ⊆ E ->
  (
    is_buftxn buftx mt γUnified ∗
    [∗ map] a ↦ v ∈ m, mapsto_txn γUnified a v
  )
    ={E}=∗
  (
    is_buftxn buftx (((λ v, existT (projT1 v) (projT2 v, projT2 v)) <$> m) ∪ mt) γUnified
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

  iMod (big_sepM_mono_fupd _ (fun a (v : {K : bufDataKind & (bufDataT K * bufDataT K)%type}) => mapsto_txn γUnified a (existT (projT1 v) (projT2 v).1) ∗ ⌜ valid_addr a ∧ valid_off (projT1 v) a.(addrOff) ⌝)%I _ emp%I with "[] [$Ha]") as "[_ Ha]".
  { iModIntro. iIntros (???) "[_ H]".
    iNamed "Histxn".
    iMod (mapsto_txn_valid with "Histxna [H Histxna]") as "[H %Havalid]"; eauto.
    iModIntro. iFrame. intuition eauto. }
  iDestruct (big_sepM_sep with "Ha") as "[Ha Havalid]".

  iModIntro.
  iExists _, _, _.
  iFrame. iFrame "#".

  iSplit.
  { iPureIntro.
    etransitivity. 1: eauto.
    (* XXX where is [union_fmap]?? *)
    (*
    eapply map_union_subseteq_r. set_solver. *)
    admit.
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
Admitted.

Theorem wp_BufTxn__CommitWait buftx mt γUnified (wait : bool) E (Q : nat -> iProp Σ) :
  {{{
    is_buftxn buftx mt γUnified ∗
    ( |={⊤ ∖ ↑walN ∖ ↑invN, E}=> ∃ (σl : async (gmap addr {K & bufDataT K})),
        "Hcrashstates_frag" ∷ ghost_var γUnified.(txn_crashstates) (1/2) σl ∗
        "Hcrashstates_fupd" ∷ (
          let σ := (modified <$> mt) ∪ latest σl in
          ghost_var γUnified.(txn_crashstates) (1/2) (async_put σ σl)
          ={E, ⊤ ∖ ↑walN ∖ ↑invN}=∗ Q (length (possible σl)) ))
  }}}
    BufTxn__CommitWait #buftx #wait
  {{{
    (ok : bool), RET #ok;
    if ok then
      ∃ txnid,
      Q txnid ∗
      (⌜wait = true⌝ -∗ own γUnified.(txn_walnames).(wal_heap_durable_lb) (◯ (MaxNat txnid))) ∗
      [∗ map] a ↦ v ∈ modified <$> mt, mapsto_txn γUnified a v
    else
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

(*
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
*)
Admitted.

End heap.
