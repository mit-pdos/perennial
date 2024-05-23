From Coq Require Import Program.Equality.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.Helpers Require Import bytes Map.
From Perennial.program_proof Require Import disk_prelude.
From Goose.github_com.mit_pdos.go_journal Require Import buf.
From Perennial.Helpers Require Import NamedProps PropRestore.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

From Perennial.program_proof Require Import util_proof disk_lib.
From Perennial.program_proof Require Export buf.defs.
From Perennial.program_proof Require Import addr.addr_proof wal.abstraction.
From Perennial.program_proof Require Export buf.buf_proof.

Section heap.
Context `{!heapGS Σ}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Definition is_bufmap (bufmap : loc) (bm : gmap addr buf) : iProp Σ :=
  ∃ (mptr : loc) (m : gmap u64 loc) (am : gmap addr loc),
    bufmap ↦[BufMap :: "addrs"] #mptr ∗
    own_map mptr (DfracOwn 1) m ∗
    ⌜ flatid_addr_map m am ⌝ ∗
    [∗ map] a ↦ bufptr; buf ∈ am; bm,
      is_buf bufptr a buf.

Theorem wp_MkBufMap stk E :
  {{{
    emp
  }}}
    MkBufMap #() @ stk; E
  {{{
    (l : loc), RET #l;
    is_bufmap l ∅
  }}}.
Proof.
  iIntros (Φ) "Hemp HΦ".

  wp_call.
  wp_apply (wp_NewMap u64).
  iIntros (mref) "Hmref".
  wp_apply wp_allocStruct; first val_ty.
  iIntros (bufmap) "Hbufmap".

  iDestruct (struct_fields_split with "Hbufmap") as "[Hbufmap _]".

  wp_pures.
  iApply "HΦ".
  iExists _, _, _.

  iFrame.
  iSplitR; first (iPureIntro; apply flatid_addr_empty).
  iApply big_sepM2_empty.
  done.
Qed.

Theorem wp_BufMap__Insert l m bl a b stk E :
  {{{
    is_bufmap l m ∗
    is_buf bl a b
  }}}
    BufMap__Insert #l #bl @ stk; E
  {{{
    RET #();
    is_bufmap l (<[a := b]> m)
  }}}.
Proof using.
  iIntros (Φ) "[Hbufmap Hbuf] HΦ".
  iDestruct "Hbufmap" as (mptr mm am) "(Hmptr & Hmap & % & Ham)".
  iNamed "Hbuf".
  iNamed "Hisbuf_without_data".

  wp_call.
  wp_loadField.
  wp_apply wp_Addr__Flatid; intuition eauto. iIntros (?) "->".
  wp_loadField.
  wp_apply (wp_MapInsert_to_val with "Hmap"); iIntros "Hmap".
  wp_pures. iApply "HΦ".
  iExists _, _, _. iFrame.
  iSplitR.
  { iPureIntro. apply flatid_addr_insert; eauto. }

  (* Two cases: either we are inserting a new addr or overwriting *)
  destruct (am !! a) eqn:Heq.
  - iDestruct (big_sepM2_lookup_l_some with "Ham") as (v2) "%"; eauto.
    iDestruct (big_sepM2_insert_acc with "Ham") as "[Hcur Hacc]"; eauto.
    iApply "Hacc".
    iExists _; iFrame. done.

  - iDestruct (big_sepM2_lookup_l_none with "Ham") as "%"; eauto.
    iApply big_sepM2_insert; eauto.
    iFrame "Ham".
    iExists _; iFrame. done.
Qed.

Theorem wp_BufMap__Del l m a stk E :
  {{{
    is_bufmap l m ∗
    ⌜ valid_addr a ⌝
  }}}
    BufMap__Del #l (addr2val a) @ stk; E
  {{{
    RET #();
    is_bufmap l (delete a m)
  }}}.
Proof using.
  iIntros (Φ) "[Hbufmap %] HΦ".
  iDestruct "Hbufmap" as (mptr mm am) "(Hmptr & Hmap & % & Ham)".

  wp_call.
  wp_apply wp_Addr__Flatid; eauto. iIntros (?) "->".
  wp_loadField.
  wp_apply (wp_MapDelete with "Hmap"); iIntros "Hmap".
  wp_pures. iApply "HΦ".
  iExists _, _, _. iFrame.
  iSplitR.
  { iPureIntro. apply flatid_addr_delete; eauto. }

  (* Two cases: either we are deleting an existing addr or noop *)
  destruct (am !! a) eqn:Heq.
  - iDestruct (big_sepM2_lookup_l_some with "Ham") as (v2) "%"; eauto.
    iDestruct (big_sepM2_delete with "Ham") as "[Hcur Hacc]"; eauto.

  - iDestruct (big_sepM2_lookup_l_none with "Ham") as "%"; eauto.
    rewrite delete_notin; eauto.
    rewrite delete_notin; eauto.
Qed.

Theorem wp_BufMap__Lookup l m a stk E :
  {{{
    is_bufmap l m ∗
    ⌜ valid_addr a ⌝
  }}}
    BufMap__Lookup #l (addr2val a) @ stk; E
  {{{
    (bptr : loc), RET #bptr;
    match m !! a with
    | None =>
      ⌜ bptr = null ⌝ ∗ is_bufmap l m
    | Some b =>
      is_buf bptr a b ∗
      (∀ b', is_buf bptr a b' -∗ is_bufmap l (<[a := b']> m))
    end
  }}}.
Proof using.
  iIntros (Φ) "[Hbufmap %] HΦ".
  iDestruct "Hbufmap" as (mptr mm am) "(Hmptr & Hmap & % & Ham)".

  wp_call.
  wp_apply wp_Addr__Flatid; eauto. iIntros (?) "->".
  wp_loadField.
  wp_apply (wp_MapGet with "Hmap"). iIntros (v ok) "[% Hmap]".
  wp_pures.

  destruct ok.
  - apply map_get_true in H1.
    erewrite flatid_addr_lookup in H1; eauto.
    iDestruct (big_sepM2_lookup_l_some with "Ham") as (vv) "%"; eauto.
    iDestruct (big_sepM2_insert_acc with "Ham") as "[Hbuf Ham]"; eauto.
    rewrite H2.
    iApply "HΦ".
    iFrame.

    iIntros "!>" (b') "Hbuf".
    iExists _, _, _; iFrame.
    iSplitR; first eauto.
    replace (am) with (<[a:=v]> am) at 1 by ( apply insert_id; eauto ).
    by iApply "Ham".

  - apply map_get_false in H1; intuition subst.
    erewrite flatid_addr_lookup in H2; eauto.
    iDestruct (big_sepM2_lookup_l_none with "Ham") as "%"; eauto.
    rewrite H1.
    iApply "HΦ".
    iSplitR; first done.
    iExists _, _, _. iFrame. done.
Qed.

Theorem wp_BufMap__Ndirty l m stk E1 :
  {{{
    is_bufmap l m
  }}}
    BufMap__Ndirty #l @ stk ; E1
  {{{
    (n : u64), RET #n;
    ⌜uint.nat n = size (filter (λ x, (snd x).(bufDirty) = true) m)⌝ ∗
    is_bufmap l m}}}.
Proof using.
  iIntros (Φ) "Hisbufmap HΦ".
  iDestruct "Hisbufmap" as (addrs bm am) "(Haddrs & Hismap & % & Hmap)".
  wp_call.
  wp_loadField.
  wp_apply (wp_MapLen with "Hismap").
  iIntros "[%Hmap_size Hismap]".
  wp_pures.
  wp_apply wp_ref_to; eauto.
  iIntros (n_l) "Hn".
  wp_loadField.

  iDestruct (big_sepM2_dom with "Hmap") as %Hdom.
  iDestruct (big_sepM2_sepM_1 with "Hmap") as "Hmap".
  iDestruct (big_sepM_flatid_addr_map_1 with "Hmap") as "Hmap"; eauto.

  wp_apply (wp_MapIter_3 _ _ _ _ _
    (λ (bmtodo bmdone : gmap u64 loc),
     ∃ (n : u64),
      ∃ (mtodo mdone : gmap addr buf) (amdone amtodo : gmap addr loc),
      "Hn" ∷ n_l ↦[uint64T] #n ∗
      "%Hn" ∷ ⌜uint.nat n = size (filter (λ x, (x.2).(bufDirty) = true) mdone)⌝ ∗
        "%Hpm" ∷ ⌜m = mtodo ∪ mdone ∧
                  dom mtodo ## dom mdone ∧
                  am = amtodo ∪ amdone
                  ⌝ ∗
        "%Hamtodo" ∷ ⌜flatid_addr_map bmtodo amtodo ∧ dom amtodo = dom mtodo⌝ ∗
        "Htodo" ∷ ( [∗ map] fa↦b ∈ bmtodo, ∃ a, ⌜fa = addr2flat a⌝ ∗
                                           (∃ y2 : buf, ⌜mtodo !! a = Some y2⌝ ∗ is_buf b a y2) ) ∗
        "Hbufs" ∷ [∗ map] a↦bufptr;buf ∈ amdone;mdone, is_buf bufptr a buf
    )%I
    with "Hismap [Hmap Hn]").
  {
    iExists (W64 0), m, ∅, ∅, am.
    rewrite big_sepM2_empty.
    iFrame.
    iPureIntro.
    split.
    - rewrite map_filter_empty //.
    - rewrite !right_id_L //.
  }
  {
    iIntros (k v bmtodo bmdone Φi).
    iModIntro.
    iIntros "[Hi %Hp] HΦ".
    iNamed "Hi".
    wp_pures.
    iDestruct (big_sepM_delete with "Htodo") as "[Hv Htodo]"; intuition eauto.
    iDestruct "Hv" as (a) "[-> Hv]".
    iDestruct "Hv" as (vbuf) "[% Hbuf]".
    wp_apply (wp_buf_loadField_dirty with "Hbuf"); iIntros "Hbuf".
    iDestruct (is_buf_valid_addr with "Hbuf") as %Ha_valid.
    assert (amtodo !! a = Some v) as Ham_lookup.
    { destruct H4 as [Hfwd Hrev].
      apply Hrev in H7 as (a' & Hvalid & Heq%(addr2flat_eq) & Hlookup);
        subst; eauto. }
    wp_if_destruct.
    { wp_load.
      wp_store.
      iModIntro.
      iApply "HΦ".
      iExists _, (delete a mtodo), (<[a:=vbuf]> mdone), (<[a:=v]> amdone), (delete a amtodo).
      iFrame.

      iSplitR.
      { iPureIntro.
        repeat match goal with
               | H: flatid_addr_map ?fm ?am |- _ =>
                 lazymatch goal with
                 | H2: size fm = size am |- _ => fail
                 | _ => pose proof (flatid_addr_map_size H)
                 end
               end.
        rewrite map_filter_insert_True //.
        rewrite map_size_insert_None.
        - rewrite -Hn.
          assert (uint.nat n ≤ size mdone)%nat.
          { rewrite Hn.
            apply map_size_filter. }
          assert (Z.of_nat (size bm) < 2^64).
          { rewrite Hmap_size.
            word. }
          assert (size mtodo + size mdone = size m)%nat.
          { replace m.
            rewrite !map_size_dom dom_union_L size_union //. }
          assert (size bmtodo + size bmdone = size bm)%nat.
          { replace bm.
            rewrite !map_size_dom dom_union_L size_union //. }
          assert (size am = size m).
          { rewrite !map_size_dom. congruence. }
          assert (Z.of_nat (size m) < 2^64) by lia.
          assert (0 < size mtodo)%nat.
          { eauto using map_size_nonzero_lookup. }
          word.
        - rewrite map_lookup_filter_None_2 //.
          left.
          apply elem_of_dom_2 in H3.
          apply not_elem_of_dom.
          set_solver. }
      iSplitR.
      { iPureIntro. rewrite -> !union_delete_insert by eauto.
        split_and!; auto.
        set_solver. }
      iSplitR.
      { iPureIntro. split.
        { apply flatid_addr_delete; eauto. }
        rewrite ?dom_delete_L. congruence. }
      iSplitL "Htodo".
      { iApply (big_sepM_mono with "Htodo"). iIntros (k x Hkx) "H".
        iDestruct "H" as (a0) "[-> H]". iDestruct "H" as (y2) "[% H]".
        iExists a0. iSplitR; first eauto.
        iExists y2. iFrame.
        destruct (decide (a = a0)); subst.
        { rewrite lookup_delete in Hkx. congruence. }
        rewrite lookup_delete_ne; eauto.
      }
      iDestruct (big_sepM2_dom with "Hbufs") as %Hdom_bufs.
      rewrite big_sepM2_insert.
      { iFrame. }
      - apply not_elem_of_dom. apply elem_of_dom_2 in H3.
        rewrite Hdom_bufs. set_solver.
      - apply not_elem_of_dom. apply elem_of_dom_2 in H3.
        set_solver.
    }
    { iModIntro.
      iApply "HΦ".
      iExists _, (delete a mtodo), (<[a:=vbuf]> mdone), (<[a:=v]> amdone), (delete a amtodo).
      iFrame "Hn".
      iSplitR.
      { iPureIntro.
        rewrite map_filter_insert_not' //=.
        - congruence.
        - intros.
          exfalso.
          apply elem_of_dom_2 in H3.
          apply elem_of_dom_2 in H9.
          set_solver.
      }
      iSplitR.
      { iPureIntro. rewrite -> !union_delete_insert by eauto.
        split_and!; auto.
        set_solver. }
      iSplitR.
      { iPureIntro. split.
        { apply flatid_addr_delete; eauto. }
        rewrite ?dom_delete_L. congruence. }
      iSplitL "Htodo".
      { iApply (big_sepM_mono with "Htodo"). iIntros (k x Hkx) "H".
        iDestruct "H" as (a0) "[-> H]". iDestruct "H" as (y2) "[% H]".
        iExists a0. iSplitR; first eauto.
        iExists y2. iFrame.
        destruct (decide (a = a0)); subst.
        { rewrite lookup_delete in Hkx. congruence. }
        rewrite lookup_delete_ne; eauto.
      }
      iDestruct (big_sepM2_dom with "Hbufs") as %Hdom_bufs.
      rewrite big_sepM2_insert.
      { iFrame. }
      - apply not_elem_of_dom. apply elem_of_dom_2 in H3.
        rewrite Hdom_bufs. set_solver.
      - apply not_elem_of_dom. apply elem_of_dom_2 in H3.
        set_solver.
    }
  }

  iIntros "(Hmap & Hi)". iNamed "Hi".
  wp_pures.
  wp_load.
  iModIntro.
  iApply "HΦ". iFrame.

  assert (mtodo = ∅).
  { apply dom_empty_iff_L.
    intuition subst.
    rewrite -H3.
    apply flatid_addr_empty_1 in H2; subst.

    set_solver. }
  assert (amtodo = ∅).
  { intuition subst.
    apply flatid_addr_empty_1 in H3; subst; auto. }
  subst.
  destruct Hpm as (Hm & _ & Ham).
  rewrite left_id_L in Hm; subst mdone.
  rewrite left_id_L in Ham; subst amdone.
  iSplitR; first by done.
  by iFrame.
Qed.

Theorem wp_BufMap__DirtyBufs l m stk E1 :
  {{{
    is_bufmap l m
  }}}
    BufMap__DirtyBufs #l @ stk ; E1
  {{{
    (s : Slice.t) (bufptrlist : list loc), RET (slice_val s);
    own_slice s ptrT (DfracOwn 1) bufptrlist ∗
    let dirtybufs := filter (λ x, (snd x).(bufDirty) = true) m in
    [∗ maplist] a ↦ b;bufptr ∈ dirtybufs;bufptrlist,
      is_buf bufptr a b
  }}}.
Proof using.
  iIntros (Φ) "Hisbufmap HΦ".
  iDestruct "Hisbufmap" as (addrs bm am) "(Haddrs & Hismap & % & Hmap)".
  wp_call.
  wp_apply wp_ref_of_zero; eauto.
  iIntros (bufs) "Hbufs".
  wp_loadField.

  iDestruct (big_sepM2_dom with "Hmap") as %Hdom.
  iDestruct (big_sepM2_sepM_1 with "Hmap") as "Hmap".
  iDestruct (big_sepM_flatid_addr_map_1 with "Hmap") as "Hmap"; eauto.

  wp_apply (wp_MapIter_3 _ _ _ _ _
    (λ (bmtodo bmdone : gmap u64 loc),
      ∃ (bufptrslice : Slice.t) (bufptrlist : list loc) (mtodo mdone : gmap addr buf) (amtodo : gmap addr loc),
        "%Hpm" ∷ ⌜m = mtodo ∪ mdone ∧ dom mtodo ## dom mdone⌝ ∗
        "%Hamtodo" ∷ ⌜flatid_addr_map bmtodo amtodo ∧ dom amtodo = dom mtodo⌝ ∗
        "Htodo" ∷ ( [∗ map] fa↦b ∈ bmtodo, ∃ a, ⌜fa = addr2flat a⌝ ∗
                                           (∃ y2 : buf, ⌜mtodo !! a = Some y2⌝ ∗ is_buf b a y2) ) ∗
        "Hbufs" ∷ bufs ↦[slice.T ptrT] (slice_val bufptrslice) ∗
        "Hbufptrslice" ∷ own_slice bufptrslice ptrT (DfracOwn 1) bufptrlist ∗
        "Hresult" ∷ ( [∗ maplist] a↦b;bufptr ∈ filter (λ x, (x.2).(bufDirty) = true) mdone;bufptrlist,
                                is_buf bufptr a b )
    )%I
    with "Hismap [Hmap Hbufs]").
  {
    iExists Slice.nil, nil, m, ∅, am.
    iSplitR.
    { iPureIntro. split. { rewrite right_id; eauto. } set_solver. }
    iSplitR.
    { iPureIntro. eauto. }
    iFrame "Hmap". iFrame "Hbufs".
    iSplitR.
    { iApply own_slice_zero. }
    rewrite map_filter_empty. iApply big_sepML_empty.
  }
  {
    iIntros (k v bmtodo bmdone Φi).
    iModIntro.
    iIntros "[Hi %Hp] HΦ".
    iNamed "Hi".
    wp_pures.
    iDestruct (big_sepM_delete with "Htodo") as "[Hv Htodo]"; intuition eauto.
    iDestruct "Hv" as (a) "[-> Hv]".
    iDestruct "Hv" as (vbuf) "[% Hbuf]".
    wp_apply (wp_buf_loadField_dirty with "Hbuf"); iIntros "Hbuf".
    wp_if_destruct.
    { wp_load.
      wp_apply (wp_SliceAppend with "Hbufptrslice").
      iIntros (s') "Hbufptrslice".
      wp_store.
      iApply "HΦ".
      iExists _, _, (delete a mtodo), (<[a:=vbuf]> mdone), (delete a amtodo).
      iSplitR.
      { iPureIntro. split.
        { rewrite union_delete_insert; eauto. }
        set_solver. }
      iSplitR.
      { iPureIntro. split.
        { apply flatid_addr_delete; eauto.
          eapply flatid_addr_lookup_valid. { apply H4. }
          apply elem_of_dom. rewrite H5. apply elem_of_dom. eauto. }
        rewrite ?dom_delete_L. congruence. }
      iSplitL "Htodo".
      { iApply (big_sepM_mono with "Htodo"). iIntros (k x Hkx) "H".
        iDestruct "H" as (a0) "[-> H]". iDestruct "H" as (y2) "[% H]".
        iExists a0. iSplitR; first eauto.
        iExists y2. iFrame.
        destruct (decide (a = a0)); subst.
        { rewrite lookup_delete in Hkx. congruence. }
        rewrite lookup_delete_ne; eauto.
      }
      iFrame "Hbufs". iFrame "Hbufptrslice".
      rewrite map_filter_insert_True; last by eauto.
      iApply big_sepML_insert_app.
      { rewrite map_lookup_filter_None. left.
        apply not_elem_of_dom.
        assert (is_Some (mtodo !! a)) as Hsome by eauto.
        apply elem_of_dom in Hsome. set_solver. }
      by iFrame.
    }
    { iApply "HΦ".
      iExists _, _, (delete a mtodo), (<[a:=vbuf]> mdone), (delete a amtodo).
      iSplitR.
      { iPureIntro. split.
        { rewrite union_delete_insert; eauto. }
        set_solver. }
      iSplitR.
      { iPureIntro. split.
        { apply flatid_addr_delete; eauto.
          eapply flatid_addr_lookup_valid. { apply H4. }
          apply elem_of_dom. rewrite H5. apply elem_of_dom. eauto. }
        rewrite ?dom_delete_L. congruence. }
      iSplitL "Htodo".
      { iApply (big_sepM_mono with "Htodo"). iIntros (k x Hkx) "H".
        iDestruct "H" as (a0) "[-> H]". iDestruct "H" as (y2) "[% H]".
        iExists a0. iSplitR; first eauto.
        iExists y2. iFrame.
        destruct (decide (a = a0)); subst.
        { rewrite lookup_delete in Hkx. congruence. }
        rewrite lookup_delete_ne; eauto.
      }
      iFrame "Hbufs". iFrame "Hbufptrslice".
      rewrite map_filter_insert_False.
      2: { simpl. congruence. }
      rewrite delete_notin.
      { by iFrame. }
      apply not_elem_of_dom.
      assert (is_Some (mtodo !! a)) as Hsome by eauto.
      apply (elem_of_dom (D:=gset addr)) in Hsome. set_solver.
    }
  }

  iIntros "(Hmap & Hi)". iNamed "Hi".
  wp_pures.
  wp_load.
  iApply "HΦ". iFrame.
  intuition subst.

  assert (mtodo = ∅); subst.
  { apply dom_empty_iff_L.
    rewrite -H3.
    apply flatid_addr_empty_1 in H2; subst.
    set_solver.
  }

  rewrite left_id. by iFrame.
Qed.

End heap.
