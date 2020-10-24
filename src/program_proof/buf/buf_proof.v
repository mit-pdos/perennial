From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.


From Perennial.Helpers Require Import bytes.
From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.goose_nfsd Require Import buf.
From Perennial.program_proof Require Import util_proof disk_lib.
From Perennial.program_proof Require Export buf.defs.
From Perennial.program_proof Require Import addr.addr_proof wal.abstraction.
From Perennial.Helpers Require Import NamedProps.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

Remove Hints fractional.into_sep_fractional : typeclass_instances.

(* TODO(tej): we don't get these definitions due to not importing the buftxn
proof; should fix that *)
Notation object := ({K & bufDataT K}).

Section heap.
Context `{!heapG Σ}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Definition is_buf_data {K} (s : Slice.t) (d : bufDataT K) (a : addr) : iProp Σ :=
  match d with
  | bufBit b => ∃ (b0 : u8), slice.is_slice_small s u8T 1 (#b0 :: nil) ∗
    ⌜ get_bit b0 (word.modu a.(addrOff) 8) = b ⌝
  | bufInode i => slice.is_slice_small s u8T 1 (inode_to_vals i)
  | bufBlock b => slice.is_slice_small s u8T 1 (Block_to_vals b)
  end.

Definition is_buf_without_data (bufptr : loc) (a : addr) (o : buf) (data : Slice.t) : iProp Σ :=
  ∃ (sz : u64),
    "Haddr" ∷ bufptr ↦[Buf.S :: "Addr"] (addr2val a) ∗
    "Hsz" ∷ bufptr ↦[Buf.S :: "Sz"] #sz ∗
    "Hdata" ∷ bufptr ↦[Buf.S :: "Data"] (slice_val data) ∗
    "Hdirty" ∷ bufptr ↦[Buf.S :: "dirty"] #o.(bufDirty) ∗
    "%" ∷ ⌜ valid_addr a ∧ valid_off o.(bufKind) a.(addrOff) ⌝ ∗
    "->" ∷ ⌜ sz = bufSz o.(bufKind) ⌝ ∗
    "%" ∷ ⌜ #bufptr ≠ #null ⌝.

Definition is_buf (bufptr : loc) (a : addr) (o : buf) : iProp Σ :=
  ∃ (data : Slice.t),
    "Hisbuf_without_data" ∷ is_buf_without_data bufptr a o data ∗
    "Hbufdata" ∷ is_buf_data data o.(bufData) a.

Definition is_bufmap (bufmap : loc) (bm : gmap addr buf) : iProp Σ :=
  ∃ (mptr : loc) (m : gmap u64 loc) (am : gmap addr loc),
    bufmap ↦[BufMap.S :: "addrs"] #mptr ∗
    is_map mptr m ∗
    ⌜ flatid_addr_map m am ⌝ ∗
    [∗ map] a ↦ bufptr; buf ∈ am; bm,
      is_buf bufptr a buf.

Theorem is_buf_not_null bufptr a o :
  is_buf bufptr a o -∗ ⌜ #bufptr ≠ #null ⌝.
Proof.
  iIntros "Hisbuf".
  iNamed "Hisbuf".
  iNamed "Hisbuf_without_data".
  eauto.
Qed.

Definition objKind (obj: object): bufDataKind := projT1 obj.
Definition objData (obj: object): bufDataT (objKind obj) := projT2 obj.

Definition data_has_obj (data: list byte) (a:addr) (obj: object) : Prop :=
  match objData obj with
  | bufBit b =>
    ∃ b0, data = [b0] ∧
          get_bit b0 (word.modu (addrOff a) 8) = b
  | bufInode i => vec_to_list i = data
  | bufBlock b => vec_to_list b = data
  end.

Theorem data_has_obj_to_buf_data s a obj data :
  data_has_obj data a obj →
  is_slice_small s u8T 1 data -∗ is_buf_data s (objData obj) a.
Proof.
  rewrite /data_has_obj /is_buf_data.
  iIntros (?) "Hs".
  destruct (objData obj); subst.
  - destruct H as (b' & -> & <-).
    iExists b'; iFrame.
    auto.
  - iFrame.
  - iFrame.
Qed.

Theorem is_buf_data_has_obj s a obj :
  is_buf_data s (objData obj) a ⊣⊢ ∃ data, is_slice_small s u8T 1 data ∗
                                           ⌜data_has_obj data a obj⌝.
Proof.
  iSplit; intros.
  - rewrite /data_has_obj /is_buf_data.
    destruct (objData obj); subst; eauto.
    iDestruct 1 as (b') "[Hs %]".
    iExists [b']; iFrame.
    eauto.
  - iDestruct 1 as (data) "[Hs %]".
    iApply (data_has_obj_to_buf_data with "Hs"); auto.
Qed.

Theorem wp_buf_loadField_sz bufptr a b :
  {{{
    is_buf bufptr a b
  }}}
    struct.loadF buf.Buf.S "Sz" #bufptr
  {{{
    RET #(bufSz b.(bufKind));
    is_buf bufptr a b
  }}}.
Proof using.
  iIntros (Φ) "Hisbuf HΦ".
  iNamed "Hisbuf".
  iNamed "Hisbuf_without_data".
  wp_loadField.
  iApply "HΦ".
  iExists _. iFrame. iExists _. iFrame. done.
Qed.

Theorem wp_buf_loadField_addr bufptr a b :
  {{{
    is_buf bufptr a b
  }}}
    struct.loadF buf.Buf.S "Addr" #bufptr
  {{{
    RET (addr2val a);
    is_buf bufptr a b
  }}}.
Proof using.
  iIntros (Φ) "Hisbuf HΦ".
  iNamed "Hisbuf".
  iNamed "Hisbuf_without_data".
  wp_loadField.
  iApply "HΦ".
  iExists _; iFrame. iExists _; iFrame. done.
Qed.

Theorem wp_buf_loadField_dirty bufptr a b :
  {{{
    is_buf bufptr a b
  }}}
    struct.loadF buf.Buf.S "dirty" #bufptr
  {{{
    RET #(b.(bufDirty));
    is_buf bufptr a b
  }}}.
Proof using.
  iIntros (Φ) "Hisbuf HΦ".
  iNamed "Hisbuf".
  iNamed "Hisbuf_without_data".
  wp_loadField.
  iApply "HΦ".
  iExists _; iFrame. iExists _; iFrame. done.
Qed.

Theorem wp_buf_wd_loadField_sz bufptr a b dataslice :
  {{{
    is_buf_without_data bufptr a b dataslice
  }}}
    struct.loadF buf.Buf.S "Sz" #bufptr
  {{{
    RET #(bufSz b.(bufKind));
    is_buf_without_data bufptr a b dataslice
  }}}.
Proof using.
  iIntros (Φ) "Hisbuf_without_data HΦ".
  iNamed "Hisbuf_without_data".
  wp_loadField.
  iApply "HΦ".
  iExists _. iFrame. done.
Qed.

Theorem wp_buf_wd_loadField_addr bufptr a b dataslice :
  {{{
    is_buf_without_data bufptr a b dataslice
  }}}
    struct.loadF buf.Buf.S "Addr" #bufptr
  {{{
    RET (addr2val a);
    is_buf_without_data bufptr a b dataslice
  }}}.
Proof using.
  iIntros (Φ) "Hisbuf_without_data HΦ".
  iNamed "Hisbuf_without_data".
  wp_loadField.
  iApply "HΦ".
  iExists _. iFrame. done.
Qed.

Theorem wp_buf_wd_loadField_dirty bufptr a b dataslice :
  {{{
    is_buf_without_data bufptr a b dataslice
  }}}
    struct.loadF buf.Buf.S "dirty" #bufptr
  {{{
    RET #(b.(bufDirty));
    is_buf_without_data bufptr a b dataslice
  }}}.
Proof using.
  iIntros (Φ) "Hisbuf_without_data HΦ".
  iNamed "Hisbuf_without_data".
  wp_loadField.
  iApply "HΦ".
  iExists _. iFrame. done.
Qed.

Theorem is_buf_return_data bufptr a b dataslice (v' : bufDataT b.(bufKind)) :
  is_buf_data dataslice v' a ∗
  is_buf_without_data bufptr a b dataslice -∗
  is_buf bufptr a (Build_buf b.(bufKind) v' b.(bufDirty)).
Proof.
  iIntros "[Hbufdata Hisbuf_without_data]".
  iExists _. iFrame.
Qed.

Theorem wp_buf_loadField_data bufptr a b :
  {{{
    is_buf bufptr a b
  }}}
    struct.loadF buf.Buf.S "Data" #bufptr
  {{{
    (vslice : Slice.t), RET (slice_val vslice);
    is_buf_data vslice b.(bufData) a ∗
    is_buf_without_data bufptr a b vslice
  }}}.
Proof using.
  iIntros (Φ) "Hisbuf HΦ".
  iNamed "Hisbuf".
  iNamed "Hisbuf_without_data".
  wp_loadField.
  iApply "HΦ".
  iFrame. iExists _; iFrame. done.
Qed.

Theorem wp_buf_storeField_data bufptr a b (vslice: Slice.t) k' (v' : bufDataT k') :
  {{{
    is_buf bufptr a b ∗
    is_buf_data vslice v' a ∗
    ⌜ k' = b.(bufKind) ⌝
  }}}
    struct.storeF buf.Buf.S "Data" #bufptr (slice_val vslice)
  {{{
    RET #();
    is_buf bufptr a (Build_buf k' v' b.(bufDirty))
  }}}.
Proof using.
  iIntros (Φ) "(Hisbuf & Hisbufdata & %) HΦ".
  iNamed "Hisbuf".
  iClear "Hbufdata".
  iNamed "Hisbuf_without_data".
  wp_apply (wp_storeField with "Hdata"); eauto.
  { eapply slice_val_ty. } (* XXX why does [val_ty] fail? *)
  iIntros "Hdata".
  iApply "HΦ".
  iExists _; iFrame. iExists _; iFrame. intuition subst. done.
Qed.

Theorem wp_MkBufMap :
  {{{
    emp
  }}}
    MkBufMap #()
  {{{
    (l : loc), RET #l;
    is_bufmap l ∅
  }}}.
Proof.
  iIntros (Φ) "Hemp HΦ".

Opaque zero_val. (* XXX can we avoid this? *)
  wp_call.
  wp_apply wp_NewMap.
  iIntros (mref) "Hmref".
  wp_apply wp_allocStruct; eauto.
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

Theorem wp_BufMap__Insert l m bl a b :
  {{{
    is_bufmap l m ∗
    is_buf bl a b
  }}}
    BufMap__Insert #l #bl
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
  iApply "HΦ".
  iExists _, _, _. iFrame.
  iSplitR.
  { iPureIntro. apply flatid_addr_insert; eauto. }

  (* Two cases: either we are inserting a new addr or overwriting *)
  destruct (am !! a) eqn:Heq.
  - iDestruct (big_sepM2_lookup_1_some with "Ham") as (v2) "%"; eauto.
    iDestruct (big_sepM2_insert_acc with "Ham") as "[Hcur Hacc]"; eauto.
    iApply "Hacc".
    iExists _; iFrame. iExists _; iFrame. done.

  - iDestruct (big_sepM2_lookup_1_none with "Ham") as "%"; eauto.
    iApply big_sepM2_insert; eauto.
    iFrame "Ham".
    iExists _; iFrame. iExists _; iFrame. done.
Qed.

Theorem wp_BufMap__Del l m a :
  {{{
    is_bufmap l m ∗
    ⌜ valid_addr a ⌝
  }}}
    BufMap__Del #l (addr2val a)
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
  iApply "HΦ".
  iExists _, _, _. iFrame.
  iSplitR.
  { iPureIntro. apply flatid_addr_delete; eauto. }

  (* Two cases: either we are deleting an existing addr or noop *)
  destruct (am !! a) eqn:Heq.
  - iDestruct (big_sepM2_lookup_1_some with "Ham") as (v2) "%"; eauto.
    iDestruct (big_sepM2_delete with "Ham") as "[Hcur Hacc]"; eauto.

  - iDestruct (big_sepM2_lookup_1_none with "Ham") as "%"; eauto.
    rewrite delete_notin; eauto.
    rewrite delete_notin; eauto.
Qed.

Theorem wp_BufMap__Lookup l m a :
  {{{
    is_bufmap l m ∗
    ⌜ valid_addr a ⌝
  }}}
    BufMap__Lookup #l (addr2val a)
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
    iDestruct (big_sepM2_lookup_1_some with "Ham") as (vv) "%"; eauto.
    iDestruct (big_sepM2_insert_acc with "Ham") as "[Hbuf Ham]"; eauto.
    rewrite H2.
    iApply "HΦ".
    iFrame.

    iIntros (b') "Hbuf".
    iExists _, _, _.
    iFrame.
    iSplitR; first eauto.
    replace (am) with (<[a:=v]> am) at 1 by ( apply insert_id; eauto ).
    iApply "Ham". iFrame.

  - apply map_get_false in H1; intuition subst.
    erewrite flatid_addr_lookup in H2; eauto.
    iDestruct (big_sepM2_lookup_1_none with "Ham") as "%"; eauto.
    rewrite H1.
    iApply "HΦ".
    iSplitR; first done.
    iExists _, _, _. iFrame. done.
Qed.

Theorem wp_BufMap__DirtyBufs l m :
  {{{
    is_bufmap l m
  }}}
    BufMap__DirtyBufs #l
  {{{
    (s : Slice.t) (bufptrlist : list loc), RET (slice_val s);
    is_slice s (refT (struct.t Buf.S)) 1 bufptrlist ∗
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

  wp_apply (wp_MapIter_3 _ _ _ _
    (λ (bmtodo bmdone : gmap u64 loc),
      ∃ (bufptrslice : Slice.t) (bufptrlist : list loc) (mtodo mdone : gmap addr buf) (amtodo : gmap addr loc),
        "%Hpm" ∷ ⌜m = mtodo ∪ mdone ∧ dom (gset addr) mtodo ## dom (gset addr) mdone⌝ ∗
        "%Hamtodo" ∷ ⌜flatid_addr_map bmtodo amtodo ∧ dom (gset addr) amtodo = dom (gset addr) mtodo⌝ ∗
        "Htodo" ∷ ( [∗ map] fa↦b ∈ bmtodo, ∃ a, ⌜fa = addr2flat a⌝ ∗
                                           (∃ y2 : buf, ⌜mtodo !! a = Some y2⌝ ∗ is_buf b a y2) ) ∗
        "Hbufs" ∷ bufs ↦[slice.T (refT (struct.t Buf.S))] (slice_val bufptrslice) ∗
        "Hbufptrslice" ∷ is_slice bufptrslice (refT (struct.t Buf.S)) 1 bufptrlist ∗
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
    { iApply is_slice_zero. }
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
        { rewrite Map.delete_insert_union; eauto. }
        set_solver. }
      iSplitR.
      { iPureIntro. split.
        { apply flatid_addr_delete; eauto.
          eapply flatid_addr_lookup_valid. { apply H4. }
          apply (elem_of_dom (D:=gset addr)). rewrite H5. apply elem_of_dom. eauto. }
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
      rewrite map_filter_insert; last by eauto.
      iApply big_sepML_insert_app.
      { rewrite map_filter_lookup_None. left.
        apply (not_elem_of_dom (D:=gset addr)).
        assert (is_Some (mtodo !! a)) as Hsome by eauto.
        apply (elem_of_dom (D:=gset addr)) in Hsome. set_solver. }
      iFrame.
    }
    { iApply "HΦ".
      iExists _, _, (delete a mtodo), (<[a:=vbuf]> mdone), (delete a amtodo).
      iSplitR.
      { iPureIntro. split.
        { rewrite Map.delete_insert_union; eauto. }
        set_solver. }
      iSplitR.
      { iPureIntro. split.
        { apply flatid_addr_delete; eauto.
          eapply flatid_addr_lookup_valid. { apply H4. }
          apply (elem_of_dom (D:=gset addr)). rewrite H5. apply elem_of_dom. eauto. }
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
      rewrite map_filter_insert_not_delete.
      2: { simpl. congruence. }
      rewrite delete_notin.
      { iFrame. }
      apply (not_elem_of_dom (D:=gset addr)).
      assert (is_Some (mtodo !! a)) as Hsome by eauto.
      apply (elem_of_dom (D:=gset addr)) in Hsome. set_solver.
    }
  }

  iIntros "(Hmap & Hi)". iNamed "Hi".
  wp_pures.
  wp_load.
  iApply "HΦ". iFrame.
  intuition subst.
  rewrite (dom_empty_inv_L (D:=gset addr) mtodo).
  { rewrite left_id. iFrame. }

  rewrite -H3.
  apply flatid_addr_empty_1 in H2; subst.
  set_solver.
Qed.

Definition extract_nth (b : Block) (elemsize : nat) (n : nat) : list val :=
  drop (n * elemsize) (take ((S n) * elemsize) (Block_to_vals b)).

Lemma roundup_multiple a b:
  b > 0 ->
  (a*b-1) `div` b + 1 = a.
Proof.
  intros.
  erewrite <- Zdiv_unique with (r := b-1) (q := a-1).
  - lia.
  - lia.
  - lia.
Qed.

Definition is_bufData_at_off {K} (b : Block) (off : u64) (d : bufDataT K) : Prop :=
  valid_off K off ∧
  match d with
  | bufBlock d => b = d
  | bufInode i => extract_nth b inode_bytes ((int.nat off)/(inode_bytes*8)) = inode_to_vals i
  | bufBit d => ∃ (b0 : u8), extract_nth b 1 ((int.nat off)/8) = #b0 :: nil ∧
      get_bit b0 (word.modu off 8) = d
  end.

Lemma buf_mapsto_non_null b a:
  b ↦[Buf.S :: "Addr"] addr2val a -∗ ⌜ b ≠ null ⌝.
Proof.
  iIntros "Hb.a".
  iDestruct (heap_mapsto_non_null with "[Hb.a]") as %Hnotnull.
  { rewrite struct_field_mapsto_eq /struct_field_mapsto_def //= struct_mapsto_eq /struct_mapsto_def.
    iDestruct "Hb.a" as "[[[Hb _] _] _]".
    repeat rewrite loc_add_0. iFrame. }
  eauto.
Qed.

Theorem wp_MkBuf K a data (bufdata : bufDataT K) :
  {{{
    is_buf_data data bufdata a ∗
    ⌜ valid_addr a ∧ valid_off K a.(addrOff) ⌝
  }}}
    MkBuf (addr2val a) #(bufSz K) (slice_val data)
  {{{
    (bufptr : loc), RET #bufptr;
    is_buf bufptr a (Build_buf _ bufdata false)
  }}}.
Proof using.
  iIntros (Φ) "[Hbufdata %] HΦ".
  wp_call.
  wp_apply wp_allocStruct; first by auto.

  iIntros (b) "Hb".
  wp_pures.
  iApply "HΦ".
  iDestruct (struct_fields_split with "Hb") as "(Hb.a & Hb.sz & Hb.data & Hb.dirty & %)".

  iDestruct (buf_mapsto_non_null with "[$]") as %Hnotnull.

  iExists _. iFrame.
  iExists _. iFrame.
  iSplitL; try done.
  iSplitL; try done.

  iPureIntro. congruence.
Qed.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Theorem wp_MkBufLoad K a blk s (bufdata : bufDataT K) :
  {{{
    slice.is_slice_small s u8T 1%Qp (Block_to_vals blk) ∗
    ⌜ is_bufData_at_off blk a.(addrOff) bufdata ⌝ ∗
    ⌜ valid_addr a ⌝
  }}}
    MkBufLoad (addr2val a) #(bufSz K) (slice_val s)
  {{{
    (bufptr : loc), RET #bufptr;
    is_buf bufptr a (Build_buf _ bufdata false)
  }}}.
Proof using.
  iIntros (Φ) "(Hs & % & %) HΦ".
  wp_call.

  iDestruct (slice.is_slice_small_sz with "Hs") as "%".
  destruct H as [Hoff Hatoff].

  wp_apply (wp_SliceSubslice_small with "[$Hs]").
  { rewrite /valid_addr in H0.
    rewrite /valid_off in Hoff.
    unfold block_bytes in *.
    iPureIntro; intuition.
    { destruct K.
      { simpl. repeat word_cleanup. }
      { simpl. repeat word_cleanup. }
      { change (bufSz KindBlock) with (Z.to_nat 4096 * 8)%nat.
        repeat word_cleanup. }
    }
    {
      replace (int.val s.(Slice.sz)) with (length (Block_to_vals blk) : Z).
      2: { word. }
      rewrite length_Block_to_vals. unfold block_bytes.
      repeat word_cleanup.
      destruct K.
      { simpl. repeat word_cleanup. }
      { simpl. simpl in Hoff. repeat word_cleanup. }
      {
        assert (a.(addrOff) = 0) as Hoff0.
        { change (bufSz KindBlock) with (Z.to_nat 4096 * 8)%nat in Hoff.
          word.
        }

        rewrite Hoff0. vm_compute. intros; congruence.
      }
    }
  }

  iIntros (s') "Hs".
  wp_pures.
  wp_apply wp_allocStruct; first by auto.

  iIntros (b) "Hb".
  wp_pures.
  iApply "HΦ".
  iDestruct (struct_fields_split with "Hb") as "(Hb.a & Hb.sz & Hb.data & Hb.dirty & %)".

  iDestruct (buf_mapsto_non_null with "[$]") as %Hnotnull.
  iExists _.
  iSplitR "Hs".
  { iExists _. rewrite /=. iFrame. iPureIntro. intuition eauto. congruence. }

  rewrite /valid_off in Hoff.
Opaque PeanoNat.Nat.div.
  destruct bufdata; cbn; cbn in Hatoff.
  - destruct Hatoff; intuition.
    iExists _.
    iSplitL; last eauto.

    unfold valid_addr in *.
    unfold addr2flat_z in *.
    unfold block_bytes in *.
    intuition idtac.
    word_cleanup.
    rewrite word.unsigned_sub.
    rewrite word.unsigned_add.
    word_cleanup.
    replace (int.val a.(addrOff) + Z.of_nat 1 - 1) with (int.val a.(addrOff)) by lia.

    rewrite -H3 /extract_nth.
    replace (int.nat a.(addrOff) `div` 8 * 1)%nat with (int.nat a.(addrOff) `div` 8)%nat by lia.
    replace (S (int.nat a.(addrOff) `div` 8) * 1)%nat with (S (int.nat a.(addrOff) `div` 8))%nat by lia.
    iExactEq "Hs". f_equal.
    f_equal.
    { rewrite Z2Nat_inj_div; try word.
      eauto. }
    f_equal.
    { rewrite Z2Nat.inj_add; try word.
      rewrite Z2Nat_inj_div; try word.
      change (Z.to_nat 8) with 8%nat.
      word. }

  - iExactEq "Hs"; f_equal.

    unfold valid_addr in *.
    unfold addr2flat_z in *.
    unfold inode_bytes, block_bytes in *.
    intuition idtac.
    word_cleanup.
    rewrite word.unsigned_sub.
    rewrite word.unsigned_add.
    word_cleanup.
    replace (int.val a.(addrOff) + Z.of_nat (Z.to_nat 128 * 8) - 1) with (int.val a.(addrOff) + (128*8-1)) by lia.

    rewrite -Hatoff /extract_nth.
    f_equal.
    { rewrite Z2Nat_inj_div; try word.
      simpl bufSz in *.
      change (Z.to_nat 8) with 8%nat.
      change (Z.to_nat 128) with 128%nat.
      change (128 * 8)%nat with (8 * 128)%nat.
      rewrite -Nat.div_div; try word.
      assert ((int.nat (addrOff a) `div` 8) `mod` 128 = 0)%nat as Hx.
      {
        replace (int.val (addrOff a)) with (Z.of_nat (int.nat (addrOff a))) in Hoff by word.
        rewrite -mod_Zmod in Hoff; try word.
        assert (int.nat (addrOff a) `mod` 1024 = 0)%nat as Hy by lia.
        replace (1024)%nat with (8*128)%nat in Hy by reflexivity.
        rewrite Nat.mod_mul_r in Hy; try word.
      }
      apply Nat.div_exact in Hx; try word.
    }
    f_equal.
    {
      simpl bufSz in *.
      rewrite Z2Nat.inj_add; try word.
      rewrite Z2Nat_inj_div; try word.
      change (Z.to_nat 1) with 1%nat.
      change (Z.to_nat 8) with 8%nat.
      change (Z.to_nat 128) with 128%nat.
      rewrite Z2Nat.inj_add; try word.
      change (Z.to_nat (128*8-1)) with (128*8-1)%nat.

      replace (128 * 8)%nat with (8 * 128)%nat by reflexivity.
      rewrite -Nat.div_div; try word.
      assert ((int.nat (addrOff a) `div` 8) `mod` 128 = 0)%nat as Hx.
      {
        replace (int.val (addrOff a)) with (Z.of_nat (int.nat (addrOff a))) in Hoff by word.
        rewrite -mod_Zmod in Hoff; try word.
        assert (int.nat (addrOff a) `mod` 1024 = 0)%nat as Hy by lia.
        replace (1024)%nat with (8*128)%nat in Hy by reflexivity.
        rewrite Nat.mod_mul_r in Hy; try word.
      }
      apply Nat.div_exact in Hx; try word.
      rewrite mult_comm in Hx.
      replace (S ((int.nat (addrOff a) `div` 8) `div` 128) * 128)%nat
         with (((int.nat (addrOff a) `div` 8) `div` 128) * 128 + 128)%nat by lia.
      rewrite -Hx.

      edestruct (Nat.div_exact (int.nat (addrOff a)) 8) as [_ Hz]; first by lia.
      rewrite -> Hz at 1.
      2: {
        replace (int.val (addrOff a)) with (Z.of_nat (int.nat (addrOff a))) in Hoff by word.
        rewrite -mod_Zmod in Hoff; try word.
        assert (int.nat (addrOff a) `mod` 1024 = 0)%nat as Hy by lia.
        replace (1024)%nat with (8*128)%nat in Hy by reflexivity.
        rewrite Nat.mod_mul_r in Hy; try word.
      }

      rewrite mult_comm. rewrite -> Nat.div_add_l by lia.
      change ((8 * 128 - 1) `div` 8)%nat with (127)%nat.
      lia.
    }

  - intuition subst.
    iExactEq "Hs".

    assert (a.(addrOff) = 0) as Hoff0.
    { replace (bufSz KindBlock) with (Z.to_nat 4096 * 8)%nat in Hoff by reflexivity.
      rewrite /valid_addr /block_bytes /= in H0.
      intuition idtac.
      word_cleanup.
    }
    rewrite Hoff0.
    unfold block_bytes in *.
    change (word.divu 0 8) with (U64 0).
    change (word.add 0 (Z.to_nat 4096 * 8)%nat) with (U64 (4096 * 8)).
    change (word.sub (4096 * 8) 1) with (U64 32767).
    change (word.divu 32767 8) with (U64 4095).
    change (word.add 4095 1) with (U64 4096).
    rewrite firstn_all2.
    2: { rewrite length_Block_to_vals /block_bytes. word. }
    rewrite skipn_O //.
Qed.

Lemma insert_Block_to_vals blk i (v : u8) (Hlt : (i < block_bytes)%nat) :
  <[i := #v]> (Block_to_vals blk) = Block_to_vals (vinsert (Fin.of_nat_lt Hlt) v blk).
Proof.
  rewrite /Block_to_vals /b2val vec_to_list_insert.
  rewrite list_fmap_insert fin_to_nat_to_fin //.
Qed.

(** * Operating on blocks as if they were [nat -> byte]. *)

Definition get_byte (b:Block) (off:Z) : byte :=
  default inhabitant (vec_to_list b !! Z.to_nat off).

Definition update_byte (b:Block) (off:Z) (x:byte) : Block :=
  if decide (0 ≤ off) then
    list_to_block (<[Z.to_nat off:=x]> (vec_to_list b))
  else b.

Hint Unfold block_bytes : word.

Theorem get_update_eq (b:Block) (off:Z) x :
  0 ≤ off < 4096 →
  get_byte (update_byte b off x) off = x.
Proof.
  intros Hbound.
  rewrite /get_byte /update_byte.
  rewrite decide_True; [|word].
  rewrite list_to_block_to_list; [|len].
  rewrite list_lookup_insert; [|len].
  auto.
Qed.

Theorem get_update_ne (b:Block) (off off':Z) x :
  off ≠ off' →
  0 ≤ off' →
  get_byte (update_byte b off x) off' = get_byte b off'.
Proof.
  intros Hne Hbound.
  rewrite /get_byte /update_byte.
  destruct (decide _); auto.
  rewrite list_to_block_to_list; [|len].
  rewrite list_lookup_insert_ne; [|word].
  auto.
Qed.

Theorem get_bit_ok b0 (off: u64) :
  (int.val off < 8) →
  get_bit b0 off = default false (byte_to_bits b0 !! int.nat off).
Proof.
  intros Hbound.
  bit_cases off; byte_cases b0; vm_refl.
Qed.

Definition install_one_bit (src dst:byte) (bit:nat) : byte :=
  (* bit in src we should copy *)
  let b := default false (byte_to_bits src !! bit) in
  let dst'_bits := <[bit:=b]> (byte_to_bits dst) in
  let dst' := bits_to_byte dst'_bits in
  dst'.

Lemma install_one_bit_spec src dst (bit: nat) :
  (bit < 8)%nat →
  ∀ bit', byte_to_bits (install_one_bit src dst bit) !! bit' =
          if (decide (bit = bit')) then byte_to_bits src !! bit
          else byte_to_bits dst !! bit'.
Proof.
  intros Hbound bit'.
  rewrite /install_one_bit.
  rewrite bits_to_byte_to_bits; [|len].
  destruct (decide _); subst.
  - rewrite list_lookup_insert; [|len].
    destruct (byte_to_bits src !! bit') eqn:Hlookup; auto.
    move: Hlookup; rewrite lookup_ge_None; len.
  - rewrite list_lookup_insert_ne //.
Qed.

Lemma default_list_lookup_lt {A:Type} (l: list A) (i: nat) x def :
  i < length l →
  default def (l !! i) = x →
  l !! i = Some x.
Proof.
  destruct (l !! i) eqn:Hlookup; simpl; [congruence|].
  move: Hlookup; rewrite lookup_ge_None; lia.
Qed.

Lemma install_one_bit_id src dst bit :
  (bit < 8)%nat →
  default false (byte_to_bits src !! bit) = default false (byte_to_bits dst !! bit) →
  install_one_bit src dst bit = dst.
Proof.
  intros.
  rewrite /install_one_bit.
  rewrite H0.
  rewrite list_insert_id.
  - rewrite byte_to_bits_to_byte //.
  - eapply default_list_lookup_lt; len; eauto.
Qed.

Lemma mask_bit_ok (b: u8) (bit: u64) :
  int.val bit < 8 →
  word.and b (word.slu (U8 1) (u8_from_u64 bit)) =
  if default false (byte_to_bits b !! int.nat bit) then
    U8 (2^(int.nat bit))
  else U8 0.
Proof.
  intros Hle.
  apply (inj int.val).
  bit_cases bit; byte_cases b; vm_refl.
Qed.

Lemma masks_different (bit:u64) :
  int.val bit < 8 →
  U8 (2^int.nat bit ) ≠ U8 0.
Proof.
  intros Hbound Heq%(f_equal int.val).
  change (int.val (U8 0)) with 0 in Heq.
  move: Heq.
  bit_cases bit; vm_compute; by inversion 1.
Qed.

Theorem wp_installOneBit (src dst: u8) (bit: u64) :
  int.val bit < 8 →
  {{{ True }}}
    installOneBit #src #dst #bit
  {{{ RET #(install_one_bit src dst (int.nat bit)); True }}}.
Proof.
  iIntros (Hbit_bounded Φ) "_ HΦ".
  iSpecialize ("HΦ" with "[//]").
  wp_call.
  wp_apply wp_ref_to; first by val_ty.
  iIntros (new_l) "new_l".
  wp_pures.
  rewrite !mask_bit_ok //.
  wp_if_destruct; wp_pures.
  - rewrite !mask_bit_ok //.
    wp_if_destruct; wp_pures.
    + wp_load. wp_store. wp_load.
      destruct (default false (byte_to_bits src !! int.nat bit)) eqn:?.
      { apply masks_different in H0; auto; contradiction. }
      destruct (default false (byte_to_bits dst !! int.nat bit)) eqn:?; last contradiction.
      iExactEq "HΦ"; do 3 f_equal.
      rewrite /install_one_bit.
      rewrite Heqb0.
      apply (inj byte_to_bits).
      rewrite bits_to_byte_to_bits; [|len].
      bit_cases bit; byte_cases dst; vm_refl.
    + destruct (default false (byte_to_bits src !! int.nat bit)) eqn:?; last contradiction.
      destruct (default false (byte_to_bits dst !! int.nat bit)) eqn:?; first contradiction.
      wp_load. wp_store. wp_load.
      iExactEq "HΦ"; do 3 f_equal.
      rewrite /install_one_bit.
      rewrite Heqb1.
      apply (inj byte_to_bits).
      rewrite bits_to_byte_to_bits; [|len].
      bit_cases bit; byte_cases dst; vm_refl.
  - wp_load.
    iExactEq "HΦ"; do 3 f_equal.
    rewrite install_one_bit_id //.
    { lia. }
    destruct (default false _), (default false _); auto.
    + apply masks_different in H0; eauto; contradiction.
    + apply symmetry, masks_different in H0; eauto; contradiction.
Qed.

Theorem wp_Buf__Install bufptr a b blk_s blk :
  {{{
    is_buf bufptr a b ∗
    is_block blk_s 1 blk
  }}}
    Buf__Install #bufptr (slice_val blk_s)
  {{{
    (blk': Block), RET #();
    is_buf bufptr a b ∗
    is_block blk_s 1 blk' ∗
    ⌜ ∀ off (d0 : bufDataT b.(bufKind)),
      is_bufData_at_off blk off d0 ->
      if decide (off = a.(addrOff))
      then is_bufData_at_off blk' off b.(bufData)
      else is_bufData_at_off blk' off d0 ⌝
  }}}.
Proof.
  iIntros (Φ) "[Hisbuf Hblk] HΦ".
  iNamed "Hisbuf".
  iNamed "Hisbuf_without_data".
  wp_call.
  wp_apply util_proof.wp_DPrintf.
  wp_loadField.

  destruct b; simpl in *.
  destruct bufData.
  - wp_pures.
    wp_loadField.
    wp_loadField.



    wp_call.

    assert (∃ (b : u8), Block_to_vals blk !! int.nat (word.divu (addrOff a) 8) = Some #b) as Hsome.
    { rewrite block_byte_index; try word; intros.
      { unfold valid_addr, block_bytes in *. intuition idtac. word. }
      eauto. }
    destruct Hsome as [vb Hsome].

    wp_apply (slice.wp_SliceGet with "[$Hblk]"); eauto.
    iIntros "[Hblk %]".

    iDestruct "Hbufdata" as (x) "[Hbufdata <-]".
    wp_apply (slice.wp_SliceGet with "[$Hbufdata]"); first done.
    iIntros "[Hbufdata %]".

    wp_call.
    wp_apply wp_ref_to; eauto. iIntros (l) "Hvblk".
    wp_pures.
    wp_if_destruct.
    + wp_if_destruct.
      * wp_load. wp_store. wp_load.
        wp_apply (slice.wp_SliceSet with "[$Hblk]"); eauto.
        iIntros "Hblk".
        wp_apply util_proof.wp_DPrintf.

        rewrite insert_Block_to_vals; intros.
        { revert H. rewrite /valid_addr /valid_off /block_bytes /=. word. }

        iApply "HΦ".

        iSplitR "Hblk".
        {
          iExists _. iFrame.
          iSplitL "Hsz".
          { iExists _. iFrame. done. }
          iExists _. iFrame. done.
        }

        iSplitL.
        { iFrame. }

        iPureIntro; intros.
        destruct (decide (off = addrOff a)); subst.
        { rewrite /is_bufData_at_off. intuition eauto.
          eexists. admit.
        }

        admit.

      * wp_load. wp_store. wp_load.
        wp_apply (slice.wp_SliceSet with "[$Hblk]"); eauto.
        iIntros "Hblk".
        wp_apply util_proof.wp_DPrintf.
        iApply "HΦ".
        admit.

    + wp_load.
      wp_apply (slice.wp_SliceSet with "[$Hblk]"); eauto.
      iIntros "Hblk".
      wp_apply util_proof.wp_DPrintf.
      iApply "HΦ".
      admit.

  - wp_pures.
    wp_loadField.
    wp_pures.
    wp_loadField.
    wp_pures.
    wp_if_destruct.
    2: {
      exfalso. apply Heqb; clear Heqb.
      unfold valid_off in *. (* XXX there is no [int.val] here.. *)
      admit.
    }

    wp_loadField.
    wp_loadField.
    wp_loadField.
    wp_call.

    wp_apply (wp_SliceTake' with "Hbufdata").
    { rewrite /inode_to_vals fmap_length vec_to_list_length /inode_bytes. word. }
    iIntros "Hbufdata".

    iDestruct (slice.is_slice_small_sz with "Hblk") as "%Hlen".
    rewrite length_Block_to_vals /block_bytes in Hlen.
    wp_apply wp_SliceSkip'.
    { replace (int.val blk_s.(Slice.sz)) with 4096 by lia. iPureIntro.
      word_cleanup. eapply Z.div_le_upper_bound; try lia.
      rewrite /valid_addr /block_bytes in H. word. }

    wp_apply (wp_SliceCopy with "[Hblk Hbufdata]").
    { admit. }
    { admit. }

    iIntros "[Hbufdata Hblk]".
    wp_apply util_proof.wp_DPrintf.
    iApply "HΦ".
    admit.

  - wp_pures.
    wp_loadField.
    wp_loadField.
    wp_pures.
    wp_if_destruct.
    2: {
      exfalso. apply Heqb0; clear Heqb0.
      unfold valid_off in *. (* XXX there is no [int.val] here.. *)
      admit.
    }

    wp_loadField.
    (* XXX stack overflow........ *)
    admit.
Admitted.

Theorem wp_Buf__SetDirty bufptr a b :
  {{{
    is_buf bufptr a b
  }}}
    Buf__SetDirty #bufptr
  {{{
    RET #();
    is_buf bufptr a (Build_buf b.(bufKind) b.(bufData) true)
  }}}.
Proof.
  iIntros (Φ) "Hisbuf HΦ".
  iNamed "Hisbuf".
  iNamed "Hisbuf_without_data".
  wp_call.
  wp_storeField.
  iApply "HΦ".
  iExists _; iFrame. iExists _; iFrame. done.
Qed.

End heap.
