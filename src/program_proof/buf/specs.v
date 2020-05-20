From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.


From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.goose_nfsd Require Import buf.
From Perennial.program_proof Require Import util_proof disk_lib.
From Perennial.program_proof.buf Require Import defs.
From Perennial.program_proof.addr Require Import specs.
From Perennial.program_proof.wal Require Import abstraction.
From Perennial.Helpers Require Import NamedProps.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

Section heap.
Context `{!heapG Σ}.
Context `{!lockG Σ}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Definition is_buf_data {K} (s : Slice.t) (d : bufDataT K) (a : addr) : iProp Σ :=
  match d with
  | bufBit b => ∃ (b0 : u8), slice.is_slice_small s u8T 1%Qp (#b0 :: nil) ∗
    ⌜ get_bit b0 (word.modu a.(addrOff) 8) = b ⌝
  | bufInode i => slice.is_slice_small s u8T 1%Qp (inode_to_vals i)
  | bufBlock b => slice.is_slice_small s u8T 1%Qp (Block_to_vals b)
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
Opaque struct.t.
  iIntros (Φ) "Hisbufmap HΦ".
  iDestruct "Hisbufmap" as (addrs bm am) "(Haddrs & Hismap & % & Hmap)".
  wp_call.
  wp_apply wp_ref_of_zero; eauto.
  iIntros (bufs) "Hbufs".
  wp_loadField.

  iDestruct (big_sepM2_dom with "Hmap") as %Hdom.
  iDestruct (big_sepM2_sepM_1 with "Hmap") as "Hmap".
  iDestruct (big_sepM_flatid_addr_map_1 with "Hmap") as "Hmap"; eauto.

(*
  wp_apply (wp_MapIter_3 _ _ _ _
    (λ (mtodo mdone : gmap u64 loc),
      ∃ (bufptrslice : Slice.t) (bufptrlist : list loc) (bufdone : gmap addr buf),
        "Hbufs" ∷ bufs ↦[slice.T (refT (struct.t Buf.S))] (slice_val bufptrslice) ∗
        "Hbufptrslice" ∷ is_slice bufptrslice (refT (struct.t Buf.S)) 1 bufptrlist ∗
        "Hdone" ∷ ( [∗ maplist] a↦b;bufptr ∈ filter (λ x, (x.2).(bufDirty) = true) bufdone;bufptrlist, is_buf bufptr a b ) ∗
        "Hdoneptr" ∷ ⌜ bufptrlist ⊆ snd <$> map_to_list mdone ⌝ ∗
        
    )%I
    with "Hismap [Hbufs] [Hmap]").
  {
    iExists _, nil.
    iSplitL.
    2: { iApply is_slice_zero. }
    iFrame.
  }
  {
    iIntros (k v Φi).
    iModIntro.
    iIntros "[Hi Hp] HΦ".
    iDestruct "Hp" as (a) "[-> Hp]".
    iDestruct "Hp" as (b) "[% Hp]".
    iDestruct "Hp" as (bl) "[-> Hp]".
    iDestruct "Hi" as (s bufptrlist) "[Hbufs Hbufptrlist]".
    wp_pures.
    wp_apply (wp_buf_loadField_dirty with "Hp"); iIntros "Hp".
    wp_if_destruct.
    { wp_load.
      wp_apply (wp_SliceAppend with "[$Hbufptrlist]"); first eauto.
      { iSplitL; eauto. admit. }
      iIntros (s') "Hbufptrlist".
      wp_store.
      iApply "HΦ".
      iSplitL "Hbufs Hbufptrlist".
      { iExists _, _. iFrame. }
      admit.
    }
    { iApply "HΦ".
      iSplitL "Hbufs Hbufptrlist".
      { iExists _, _. iFrame. }
      admit.
    }
  }

  iIntros "(Hmap & Hi & Hq)".
  iDestruct "Hi" as (s bufptrlist) "[Hbufs Hbufptrlist]".
  wp_pures.
  wp_load.
  iApply "HΦ".
  iFrame.
  admit.
*)
Transparent struct.t.
Admitted.

Definition vtake' {A} (i n : nat) (H : (i ≤ n)%nat) (v : vec A n) : vec A i.
  destruct (decide (i = n)%nat); subst.
  - exact v.
  - assert (i < n)%nat as Hf by abstract lia.
    replace i with (fin_to_nat (nat_to_fin Hf)) by abstract rewrite fin_to_nat_to_fin //.
    refine (vtake _ v).
Defined.

Definition vdrop' {A} (i n : nat) (H : (i < n)%nat) (v : vec A n) : vec A (n-i).
  replace i with (fin_to_nat (nat_to_fin H)) by abstract rewrite fin_to_nat_to_fin //.
  refine (vdrop _ v).
Defined.

Definition extract_nth (b : Block) (elemsize : nat) (n : nat) : option (vec u8 elemsize).
  destruct (decide (elemsize = 0)%nat); first exact None.
  destruct (decide ((S n) * elemsize <= block_bytes)%nat); last exact None.
  refine (Some _).

  replace elemsize with ((S n * elemsize) - n * elemsize)%nat by abstract lia.
  refine (vdrop' _ _ _ _); first abstract lia.
  refine (vtake' _ _ _ b); abstract lia.
Defined.

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

Lemma extract_nth_skipn_firstn blk sz offcount e:
  extract_nth blk sz offcount = Some e ->
  b2val <$> vec_to_list e =
    skipn (offcount*sz)
          (firstn (offcount*sz + sz) (Block_to_vals blk)).
Proof.
  pose proof (length_Block_to_vals blk) as H; revert H.
  rewrite /extract_nth /Block_to_vals fmap_length; intros.
  rewrite -fmap_take -fmap_drop. f_equal.

  destruct (decide (sz = 0)%nat); try congruence.
  destruct (decide ((S offcount) * sz ≤ block_bytes)%nat); try congruence.
  inversion H0; clear H0; subst.

  rewrite /vtake' /vdrop'.
  destruct (decide (sz + offcount * sz = block_bytes)%nat).
  - rewrite -> firstn_all2 by lia.

    assert (offcount * sz < block_bytes)%nat as Hf by lia.
    replace (@drop u8 (offcount * sz)) with (@drop u8 (fin_to_nat (nat_to_fin Hf))).
    2: { rewrite fin_to_nat_to_fin; auto. }
    rewrite -vec_to_list_drop.

    admit.

  - assert (offcount * sz + sz < block_bytes)%nat as Hf by lia.
    replace (offcount * sz + sz)%nat with (fin_to_nat (nat_to_fin Hf)).
    2: { rewrite fin_to_nat_to_fin; auto. }
    rewrite -vec_to_list_take.

    assert (offcount * sz < (@fin_to_nat block_bytes (nat_to_fin Hf)))%nat as Hf2.
    { rewrite fin_to_nat_to_fin. lia. }
    replace (@drop u8 (offcount * sz)%nat) with (@drop u8 (fin_to_nat (nat_to_fin Hf2))).
    2: { rewrite fin_to_nat_to_fin; auto. }
    rewrite -vec_to_list_drop.

    admit.
Admitted.

Definition is_bufData_at_off {K} (b : Block) (off : u64) (d : bufDataT K) : Prop :=
  valid_off K off ∧
  match d with
  | bufBlock d => b = d
  | bufInode i => extract_nth b inode_bytes ((int.nat off)/(inode_bytes*8)) = Some i
  | bufBit d => ∃ (b0 : u8), extract_nth b 1 ((int.nat off)/8) = Some (Vector.of_list [b0]) ∧
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
  iDestruct (is_slice_small_sz with "Hs") as "%".
  destruct H as [Hoff Hatoff].

  wp_apply (wp_SliceSubslice_small with "[$Hs]").
  { rewrite /valid_addr in H0.
    iPureIntro; intuition.
    { admit. }
    { admit. }
  }

  iIntros (s') "Hs".
  wp_pures.
  wp_apply wp_allocStruct; first by auto.

  iIntros (b) "Hb".
  wp_pures.
  iApply "HΦ".
  iDestruct (struct_fields_split with "Hb") as "(Hb.a & Hb.sz & Hb.data & Hb.dirty & %)".

  iDestruct (buf_mapsto_non_null with "[$]") as %Hnotnull.

(*
  rewrite /valid_off in Hoff.
Opaque PeanoNat.Nat.div.
  destruct bufdata; cbn; cbn in Hatoff.
  - destruct Hatoff; intuition.
    iSplitR.
    { iPureIntro. congruence. }
    iExists _.
    iSplitL; last eauto.
    iExactEq "Hs"; f_equal.

    unfold valid_addr in *.
    unfold addr2flat_z in *.
    unfold block_bytes in *.
    intuition idtac.
    word_cleanup.
    rewrite word.unsigned_sub.
    rewrite word.unsigned_add.
    word_cleanup.
    replace (int.val a.(addrOff) + Z.of_nat 1 - 1) with (int.val a.(addrOff)) by lia.
    rewrite wrap_small.
    2: {
      split.
      - assert (0 ≤ int.val a.(addrOff) `div` 8); try lia.
        apply Z_div_pos; lia.
      - assert (int.val a.(addrOff) `div` 8 ≤ int.val a.(addrOff)); try lia.
        apply Zdiv_le_upper_bound; lia.
    }

    eapply extract_nth_skipn_firstn in H3.
    rewrite /b2val /= in H3.
    rewrite H3.
    f_equal.
    { replace (int.nat a.(addrOff) `div` 8 * 1)%nat with (int.nat a.(addrOff) `div` 8)%nat by lia.
      apply Nat2Z.inj.
      rewrite -> div_Zdiv by lia.
      rewrite -> Z2Nat.id by lia.
      rewrite -> Z2Nat.id by ( eapply Z_div_pos; lia ).
      lia.
    }
    f_equal.
    { admit. }

  - iSplitR.
    { iPureIntro. congruence. }
    iExactEq "Hs"; f_equal.

    unfold valid_addr in *.
    unfold addr2flat_z in *.
    unfold inode_bytes, block_bytes in *.
    intuition idtac.
    word_cleanup.
    rewrite word.unsigned_sub.
    rewrite word.unsigned_add.
    word_cleanup.
    replace (int.val a.(addrOff) + Z.of_nat (Z.to_nat 128 * 8) - 1) with (int.val a.(addrOff) + (128*8-1)) by lia.
    rewrite wrap_small.
    2: {
      split.
      - assert (0 ≤ (int.val a.(addrOff) + (128*8-1)) `div` 8); try lia.
        apply Z_div_pos; lia.
      - assert ((int.val a.(addrOff) + (128*8-1)) `div` 8 ≤ int.val a.(addrOff) + (128*8-1)); try lia.
        apply Zdiv_le_upper_bound; lia.
    }

    eapply extract_nth_skipn_firstn in Hatoff.
    rewrite /inode_to_vals Hatoff.
    f_equal.
    { admit. }
    f_equal.
    { admit. }

  - intuition subst.
    iSplitR.
    { iPureIntro. congruence. }
    iExactEq "Hs".

    assert (a.(addrOff) = 0) as Hoff0.
    { simpl in Hoff.
      rewrite /valid_addr /block_bytes /= in H0.
      destruct H0.
      admit.
    }
    rewrite Hoff0.
    unfold block_bytes in *.
    replace (word.divu 0 8) with (U64 0) by reflexivity.
    replace (word.add 0 (Z.to_nat 4096 * 8)%nat) with (U64 (4096 * 8)) by reflexivity.
    replace (word.sub (4096 * 8) 1) with (U64 32767) by reflexivity.
    replace (word.divu 32767 8) with (U64 4095) by reflexivity.
    replace (word.add 4095 1) with (U64 4096) by reflexivity.
    rewrite firstn_all2.
    2: { rewrite length_Block_to_vals /block_bytes. word. }
    rewrite skipn_O //.
*)
Admitted.

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

    wp_apply (slice.wp_SliceGet with "[$Hblk]").
    { admit. }
    iIntros "[Hblk %]".

    iDestruct "Hbufdata" as (x) "[Hbufdata <-]".
    wp_apply (slice.wp_SliceGet with "[$Hbufdata]"); first done.
    iIntros "[Hbufdata %]".

    wp_call.
    admit.

  - wp_pures.
    wp_loadField.
    wp_pures.
    wp_loadField.
    wp_pures.

    destruct (bool_decide (#(word.modu a.(addrOff) 8 : u64) = #0)) eqn:Hd;
      wp_pures.
    2: {
      (* contradiction with [valid_off] in H2. *)
      admit.
    }

    wp_loadField.
    wp_loadField.
    wp_loadField.
    wp_call.

    (* XXX need WP for SliceCopy, and more specialized WPs for
      SliceSkip and SliceTake in terms of is_slice_small *)
    admit.

  - wp_pures.
    wp_loadField.
    wp_loadField.
    wp_pures.

    destruct (bool_decide (#(word.modu a.(addrOff) 8 : u64) = #0)) eqn:Hd;
      wp_pures.
    2: {
      (* contradiction with [valid_off] in H. *)
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
