From Coq Require Import Program.Equality.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.Helpers Require Import bytes Map.
From Perennial.program_proof Require Import disk_prelude.
From Goose.github_com.mit_pdos.go_journal Require Import buf.
From Perennial.program_proof Require Import util_proof disk_lib.
From Perennial.program_proof Require Export buf.defs.
From Perennial.program_proof Require Import addr.addr_proof wal.abstraction.
From Perennial.Helpers Require Import NamedProps PropRestore.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

(* an object is the data for a sub-block object, a dynamic bundle of a kind and
data of the appropriate size *)
(* NOTE(tej): not necessarily the best name, because it's so general as to be
meaningless *)
(* TODO(tej): it would be nice if both of these were records *)
Notation object := ({K & bufDataT K}).
Notation versioned_object := ({K & (bufDataT K * bufDataT K)%type}).

Section heap.
Context `{!heapGS Σ}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Definition is_buf_data {K} (s : Slice.t) (d : bufDataT K) (a : addr) : iProp Σ :=
  match d with
  | bufBit b => ∃ (b0 : u8), slice.own_slice_small s u8T (DfracOwn 1) (#b0 :: nil) ∗
    ⌜ get_bit b0 (word.modu a.(addrOff) 8) = b ⌝
  | bufInode i => slice.own_slice_small s u8T (DfracOwn 1) (inode_to_vals i)
  | bufBlock b => slice.own_slice_small s u8T (DfracOwn 1) (Block_to_vals b)
  end.

Definition is_buf_without_data (bufptr : loc) (a : addr) (o : buf) (data : Slice.t) : iProp Σ :=
  ∃ (sz : u64),
    "Haddr" ∷ bufptr ↦[Buf :: "Addr"] (addr2val a) ∗
    "Hsz" ∷ bufptr ↦[Buf :: "Sz"] #sz ∗
    "Hdata" ∷ bufptr ↦[Buf :: "Data"] (slice_val data) ∗
    "Hdirty" ∷ bufptr ↦[Buf :: "dirty"] #o.(bufDirty) ∗
    "%" ∷ ⌜ valid_addr a ∧ valid_off o.(bufKind) a.(addrOff) ⌝ ∗
    "->" ∷ ⌜ sz = bufSz o.(bufKind) ⌝ ∗
    "%" ∷ ⌜ #bufptr ≠ #null ⌝.

Definition is_buf (bufptr : loc) (a : addr) (o : buf) : iProp Σ :=
  ∃ (data : Slice.t),
    "Hisbuf_without_data" ∷ is_buf_without_data bufptr a o data ∗
    "Hbufdata" ∷ is_buf_data data o.(bufData) a.

Theorem is_buf_not_null bufptr a o :
  is_buf bufptr a o -∗ ⌜ #bufptr ≠ #null ⌝.
Proof.
  iIntros "Hisbuf".
  iNamed "Hisbuf".
  iNamed "Hisbuf_without_data".
  eauto.
Qed.

Theorem is_buf_without_data_valid_addr bufptr a o s :
  is_buf_without_data bufptr a o s -∗ ⌜valid_addr a⌝.
Proof.
  iNamed 1; intuition auto.
Qed.

Theorem is_buf_valid_addr bufptr a o :
  is_buf bufptr a o -∗ ⌜valid_addr a⌝.
Proof.
  iNamed 1.
  iApply (is_buf_without_data_valid_addr with "[$]").
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
  own_slice_small s u8T (DfracOwn 1) data -∗ is_buf_data s (objData obj) a.
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
  is_buf_data s (objData obj) a ⊣⊢ ∃ data, own_slice_small s u8T (DfracOwn 1) data ∗
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

Theorem wp_buf_loadField_sz bufptr a b stk E :
  {{{
    is_buf bufptr a b
  }}}
    struct.loadF buf.Buf "Sz" #bufptr @ stk; E
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
  iExists _. iFrame. done.
Qed.

Theorem wp_buf_loadField_addr bufptr a b stk E :
  {{{
    is_buf bufptr a b
  }}}
    struct.loadF buf.Buf "Addr" #bufptr @ stk; E
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
  iExists _; iFrame. done.
Qed.

Theorem wp_buf_loadField_dirty bufptr a b stk E :
  {{{
    is_buf bufptr a b
  }}}
    struct.loadF buf.Buf "dirty" #bufptr @ stk ; E
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
  iExists _; iFrame. done.
Qed.

Theorem wp_buf_wd_loadField_sz bufptr a b dataslice stk E :
  {{{
    is_buf_without_data bufptr a b dataslice
  }}}
    struct.loadF buf.Buf "Sz" #bufptr @ stk; E
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

Theorem wp_buf_wd_loadField_addr bufptr a b dataslice stk E :
  {{{
    is_buf_without_data bufptr a b dataslice
  }}}
    struct.loadF buf.Buf "Addr" #bufptr @ stk; E
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

Theorem wp_buf_wd_loadField_dirty bufptr a b dataslice stk E :
  {{{
    is_buf_without_data bufptr a b dataslice
  }}}
    struct.loadF buf.Buf "dirty" #bufptr @ stk; E
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

Theorem wp_buf_loadField_data bufptr a b stk E :
  {{{
    is_buf bufptr a b
  }}}
    struct.loadF buf.Buf "Data" #bufptr @ stk; E
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
  iFrame. done.
Qed.

Theorem wp_buf_storeField_data bufptr a b (vslice: Slice.t) k' (v' : bufDataT k') stk E :
  {{{
    is_buf bufptr a b ∗
    is_buf_data vslice v' a ∗
    ⌜ k' = b.(bufKind) ⌝
  }}}
    struct.storeF buf.Buf "Data" #bufptr (slice_val vslice) @ stk; E
  {{{
    RET #();
    is_buf bufptr a (Build_buf k' v' b.(bufDirty))
  }}}.
Proof using.
  iIntros (Φ) "(Hisbuf & Hisbufdata & %) HΦ".
  iNamed "Hisbuf".
  iClear "Hbufdata".
  iNamed "Hisbuf_without_data".
  wp_storeField.
  iApply "HΦ".
  iExists _; iFrame. intuition subst. done.
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
  | bufBlock d => b = d ∧ uint.Z off = 0
  | bufInode i => extract_nth b inode_bytes ((uint.nat off)/(inode_bytes*8)) = inode_to_vals i
  | bufBit d => ∃ (b0 : u8), extract_nth b 1 ((uint.nat off)/8) = #b0 :: nil ∧
      get_bit b0 (word.modu off 8) = d
  end.

Lemma buf_pointsto_non_null b a:
  b ↦[Buf :: "Addr"] addr2val a -∗ ⌜ b ≠ null ⌝.
Proof.
  iIntros "Hb.a".
  iDestruct (heap_pointsto_non_null with "[Hb.a]") as %Hnotnull.
  { rewrite struct_field_pointsto_eq /struct_field_pointsto_def //= struct_pointsto_eq /struct_pointsto_def.
    iDestruct "Hb.a" as "[[[Hb _] _] _]".
    repeat rewrite loc_add_0. iFrame. }
  eauto.
Qed.

Theorem wp_MkBuf K a data (bufdata : bufDataT K) stk E :
  {{{
    is_buf_data data bufdata a ∗
    ⌜ valid_addr a ∧ valid_off K a.(addrOff) ⌝
  }}}
    MkBuf (addr2val a) #(bufSz K) (slice_val data) @ stk; E
  {{{
    (bufptr : loc), RET #bufptr;
    is_buf bufptr a (Build_buf _ bufdata false)
  }}}.
Proof using.
  iIntros (Φ) "[Hbufdata %] HΦ".
  wp_call.
  wp_apply wp_allocStruct; first val_ty.

  iIntros (b) "Hb".
  wp_pures.
  iApply "HΦ".
  iDestruct (struct_fields_split with "Hb") as "(Hb.a & Hb.sz & Hb.data & Hb.dirty & %)".

  iDestruct (buf_pointsto_non_null with "[$]") as %Hnotnull.

  iExists _. iFrame. eauto with congruence.
Qed.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Theorem wp_MkBufLoad K a blk s (bufdata : bufDataT K) stk E :
  {{{
    slice.own_slice_small s u8T (DfracOwn 1) (Block_to_vals blk) ∗
    ⌜ is_bufData_at_off blk a.(addrOff) bufdata ⌝ ∗
    ⌜ valid_addr a ⌝
  }}}
    MkBufLoad (addr2val a) #(bufSz K) (slice_val s) @ stk; E
  {{{
    (bufptr : loc), RET #bufptr;
    is_buf bufptr a (Build_buf _ bufdata false)
  }}}.
Proof using.
  iIntros (Φ) "(Hs & % & %) HΦ".
  wp_call.

  iDestruct (slice.own_slice_small_sz with "Hs") as "%".
  destruct H as [Hoff Hatoff].

  wp_apply (slice.wp_SliceSubslice_small with "[$Hs]").
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
      replace (uint.Z s.(Slice.sz)) with (length (Block_to_vals blk) : Z).
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
  wp_apply wp_allocStruct; first val_ty.

  iIntros (b) "Hb".
  wp_pures.
  iApply "HΦ". iModIntro.
  iDestruct (struct_fields_split with "Hb") as "(Hb.a & Hb.sz & Hb.data & Hb.dirty & %)".

  iDestruct (buf_pointsto_non_null with "[$]") as %Hnotnull.
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
    replace (uint.Z a.(addrOff) + Z.of_nat 1 - 1) with (uint.Z a.(addrOff)) by lia.

    rewrite -H3 /extract_nth.
    replace (uint.nat a.(addrOff) `div` 8 * 1)%nat with (uint.nat a.(addrOff) `div` 8)%nat by lia.
    replace (S (uint.nat a.(addrOff) `div` 8) * 1)%nat with (S (uint.nat a.(addrOff) `div` 8))%nat by lia.
    iExactEq "Hs". f_equal.
    f_equal.
    { rewrite Z2Nat.inj_div; try word.
      eauto. }
    f_equal.
    { rewrite Z2Nat.inj_add; try word.
      rewrite Z2Nat.inj_div; try word.
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
    replace (uint.Z a.(addrOff) + Z.of_nat (Z.to_nat 128 * 8) - 1) with (uint.Z a.(addrOff) + (128*8-1)) by lia.

    rewrite -Hatoff /extract_nth.
    f_equal.
    { rewrite Z2Nat.inj_div; try word.
      simpl bufSz in *.
      change (Z.to_nat 8) with 8%nat.
      change (Z.to_nat 128) with 128%nat.
      change (128 * 8)%nat with (8 * 128)%nat.
      rewrite -Nat.Div0.div_div; try word.
      assert ((uint.nat (addrOff a) `div` 8) `mod` 128 = 0)%nat as Hx.
      {
        replace (uint.Z (addrOff a)) with (Z.of_nat (uint.nat (addrOff a))) in Hoff by word.
        rewrite -Nat2Z.inj_mod in Hoff; try word.
        assert (uint.nat (addrOff a) `mod` 1024 = 0)%nat as Hy by lia.
        replace (1024)%nat with (8*128)%nat in Hy by reflexivity.
        rewrite Nat.Div0.mod_mul_r in Hy; try word.
      }
      apply Nat.Div0.div_exact in Hx; try word.
    }
    f_equal.
    {
      simpl bufSz in *.
      rewrite Z2Nat.inj_add; try word.
      rewrite Z2Nat.inj_div; try word.
      change (Z.to_nat 1) with 1%nat.
      change (Z.to_nat 8) with 8%nat.
      change (Z.to_nat 128) with 128%nat.
      rewrite Z2Nat.inj_add; try word.
      change (Z.to_nat (128*8-1)) with (128*8-1)%nat.

      replace (128 * 8)%nat with (8 * 128)%nat by reflexivity.
      rewrite -Nat.Div0.div_div; try word.
      assert ((uint.nat (addrOff a) `div` 8) `mod` 128 = 0)%nat as Hx.
      {
        replace (uint.Z (addrOff a)) with (Z.of_nat (uint.nat (addrOff a))) in Hoff by word.
        rewrite -Nat2Z.inj_mod in Hoff; try word.
        assert (uint.nat (addrOff a) `mod` 1024 = 0)%nat as Hy by lia.
        replace (1024)%nat with (8*128)%nat in Hy by reflexivity.
        rewrite Nat.Div0.mod_mul_r in Hy; try word.
      }
      apply Nat.Div0.div_exact in Hx; try word.
      rewrite Nat.mul_comm in Hx.
      replace (S ((uint.nat (addrOff a) `div` 8) `div` 128) * 128)%nat
         with (((uint.nat (addrOff a) `div` 8) `div` 128) * 128 + 128)%nat by lia.
      rewrite -Hx.

      edestruct (Nat.Div0.div_exact (uint.nat (addrOff a)) 8) as [_ Hz].
      rewrite -> Hz at 1.
      2: {
        replace (uint.Z (addrOff a)) with (Z.of_nat (uint.nat (addrOff a))) in Hoff by word.
        rewrite -Nat2Z.inj_mod in Hoff; try word.
        assert (uint.nat (addrOff a) `mod` 1024 = 0)%nat as Hy by lia.
        replace (1024)%nat with (8*128)%nat in Hy by reflexivity.
        rewrite Nat.Div0.mod_mul_r in Hy; try word.
      }

      rewrite Nat.mul_comm. rewrite -> Nat.div_add_l by lia.
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
    change (word.divu 0 8) with (W64 0).
    change (word.add 0 (Z.to_nat 4096 * 8)%nat) with (W64 (4096 * 8)).
    change (word.sub (4096 * 8) 1) with (W64 32767).
    change (word.divu 32767 8) with (W64 4095).
    change (word.add 4095 1) with (W64 4096).
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

(** * [byte → list bool] reasoning *)

Definition get_buf_data_bit (b: Block) (off: u64) : bool :=
  let b_byte := get_byte b (uint.Z off `div` 8) in
  let b_bit  := default false (byte_to_bits b_byte !! Z.to_nat (uint.Z off `mod` 8)) in
  b_bit.

Theorem get_bit_ok b0 (off: u64) :
  (uint.Z off < 8) →
  get_bit b0 off = default false (byte_to_bits b0 !! uint.nat off).
Proof.
  intros Hbound.
  bit_cases off; byte_cases b0; vm_refl.
Qed.

Lemma drop_take_lookup {A} i (l: list A) x :
  l !! i = Some x →
  drop i (take (S i) l) = [x].
Proof.
  intros.
  apply elem_of_list_split_length in H as (l1 & l2 & -> & ->).
  rewrite take_app_ge; [ | lia ].
  rewrite drop_app_ge; [ | lia ].
  replace (length l1 - length l1)%nat with 0%nat by lia.
  replace (S (length l1) - length l1)%nat with 1%nat by lia.
  simpl.
  destruct l2; auto.
Qed.

Lemma extract_nth_bit blk (off: nat) :
  extract_nth blk 1 off =
  if decide (off < block_bytes)%nat then
    [b2val (default inhabitant (vec_to_list blk !! off))]
  else [].
Proof.
  rewrite /extract_nth.
  rewrite !Nat.mul_1_r.
  rewrite /Block_to_vals.
  rewrite -fmap_take -fmap_drop.
  destruct (decide _).
  - destruct (lookup_lt_is_Some_2 blk off) as [b0 Hlookup].
    { len. }
    rewrite Hlookup.
    erewrite drop_take_lookup; eauto.
  - rewrite take_ge; [ | len ].
    rewrite drop_ge; [ | len ].
    auto.
Qed.

Lemma valid_off_bit_trivial off : valid_off KindBit off ↔ True.
Proof.
  rewrite /valid_off /=.
  rewrite Z.mod_1_r //.
Qed.

Theorem is_bufData_bit blk off (d: bufDataT KindBit) :
  is_bufData_at_off blk off d ↔ (uint.nat off `div` 8 < block_bytes)%nat ∧ bufBit (get_buf_data_bit blk off) = d.
Proof.
  rewrite /is_bufData_at_off.
  dependent destruction d.
  rewrite valid_off_bit_trivial.
  split.
  - intros [_ ?].
    destruct H as [byte0 [Hnth_byte Hget_bit]].
    rewrite -> get_bit_ok in Hget_bit by word.
    rewrite extract_nth_bit in Hnth_byte.
    destruct (decide _); [ | congruence ].
    split; [ lia | ].
    inversion Hnth_byte; subst; clear Hnth_byte.
    f_equal.
    rewrite /get_buf_data_bit /get_byte.
    word_cleanup.
    rewrite Z2Nat.inj_div //.
    word.
  - intros [Hbound Hbeq].
    inversion Hbeq; subst; clear Hbeq.
    split; [done|].
    rewrite extract_nth_bit.
    rewrite decide_True //.
    eexists; split; [eauto|].
    rewrite -> get_bit_ok by word.
    rewrite /get_buf_data_bit /get_byte.
    word_cleanup.
    rewrite Z2Nat.inj_div //.
    word.
Qed.

(* TODO(tej): I should have used !!! (lookup_total), which is [default inhabitant
(_ !! _)] ([list_lookup_total_alt] proves that). *)

(* off is a bit offset *)
Definition get_inode (blk: Block) (off: nat) : inode_buf :=
  let start_byte := (off `div` 8)%nat in
  list_to_inode_buf (subslice start_byte (start_byte+inode_bytes) (vec_to_list blk)).

Lemma Nat_div_inode_bits (off:nat) :
  off `mod` 1024 = 0 →
  (off `div` (inode_bytes * 8) * inode_bytes =
   off `div` 8)%nat.
Proof.
  intros.
  word_cleanup.
  apply (inj Z.of_nat).
  repeat rewrite !Nat2Z.inj_div !Nat2Z.inj_mul !Z2Nat.id //; try word.
Qed.

Global Instance Nat_mul_comm : Comm eq Nat.mul.
Proof. intros x1 x2. lia. Qed.

Global Instance Z_mul_comm : Comm eq Z.mul.
Proof. intros x1 x2. lia. Qed.

Global Instance Nat_mul_assoc : Assoc eq Nat.mul.
Proof. intros x1 x2 x3. lia. Qed.

Global Instance Z_mul_assoc : Assoc eq Z.mul.
Proof. intros x1 x2 x3. lia. Qed.

Lemma Nat_div_exact_2 : ∀ a b : nat, (b ≠ 0 → a `mod` b = 0 → a = b * a `div` b)%nat.
Proof.
  intros.
  apply Nat.Div0.div_exact; auto.
Qed.

Lemma Z_mod_1024_to_div_8 (z:Z) :
  z `mod` 1024 = 0 →
  z `div` 8 = 128 * (z `div` 1024).
Proof. lia. Qed.

Hint Rewrite Nat2Z.inj_mul Nat2Z.inj_div : word.

Theorem is_bufData_inode blk off (d: bufDataT KindInode) :
  is_bufData_at_off blk off d ↔
  (uint.nat off `div` 8 < block_bytes)%nat ∧
  valid_off KindInode off ∧
  bufInode (get_inode blk (uint.nat off)) = d.
Proof.
  dependent destruction d; simpl.
  rewrite /is_bufData_at_off.
  rewrite /extract_nth.
  rewrite /Block_to_vals.
  rewrite -fmap_take -fmap_drop.
  rewrite /get_inode.
  split.
  - intros [Hvalid Heq].
    rewrite PeanoNat.Nat.mul_succ_l in Heq.
    rewrite /valid_off /= in Hvalid.
    rewrite -> Nat_div_inode_bits in Heq by word.
    rewrite /subslice.
    rewrite /inode_to_vals in Heq.
    apply (inj (fmap b2val)) in Heq.
    assert (uint.nat off `div` 8 < block_bytes)%nat.
    { apply (f_equal length) in Heq.
      move: Heq; len. }
    split; first done.
    split; first done.
    f_equal.
    rewrite Heq.
    rewrite inode_buf_to_list_to_inode_buf //.
  - intros (Hbound&Hvalid&Hdata).
    inversion Hdata; subst; clear Hdata.
    split; first done.
    rewrite /valid_off /= in Hvalid.
    rewrite /inode_to_vals.
    f_equal.
    rewrite PeanoNat.Nat.mul_succ_l.
    rewrite -> !Nat_div_inode_bits by word.
    rewrite list_to_inode_buf_to_list; last first.
    { rewrite /subslice /inode_bytes; len.
      change (Z.to_nat 128) with 128%nat.
      change (Z.of_nat 1024) with 1024 in Hvalid.
      pose proof (Z_mod_1024_to_div_8 (uint.Z off) Hvalid) as Hdiv8.
      assert (uint.nat off `div` 8 = 128 * uint.nat off `div` 1024)%nat.
      { apply Nat2Z.inj. word. }
      word. }
    auto.
Qed.

Lemma valid_block_off off :
  uint.Z off < block_bytes * 8 →
  valid_off KindBlock off →
  off = W64 0.
Proof.
  intros Hbound.
  rewrite /valid_off => Hvalid_off.
  change (Z.of_nat (bufSz KindBlock)) with 32768 in Hvalid_off.
  change (block_bytes * 8) with 32768 in Hbound.
  apply (inj uint.Z).
  word.
Qed.

Lemma is_bufData_block b off (d: bufDataT KindBlock) :
  is_bufData_at_off b off d ↔ off = W64 0 ∧ bufBlock b = d.
Proof.
  dependent destruction d.
  rewrite /is_bufData_at_off /=.
  rewrite /valid_off.
  change (Z.of_nat $ bufSz KindBlock) with 32768.
  (intuition subst); try congruence; try word.
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
  uint.Z bit < 8 →
  word.and b (word.slu (W8 1) (W8 (uint.Z bit))) =
  if default false (byte_to_bits b !! uint.nat bit) then
    W8 (2^(uint.nat bit))
  else W8 0.
Proof.
  intros Hle.
  apply (inj uint.Z).
  bit_cases bit; byte_cases b; vm_refl.
Qed.

Lemma masks_different (bit:u64) :
  uint.Z bit < 8 →
  W8 (2^uint.nat bit ) ≠ W8 0.
Proof.
  intros Hbound Heq%(f_equal uint.Z).
  change (uint.Z (W8 0)) with 0 in Heq.
  move: Heq.
  bit_cases bit; vm_compute; by inversion 1.
Qed.

Theorem wp_installOneBit (src dst: u8) (bit: u64) stk E :
  uint.Z bit < 8 →
  {{{ True }}}
    installOneBit #src #dst #bit @ stk; E
  {{{ RET #(install_one_bit src dst (uint.nat bit)); True }}}.
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
      destruct (default false (byte_to_bits src !! uint.nat bit)) eqn:?.
      { apply masks_different in Heqb0; auto; contradiction. }
      destruct (default false (byte_to_bits dst !! uint.nat bit)) eqn:?; last contradiction.
      iModIntro.
      iExactEq "HΦ"; do 3 f_equal.
      rewrite /install_one_bit.
      rewrite Heqb1.
      apply (inj byte_to_bits).
      rewrite bits_to_byte_to_bits; [|len].
      bit_cases bit; byte_cases dst; vm_refl.
    + destruct (default false (byte_to_bits src !! uint.nat bit)) eqn:?; last contradiction.
      destruct (default false (byte_to_bits dst !! uint.nat bit)) eqn:?; first contradiction.
      wp_load. wp_store. wp_load.
      iModIntro.
      iExactEq "HΦ"; do 3 f_equal.
      rewrite /install_one_bit.
      rewrite Heqb1.
      apply (inj byte_to_bits).
      rewrite bits_to_byte_to_bits; [|len].
      bit_cases bit; byte_cases dst; vm_refl.
  - wp_load. iModIntro.
    iExactEq "HΦ"; do 3 f_equal.
    rewrite install_one_bit_id //.
    { lia. }
    destruct (default false _), (default false _); auto.
    + apply masks_different in Heqb; eauto; contradiction.
    + apply symmetry, masks_different in Heqb; eauto; contradiction.
Qed.

Lemma list_alter_lookup_insert {A} (l: list A) (i: nat) (f: A → A) x0 :
  l !! i = Some x0 →
  alter f i l = <[i:=f x0]> l.
Proof.
  revert i; induction l as [|x l]; intros i.
  - reflexivity.
  - destruct i; simpl.
    + congruence.
    + intros Halter%IHl.
      rewrite -/(alter f i l) Halter //.
Qed.

Theorem wp_installBit
        (src_s: Slice.t) (src_b: u8) q (* source *)
        (dst_s: Slice.t)  (dst_bs: list u8) (* destination *)
        (dstoff: u64) (* the offset we're modifying, in bits *) stk E :
  (uint.Z dstoff < 8 * Z.of_nat (length dst_bs)) →
  {{{ own_slice_small src_s byteT q [src_b] ∗ own_slice_small dst_s byteT (DfracOwn 1) dst_bs  }}}
    installBit (slice_val src_s) (slice_val dst_s) #dstoff @ stk; E
  {{{ RET #();
      let dst_bs' :=
          alter
            (λ dst, install_one_bit src_b dst (Z.to_nat $ uint.Z dstoff `mod` 8))
            (Z.to_nat $ uint.Z dstoff `div` 8) dst_bs in
      own_slice_small src_s byteT q [src_b] ∗ own_slice_small dst_s byteT (DfracOwn 1) dst_bs' }}}.
Proof.
  iIntros (Hbound Φ) "Hpre HΦ".
  iDestruct "Hpre" as "[Hsrc Hdst]".
  wp_call.
  destruct (lookup_lt_is_Some_2 dst_bs (Z.to_nat (uint.Z dstoff `div` 8)))
    as [dst_b Hlookup]; first word.
  wp_apply (wp_SliceGet (V:=u8) with "[$Hdst]").
  { iPureIntro. word_cleanup. eauto. }
  iIntros "Hdst".
  wp_apply (wp_SliceGet (V:=u8) with "[$Hsrc]").
  { iPureIntro. change (uint.nat 0) with 0%nat. reflexivity. }
  iIntros "Hsrc".
  wp_apply wp_installOneBit; first word.
  wp_apply (wp_SliceSet (V:=u8) with "[$Hdst]").
  { iPureIntro. word_cleanup. eauto. }
  iIntros "Hdst".
  wp_pures. iModIntro. iApply "HΦ".
  iFrame "Hsrc".
  iExactEq "Hdst".
  f_equal.
  word_cleanup.
  erewrite list_alter_lookup_insert; eauto.
Qed.

Lemma list_inserts_app_r' {A} (l1 l2 l3: list A) (i: nat) :
  (length l2 ≤ i)%nat →
  list_inserts i l1 (l2 ++ l3) = l2 ++ list_inserts (i-length l2) l1 l3.
Proof.
  intros.
  replace i with (length l2 + (i - length l2))%nat at 1 by lia.
  rewrite list_inserts_app_r //.
Qed.

Theorem wp_installBytes
        (src_s: Slice.t) (src_bs: list u8) q (* source *)
        (dst_s: Slice.t) (dst_bs: list u8) (* destination *)
        (dstoff: u64) (* the offset we're modifying, in bits *)
        (nbit: u64)   (* the number of bits we're modifying *) stk E :
  uint.Z nbit `div` 8 ≤ Z.of_nat (length src_bs) →
  uint.Z dstoff `div` 8 + uint.Z nbit `div` 8 ≤ Z.of_nat (length dst_bs) →
  {{{ own_slice_small src_s byteT q src_bs ∗
      own_slice_small dst_s byteT (DfracOwn 1) dst_bs
  }}}
    installBytes (slice_val src_s) (slice_val dst_s) #dstoff #nbit @ stk; E
  {{{ RET #(); own_slice_small src_s byteT q src_bs ∗
               let src_bs' := take (Z.to_nat $ uint.Z nbit `div` 8) src_bs in
               let dst_bs' := list_inserts (Z.to_nat $ uint.Z dstoff `div` 8) src_bs' dst_bs in
               own_slice_small dst_s byteT (DfracOwn 1) dst_bs'
  }}}.
Proof.
  intros Hnbound Hdst_has_space.
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as "[Hsrc Hdst]".
  wp_call.
  iDestruct (own_slice_small_sz with "Hsrc") as %Hsrc_sz.
  iDestruct (own_slice_small_wf with "Hsrc") as %Hsrc_wf.
  iDestruct (own_slice_small_sz with "Hdst") as %Hdst_sz.
  iDestruct (own_slice_small_wf with "Hdst") as %Hdst_wf.
  wp_apply wp_SliceTake; first by word.
  wp_pures.
  wp_apply wp_SliceSkip; first by word.
  iDestruct (slice_small_split _ (word.divu dstoff 8) with "Hdst")
    as "[Hdst1 Hdst2]"; first by word.
  iDestruct (slice_small_split _ (word.divu nbit 8) with "Hsrc")
    as "[Hsrc1 Hsrc2]"; first by word.
  wp_apply (wp_SliceCopy (V:=u8) with "[$Hsrc1 $Hdst2]").
  { len. }
  iIntros "[Hsrc1 Hdst2']".
  wp_pures.
  iDestruct (own_slice_combine with "Hdst1 Hdst2'")
    as "Hdst"; first by word.
  iDestruct (own_slice_combine with "Hsrc1 Hsrc2")
    as "Hsrc"; first by word.
  rewrite take_drop.
  iApply "HΦ". iModIntro.
  iFrame "Hsrc".
  iExactEq "Hdst".
  f_equal.
  len.
  rewrite -> Nat.min_l by word.
  rewrite drop_drop.
  rewrite -[l in list_inserts _ _ l](take_drop (uint.nat (word.divu dstoff 8)) dst_bs).
  rewrite -> list_inserts_app_r' by len.
  f_equal.
  match goal with
  | |- context[list_inserts ?n _ _] => replace n with 0%nat by len
  end.
  match goal with
  | |- context[list_inserts _ _ ?l] =>
    rewrite -(take_drop (uint.nat (word.divu nbit 8)) l)
  end.
  rewrite -> list_inserts_0_r by len.
  rewrite drop_drop.
  f_equal.
  f_equal; word.
Qed.

Hint Unfold valid_addr block_bytes : word.

Lemma own_slice_to_block s q bs :
  length bs = block_bytes →
  own_slice_small s byteT q bs ⊣⊢
  is_block s q (list_to_block bs).
Proof.
  iIntros (Hlen).
  rewrite /is_block.
  rewrite list_to_block_to_vals //.
Qed.

(** states that [blk'] is like [blk] but with [buf_b] installed at [off'] *)
Definition is_installed_block (blk: Block) (buf_b: buf) (off': u64) (blk': Block) : Prop :=
  ∀ off (d0: bufDataT buf_b.(bufKind)),
    is_bufData_at_off blk off d0 →
    if decide (off = off')
    then is_bufData_at_off blk' off buf_b.(bufData)
    else is_bufData_at_off blk' off d0.

Lemma is_installed_block_bit (off:u64) (b bufDirty : bool) (blk : Block) :
    uint.Z off < block_bytes * 8 →
    ∀ src_b : u8,
      get_bit src_b (word.modu off 8) = b
      → is_installed_block
          blk
          {| bufKind := KindBit; bufData := bufBit b; bufDirty := bufDirty |}
          off
          (list_to_block
             (alter
                (λ (dst:u8),
                 install_one_bit src_b dst
                                 (Z.to_nat (uint.Z off `mod` 8)))
                (Z.to_nat (uint.Z off `div` 8)) (vec_to_list blk))).
Proof.
  intros Haddroff_bound src_b <-.
  rewrite -> get_bit_ok by word.
  intros off' d ?.
  apply is_bufData_bit in H as [Hoff_bound <-].
  word_cleanup.
  remember (uint.Z off `div` 8) as byteOff.
  remember (uint.Z off `mod` 8) as bitOff.
  destruct (lookup_lt_is_Some_2 (vec_to_list blk) (Z.to_nat byteOff))
    as [byte0 Hlookup_byte]; [ len | ].
  destruct (decide _); [subst off'|].
  + (* modified the desired bit *)
    apply is_bufData_bit; split; [done|].
    f_equal.
    rewrite /get_buf_data_bit.
    rewrite /get_byte.
    word_cleanup.
    rewrite list_to_block_to_list; [|len].
    rewrite -!HeqbyteOff -!HeqbitOff.
    rewrite list_lookup_alter.
    f_equal.
    rewrite Hlookup_byte.
    rewrite install_one_bit_spec; [ | word ].
    rewrite decide_True //.
  + (* other bits are unchanged *)
    apply is_bufData_bit; split; [done|].
    f_equal.
    rewrite /get_buf_data_bit.
    f_equal.
    (* are we looking up the same byte, but a different bit? *)
    destruct (decide (uint.Z off' `div` 8 = byteOff)).
    * rewrite e.
      word_cleanup.
      rewrite /get_byte.
      rewrite -> list_to_block_to_list by len.
      rewrite list_lookup_alter.
      rewrite Hlookup_byte /=.
      rewrite install_one_bit_spec; [ | word ].
      rewrite decide_False //.
      intros Heq.
      contradiction n.
      word.
    * rewrite /get_byte.
      rewrite -> list_to_block_to_list by len.
      rewrite list_lookup_alter_ne //.
      word.
Qed.

Hint Rewrite @inserts_length : len.

Lemma subslice_lookup_ge_iff {A} n m i (l: list A) :
  (m ≤ length l)%nat →
  (m ≤ n+i)%nat ↔
  subslice n m l !! i = None.
Proof.
  intros Hmbound.
  rewrite lookup_ge_None.
  rewrite subslice_length //.
  lia.
Qed.

Lemma subslice_lookup_ge {A} n m i (l: list A) :
  (m ≤ length l)%nat →
  (m ≤ n+i)%nat →
  subslice n m l !! i = None.
Proof.
  intros ??.
  apply subslice_lookup_ge_iff; auto.
Qed.

Lemma subslice_list_inserts_eq {A} (k l: list A) n m :
  (m = n + length k)%nat →
  (n + length k ≤ length l)%nat →
  subslice n m (list_inserts n k l) = k.
Proof.
  intros -> Hinsert_in_bounds.
  apply list_eq; intros i.
  destruct (decide (i < length k)) as [Hbound|?].
  - rewrite -> subslice_lookup by lia.
    rewrite list_lookup_inserts; auto with f_equal lia.
  - rewrite subslice_lookup_ge; auto with lia.
    + rewrite lookup_ge_None_2 //; lia.
    + rewrite inserts_length; lia.
Qed.

Lemma subslice_list_inserts_ne {A} (k l: list A) n m i :
  ( m ≤ length l )%nat →
  ( m ≤ i ∨
    i + length k ≤ n )%nat →
  subslice n m (list_inserts i k l) = subslice n m l.
Proof.
  intros.
  apply list_eq; intros j.
  destruct (decide (n+j < m)) as [Hbound|?].
  - repeat rewrite -> subslice_lookup by lia.
    intuition.
    + rewrite list_lookup_inserts_lt; last by lia. done.
    + rewrite list_lookup_inserts_ge; last by lia. done.
  - repeat rewrite -> subslice_lookup_ge; auto with lia.
    rewrite inserts_length; lia.
Qed.

Lemma Nat_mod_1024_to_div_8 (n:nat) :
  Z.of_nat n `mod` 1024 = 0 →
  (n `div` 8 = 128 * (n `div` 1024))%nat.
Proof.
  intros Hn_mod.
  pose proof (Z_mod_1024_to_div_8 (Z.of_nat n) Hn_mod).
  apply (f_equal Z.to_nat) in H.
  rewrite Z2Nat.inj_div in H; try lia.
  apply (inj Z.of_nat).
  move: H; word.
Qed.

Lemma is_installed_block_inode (a : addr) (i : inode_buf) (bufDirty : bool) (blk : Block) :
    valid_addr a ∧ valid_off KindInode (addrOff a) →
    is_installed_block
      blk
      {| bufKind := KindInode; bufData := bufInode i; bufDirty := bufDirty |}
      (addrOff a)
      (list_to_block
         (list_inserts (Z.to_nat (uint.Z (addrOff a) `div` 8))
                       (take (Z.to_nat (uint.Z 1024%nat `div` 8)) i) blk)).
Proof.
  intros H.
  destruct H as [[? ?] ?].
  generalize dependent (addrOff a); intros off.
  intros Hoff_bound Hvalid_off.
  intros off' d Hdata_at_off; simpl in *.
  apply is_bufData_inode in Hdata_at_off as (Hoff'_bound&Hoff'_valid&<-).
  change (Z.to_nat (uint.Z 1024%nat `div` 8)) with inode_bytes.
  rewrite -> take_ge by len.
  destruct (decide _); [subst off'|]; apply is_bufData_inode.
  - split; first done.
    split; first done.
    f_equal.
    rewrite /get_inode.
    rewrite /valid_off /= in Hvalid_off.
    rewrite -> list_to_block_to_list by len.
    rewrite Z2Nat.inj_div; try word.
    change (Z.to_nat 8) with 8%nat.
    rewrite subslice_list_inserts_eq; len.
    { rewrite inode_buf_to_list_to_inode_buf //. }
    cut (uint.Z off `div` 8 + 128 ≤ 4096).
    { intros.
      rewrite /inode_bytes /block_bytes.
      move: H; word_cleanup.
      rewrite -> Z2Nat.inj_le by word.
      rewrite -> Z2Nat.inj_add by word.
      rewrite -> Z2Nat.inj_div by word.
      auto. }
    word.
  - split; first done.
    split; first done.
    f_equal.
    rewrite /get_inode.
    f_equal.
    rewrite -> list_to_block_to_list by len.
    rewrite /valid_off /= in Hvalid_off, Hoff'_valid.
    assert (uint.nat off' `div` 8 ≠ uint.nat off `div` 8).
    { intros Heq.
      apply n.
      word. }
    replace (Z.to_nat (uint.Z off `div` 8)) with (uint.nat off `div` 8)%nat; last first.
    { rewrite Z2Nat.inj_div //; word. }
    rewrite -> !Nat_mod_1024_to_div_8 by lia.
    rewrite -> !Z_mod_1024_to_div_8 in H by lia.
    rewrite /inode_bytes.
    rewrite subslice_list_inserts_ne; eauto;
      rewrite vec_to_list_length.
    + revert Hoff'_bound. rewrite /block_bytes.
      change 1024%nat with (8 * 128)%nat.
      rewrite -Nat.Div0.div_div.
      generalize (uint.nat off' `div` 8)%nat; intros x Hx.
      assert (x `div` 128 < 32)%nat; try lia.
      eapply Nat.div_lt_upper_bound; lia.
    + destruct (decide (uint.nat off' < uint.nat off)); [ left | right ].
      * assert ((uint.nat off' `div` 1024)%nat < (uint.nat off `div` 1024)%nat); last by lia.
        rewrite !Nat2Z.inj_div; lia.
      * assert ((uint.nat off' `div` 1024)%nat > (uint.nat off `div` 1024)%nat); last by lia.
        rewrite !Nat2Z.inj_div; lia.
Qed.

Lemma is_installed_block_block (b : Block) (bufDirty : bool) (blk : Block) :
    is_installed_block
      blk
      {| bufKind := KindBlock; bufData := bufBlock b; bufDirty := bufDirty |} 0
      (list_to_block (list_inserts 0 (take block_bytes b) blk)).
Proof.
  rewrite -> take_ge by len.
  rewrite -[l in list_inserts _ _ l]app_nil_r.
  rewrite -> list_inserts_0_r by len.
  rewrite app_nil_r.

  rewrite block_to_list_to_block.
  intros off d Hdata%is_bufData_block.
  destruct Hdata as [-> <-].
  simpl.
  destruct (decide _); [ subst | congruence ].
  apply is_bufData_block; auto.
Qed.

Lemma bufSz_block_eq :
  Z.of_nat (bufSz KindBlock) = 32768.
Proof. reflexivity. Qed.

Lemma valid_block_off_addr a :
  valid_addr a →
  valid_off KindBlock (addrOff a) →
  addrOff a = W64 0.
Proof.
  destruct 1 as [? _].
  apply valid_block_off; auto.
Qed.

Theorem wp_Buf__Install bufptr a b blk_s blk stk E :
  {{{
    is_buf bufptr a b ∗
    is_block blk_s (DfracOwn 1) blk
  }}}
    Buf__Install #bufptr (slice_val blk_s) @ stk; E
  {{{
    (blk': Block), RET #();
    is_buf bufptr a b ∗
    is_block blk_s (DfracOwn 1) blk' ∗
    ⌜ is_installed_block blk b a.(addrOff) blk' ⌝
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
    iDestruct "Hbufdata" as (src_b) "[Hsrc %Hsrc_data]".
    wp_apply (wp_installBit with "[$Hsrc $Hblk]").
    { rewrite vec_to_list_length.
      word. }
    iIntros "[Hsrc Hdst]".
    wp_apply wp_DPrintf.
    wp_pures. iApply "HΦ". iModIntro.
    iDestruct (own_slice_to_block with "Hdst") as "$".
    { len. }
    iSplitL.
    { iExists _; iFrame "∗%"; done. }
    iPureIntro.
    apply is_installed_block_bit; auto.
    word.

  - wp_pures.
    wp_loadField. wp_pures.
    wp_loadField.
    wp_pures.
    rewrite bool_decide_eq_true_2; last first.
    { f_equal.
      f_equal.
      apply (inj uint.Z).
      destruct H as [? ?].
      word_cleanup.
      rewrite /valid_off /= in H1.
      change (Z.of_nat 1024) with (8*128) in H1.
      rewrite Z.rem_mul_r // in H1.
      word. }
    wp_if.
    wp_loadField. wp_loadField. wp_loadField.
    simpl.
    wp_apply (wp_installBytes with "[$Hbufdata $Hblk]").
    { len. }
    { len.
      change (uint.Z 1024%nat `div` 8) with 128.
      destruct H as [Hvalid H].
      destruct Hvalid.
      rewrite Z_mod_1024_to_div_8 //.
      word. }
    iIntros "[Hbufdata Hblk]".
    wp_pures. wp_apply wp_DPrintf.
    iDestruct (own_slice_to_block with "Hblk") as "Hblk".
    { len. }
    wp_pures. iApply "HΦ". iModIntro.
    iFrame "Hblk".
    iSplitL.
    { iExists _; iFrame. done. }
    iPureIntro.
    apply is_installed_block_inode.
    auto.

  - destruct H as [H Hvalidoff].
    rewrite (valid_block_off_addr a) //.
    rewrite bufSz_block_eq.
    wp_pures.
    wp_loadField. wp_loadField.
    wp_pures.
    rewrite bool_decide_eq_true_2; last first.
    { f_equal.
      f_equal.
      apply (inj uint.Z).
      rewrite /valid_off in Hvalidoff.
      rewrite bufSz_block_eq in Hvalidoff.
      word. }
    wp_if.
    wp_loadField. wp_loadField. wp_loadField.
    rewrite (valid_block_off_addr a) //.
    wp_apply (wp_installBytes with "[$Hbufdata $Hblk]").
    { len. }
    { len. }
    iIntros "[Hsrc Hblk]".
    iDestruct (own_slice_to_block with "Hblk") as "Hblk".
    { len. }
    wp_pures. wp_apply wp_DPrintf.
    wp_pures. iModIntro. iApply "HΦ".
    iFrame "Hblk".
    iSplitL.
    { iExists _; iFrame. auto. }
    iPureIntro.
    change (Z.to_nat (uint.Z 0 `div` 8)) with 0%nat.
    change (Z.to_nat (uint.Z 32768 `div` 8)) with block_bytes.
    apply is_installed_block_block.
Qed.

Theorem wp_Buf__SetDirty bufptr a b stk E :
  {{{
    is_buf bufptr a b
  }}}
    Buf__SetDirty #bufptr @ stk; E
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
  iExists _; iFrame. done.
Qed.

End heap.
