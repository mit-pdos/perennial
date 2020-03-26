From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.Helpers Require Import GenHeap.
From Perennial.goose_lang.lib Require Import struct.

From Goose.github_com.mit_pdos.goose_nfsd Require Import buf.
From Perennial.program_proof.addr Require Import specs.

Section heap.
Context `{!heapG Σ}.
Context `{!lockG Σ}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Definition inode_bytes := Z.to_nat 128.
Definition inode_buf := vec u8 inode_bytes.
Definition inode_to_vals {ext: ext_op} (i:inode_buf) : list val :=
  fmap b2val (vec_to_list i).

Inductive bufDataKind :=
| KindBit
| KindInode
| KindBlock
.

Global Instance bufDataKind_eq_dec : EqDecision bufDataKind.
Proof.
  solve_decision.
Defined.

Inductive bufDataT : forall {K : bufDataKind}, Type :=
| bufBit (b : bool) : @bufDataT KindBit
| bufInode (i : inode_buf) : @bufDataT KindInode
| bufBlock (b : Block) : @bufDataT KindBlock
.

Definition bufSz K : nat :=
  match K with
  | KindBit => 1
  | KindInode => inode_bytes*8
  | KindBlock => block_bytes*8
  end.

Record buf := {
  bufKind : bufDataKind;
  bufData : @bufDataT bufKind;
  bufDirty : bool;
}.

Definition get_bit (b0 : u8) (off : u64) : bool.
Admitted.

Definition is_buf (bufptr : loc) (a : addr) (o : buf) : iProp Σ :=
  ∃ (data : Slice.t) (sz : u64),
    bufptr ↦[Buf.S :: "Addr"] (addr2val a) ∗
    bufptr ↦[Buf.S :: "Sz"] #sz ∗
    bufptr ↦[Buf.S :: "Data"] (slice_val data) ∗
    bufptr ↦[Buf.S :: "dirty"] #o.(bufDirty) ∗
    ⌜ valid_addr a ⌝ ∗
    match o.(bufData) with
    | bufBit b => ∃ (b0 : u8), is_slice data u8T 1%Qp (#b0 :: nil) ∗
      ⌜ get_bit b0 (word.modu a.(addrOff) 8) ⌝ ∗
      ⌜ sz = 1 ⌝
    | bufInode i => is_slice data u8T 1%Qp (inode_to_vals i) ∗
      ⌜ sz = (inode_bytes * 8)%nat ⌝
    | bufBlock b => is_slice data u8T 1%Qp (Block_to_vals b) ∗
      ⌜ sz = (block_bytes * 8)%nat ⌝
    end.

Definition is_bufmap (bufmap : loc) (bm : gmap addr buf) : iProp Σ :=
  ∃ (mptr : loc) (m : gmap u64 val) (am : gmap addr val),
    bufmap ↦[BufMap.S :: "addrs"] #mptr ∗
    is_map mptr (m, #null) ∗
    ⌜ flatid_addr_map m am ⌝ ∗
    [∗ map] a ↦ bufptr; buf ∈ am; bm,
      ∃ (bufloc : loc),
        ⌜ bufptr = #bufloc ⌝ ∗
        is_buf bufloc a buf.

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
Proof.
  iIntros (Φ) "[Hbufmap Hbuf] HΦ".
  iDestruct "Hbufmap" as (mptr mm am) "(Hmptr & Hmap & % & Ham)".
  iDestruct "Hbuf" as (bufdata bufsz) "(Hbuf.addr & Hbuf.sz & Hbuf.data & Hbuf.dirty & % & Hdata)".

  wp_call.
  wp_loadField.
  wp_apply wp_Addr__Flatid; eauto. iIntros (?) "->".
  wp_loadField.
  wp_apply (wp_MapInsert with "Hmap"); iIntros "Hmap".
  iApply "HΦ".
  iExists _, _, _. iFrame.
  iSplitR.
  { iPureIntro. apply flatid_addr_insert; eauto. }

  (* Two cases: either we are inserting a new addr or overwriting *)
  destruct (am !! a) eqn:Heq.
  - iDestruct (big_sepM2_lookup_1_some with "Ham") as (v2) "%"; eauto.
    iDestruct (big_sepM2_insert_acc with "Ham") as "[Hcur Hacc]"; eauto.
    iApply "Hacc".
    iExists _.
    iSplitR; eauto.
    iExists _, _. iFrame. done.

  - iDestruct (big_sepM2_lookup_1_none with "Ham") as "%"; eauto.
    iApply big_sepM2_insert; eauto.
    iFrame "Ham".
    iExists _.
    iSplitR; eauto.
    iExists _, _. iFrame. done.
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
Proof.
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
Proof.
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
    iDestruct "Hbuf" as (bufloc) "[-> Hbuf]".
    rewrite H2.
    iApply "HΦ".
    iFrame.

    iIntros (b') "Hbuf".
    iExists _, _, _.
    iFrame.
    iSplitR; first eauto.
    replace (am) with (<[a:=#bufloc]> am) at 1 by ( apply insert_id; eauto ).
    iApply "Ham".
    iExists _. iFrame. done.

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
    (s : Slice.t) bufptrlist dirtylist, RET (slice_val s);
    is_slice s (refT (struct.t Buf.S)) 1%Qp bufptrlist ∗
    ⌜ dirtylist ≡ₚ filter (λ x, (snd x).(bufDirty) = true) (map_to_list m) ⌝ ∗
    [∗ list] _ ↦ bufptrval; addrbuf ∈ bufptrlist; dirtylist,
      ∃ (bufptr : loc),
        ⌜ bufptrval = #bufptr ⌝ ∗
        is_buf bufptr (fst addrbuf) (snd addrbuf)
  }}}.
Proof.
Admitted.

Definition extract_nth (b : Block) (elemsize : nat) (n : nat) : option (vec u8 elemsize).
  destruct (decide ((S n) * elemsize <= block_bytes)).
  - refine (Some _).

    assert (elemsize ≤ block_bytes - n * elemsize)%nat by abstract lia.
    refine (Vector.take _ H _).

    unfold Block in b.
    assert (block_bytes = n * elemsize + (block_bytes - n * elemsize))%nat by abstract lia.
    rewrite H0 in b.
    refine (snd (Vector.splitat _ b)).
  - exact None.
Defined.

Definition is_bufData_at_off {K} (b : Block) (off : u64) (d : @bufDataT K) : Prop :=
  match d with
  | bufBlock d => off = 0 ∧ b = d
  | bufInode i => extract_nth b inode_bytes (int.nat off) = Some i
  | bufBit d => ∃ (b0 : u8), extract_nth b 1 ((int.nat off)/8) = Some (Vector.of_list [b0]) ∧
      get_bit b0 (word.modu off 8) = d
  end.

End heap.
