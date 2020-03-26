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

Inductive bufDataT :=
| bufBit (b : bool)
| bufInode (i : inode_buf)
| bufBlock (b : Block)
.

Record buf := {
  bufData : bufDataT;
  bufDirty : bool;
}.

Definition get_bit (b0 : u8) (off : u64) : bool.
Admitted.

Definition is_bufObject (bufptr : loc) (a : addr) (o : buf) : iProp Σ :=
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
  ∃ (mptr : loc) (m : gmap u64 val) (am : gmap addr val) def,
    bufmap ↦[BufMap.S :: "addrs"] #mptr ∗
    is_map mptr (m, def) ∗
    ⌜ flatid_addr_map m am ⌝ ∗
    [∗ map] a ↦ bufptr; buf ∈ am; bm,
      ∃ (bufloc : loc),
        ⌜ bufptr = #bufloc ⌝ ∗
        is_bufObject bufloc a buf.

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
  iExists _, _, _, _.

  iFrame.
  iSplitR; first (iPureIntro; apply flatid_addr_empty).
  iApply big_sepM2_empty.
  done.
Qed.

End heap.
