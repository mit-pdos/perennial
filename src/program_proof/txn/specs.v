From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(*
  TODO: get txn to actually Goose
  TODO: allow representing multiple logical disks with Txn,
    one per logical disk from Wal.
  TODO: how to deal with crashes?  the 3 ghost maps exposed
    by Txn must remain latest, so what represents the old state?
*)

From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.

From Goose.github_com.mit_pdos.goose_nfsd Require Import buf.

Record addr := {
  addrBlock : u64;
  addrOff : u64;
}.

Definition inode_bytes := Z.to_nat 128.
Definition inode_buf := vec u8 inode_bytes.
Definition inode_to_vals {ext: ext_op} (i:inode_buf) : list val :=
  fmap b2val (vec_to_list i).

Definition inode_bits : u64 := inode_bytes*8.
Definition block_bits : u64 := block_bytes*8.

Inductive updatable_buf (T : Type) :=
| Stable : forall (v : T), updatable_buf T
| Unstable.

Arguments Unstable {T}.
Arguments Stable {T} v.

Inductive txnObject :=
| txnBit (b : bool)
| txnInode (i : inode_buf)
| txnBlock (b : Block)
.

Global Instance addr_eq_dec : EqDecision addr.
Admitted.

Global Instance addr_finite : Countable addr.
Admitted.

Section heap.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!gen_heapPreG u64 Block Σ}.
Context `{!gen_heapPreG u64 (updatable_buf Block) Σ}.
Context `{!gen_heapPreG u64 (updatable_buf inode_buf) Σ}.
Context `{!gen_heapPreG u64 (updatable_buf bool) Σ}.
Context `{!gen_heapPreG unit
          (gmap u64 (gmap u64 (updatable_buf bool)) *
           gmap u64 (gmap u64 (updatable_buf inode_buf)) *
           gmap u64 (gmap u64 (updatable_buf Block)))
         Σ}.
Context `{!gen_heapPreG addr txnObject Σ}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Definition lockN : namespace := nroot .@ "txnlock".
Definition invN : namespace := nroot .@ "txninv".

Definition txn_inodes_in_block (b : Block) (gm : gmap u64 (updatable_buf inode_buf)) : iProp Σ :=
  (
    [∗ map] off ↦ maybe_inode ∈ gm,
      match maybe_inode with
      | Unstable => True
      | Stable v =>
        (* extract bytes off*inode_size..(off+1)*inode_size from b;
            they must be equal to v *)
        True
      end
  )%I.

Definition txn_bits_in_block (b : Block) (gm : gmap u64 (updatable_buf bool)) : iProp Σ :=
  (
    [∗ map] off ↦ maybe_bit ∈ gm,
      match maybe_bit with
      | Unstable => True
      | Stable v =>
        (* extract bit off from block; it must be equal to v *)
        True
      end
  )%I.

Definition txn_blocks_in_block (b : Block) (gm : gmap u64 (updatable_buf Block)) : iProp Σ :=
  (
    [∗ map] off ↦ maybe_block ∈ gm,
      match maybe_block with
      | Unstable => True
      | Stable v =>
        ⌜ off = (0 : u64) ⌝ ∗
        ⌜ v = b ⌝
      end
  )%I.

Definition is_txn_always (walHeap : gen_heapG u64 Block Σ)
    (gBits   : gmap u64 (gen_heapG u64 (updatable_buf bool) Σ))
    (gInodes : gmap u64 (gen_heapG u64 (updatable_buf inode_buf) Σ))
    (gBlocks : gmap u64 (gen_heapG u64 (updatable_buf Block) Σ))
    γMaps
    : iProp Σ :=
  (
    ∃ (mBits : gmap u64 (gmap u64 (updatable_buf bool)))
      (mInodes : gmap u64 (gmap u64 (updatable_buf inode_buf)))
      (mBlocks : gmap u64 (gmap u64 (updatable_buf Block))),
      ( [∗ map] blkno ↦ gm;gh ∈ mBits;gBits, gen_heap_ctx (hG := gh) gm ) ∗
      ( [∗ map] blkno ↦ gm;gh ∈ mInodes;gInodes, gen_heap_ctx (hG := gh) gm ) ∗
      ( [∗ map] blkno ↦ gm;gh ∈ mBlocks;gBlocks, gen_heap_ctx (hG := gh) gm ) ∗
      mapsto (hG := γMaps) tt (1/2) (mBits, mInodes, mBlocks) ∗
      ( [∗ map] blkno ↦ bitmap ∈ mBits,
          ∃ b,
            mapsto (hG := walHeap) blkno 1 b ∗
            txn_bits_in_block b bitmap ) ∗
      ( [∗ map] blkno ↦ inodemap ∈ mInodes,
          ∃ b,
            mapsto (hG := walHeap) blkno 1 b ∗
            txn_inodes_in_block b inodemap ) ∗
      ( [∗ map] blkno ↦ blockmap ∈ mBlocks,
          ∃ b,
            mapsto (hG := walHeap) blkno 1 b ∗
            txn_blocks_in_block b blockmap )
  )%I.

Definition is_txn_locked γMaps : iProp Σ :=
  (
    ∃ (mBits : gmap u64 (gmap u64 (updatable_buf bool)))
      (mInodes : gmap u64 (gmap u64 (updatable_buf inode_buf)))
      (mBlocks : gmap u64 (gmap u64 (updatable_buf Block))),
      mapsto (hG := γMaps) tt (1/2) (mBits, mInodes, mBlocks) ∗
      ( [∗ map] blkno ↦ bitmap ∈ mBits,
          [∗ map] off ↦ ub_bit ∈ bitmap, ⌜ub_bit ≠ Unstable⌝ ) ∗
      ( [∗ map] blkno ↦ inodemap ∈ mBits,
          [∗ map] off ↦ ub_inode ∈ inodemap, ⌜ub_inode ≠ Unstable⌝ ) ∗
      ( [∗ map] blkno ↦ blockmap ∈ mBits,
          [∗ map] off ↦ ub_block ∈ blockmap, ⌜ub_block ≠ Unstable⌝ )
  )%I.

Definition is_txn (l : loc)
    (gBits   : gmap u64 (gen_heapG u64 (updatable_buf bool) Σ))
    (gInodes : gmap u64 (gen_heapG u64 (updatable_buf inode_buf) Σ))
    (gBlocks : gmap u64 (gen_heapG u64 (updatable_buf Block) Σ))
    : iProp Σ :=
  (
    ∃ γMaps γLock (walHeap : gen_heapG u64 Block Σ),
      (* Say something about the struct Txn stored at l,
         get the [*wal.Walog] from l, and connect that
         to wal_Heap. *)
      inv invN (is_txn_always walHeap gBits gInodes gBlocks γMaps) ∗
      is_lock lockN γLock #l (is_txn_locked γMaps)
  )%I.

Axiom txn_Load : val.

Theorem wp_txn_Load_bit l gBits gInodes gBlocks (blk off : u64)
    (hG : gen_heapG u64 (updatable_buf bool) Σ) v :
  {{{ is_txn l gBits gInodes gBlocks ∗
      ⌜gBits !! blk = Some hG⌝ ∗
      mapsto (hG := hG) off 1 (Stable v)
  }}}
    txn_Load #l (#blk, #off, #1)
  {{{ (buf : Slice.t) b, RET (slice_val buf);
      is_slice buf u8T [b] ∗
      ⌜b = #0 <-> v = false⌝
  }}}.
Proof.
Admitted.

Theorem wp_txn_Load_inode l gBits gInodes gBlocks (blk off : u64)
    (hG : gen_heapG u64 (updatable_buf inode_buf) Σ) v :
  {{{ is_txn l gBits gInodes gBlocks ∗
      ⌜gInodes !! blk = Some hG⌝ ∗
      mapsto (hG := hG) off 1 (Stable v)
  }}}
    txn_Load #l (#blk, #off, #(inode_bytes*8))
  {{{ (buf : Slice.t) vals, RET (slice_val buf);
      is_slice buf u8T vals ∗
      ⌜vals = inode_to_vals v⌝ }}}.
Proof.
Admitted.

Theorem wp_txn_Load_block l gBits gInodes gBlocks (blk off : u64)
    (hG : gen_heapG u64 (updatable_buf Block) Σ) v :
  {{{ is_txn l gBits gInodes gBlocks ∗
      ⌜gBlocks !! blk = Some hG⌝ ∗
      mapsto (hG := hG) off 1 (Stable v)
  }}}
    txn_Load #l (#blk, #off, #(block_bytes*8))
  {{{ (buf : Slice.t) vals, RET (slice_val buf);
      is_slice buf u8T vals ∗
      ⌜vals = Block_to_vals v⌝ }}}.
Proof.
Admitted.

Axiom txn_CommitWait : val.

Definition commit_pre
    (gBits   : gmap u64 (gen_heapG u64 (updatable_buf bool) Σ))
    (gInodes : gmap u64 (gen_heapG u64 (updatable_buf inode_buf) Σ))
    (gBlocks : gmap u64 (gen_heapG u64 (updatable_buf Block) Σ))
    (b : val) : iProp Σ :=
  (
    ∃ (bloc : loc) (blkno off sz : u64) data data_vals,
      ⌜b = #bloc⌝ ∗
      bloc ↦[struct.t buf.Buf.S] (#blkno, #off, #sz, slice_val data) ∗
      is_slice data u8T data_vals ∗
      (
        ( ∃ (hG : gen_heapG u64 (updatable_buf bool) Σ) v,
          ⌜sz=1⌝ ∗
          ⌜gBits !! blkno = Some hG⌝ ∗
          mapsto (hG := hG) off 1 (Stable v) ) ∨
        ( ∃ (hG : gen_heapG u64 (updatable_buf inode_buf) Σ) v,
          ⌜sz=inode_bits⌝ ∗
          ⌜gInodes !! blkno = Some hG⌝ ∗
          mapsto (hG := hG) off 1 (Stable v) ) ∨
        ( ∃ (hG : gen_heapG u64 (updatable_buf Block) Σ) v,
          ⌜sz=block_bits⌝ ∗
          ⌜gBlocks !! blkno = Some hG⌝ ∗
          mapsto (hG := hG) off 1 (Stable v) )
      )
  )%I.

Definition commit_post
    (gBits   : gmap u64 (gen_heapG u64 (updatable_buf bool) Σ))
    (gInodes : gmap u64 (gen_heapG u64 (updatable_buf inode_buf) Σ))
    (gBlocks : gmap u64 (gen_heapG u64 (updatable_buf Block) Σ))
    (b : val) : iProp Σ :=
  (
    ∃ (bloc : loc) (blkno off sz : u64) data data_vals,
      ⌜b = #bloc⌝ ∗
      bloc ↦[struct.t buf.Buf.S] (#blkno, #off, #sz, slice_val data) ∗
      is_slice data u8T data_vals ∗
      (
        ( ∃ (hG : gen_heapG u64 (updatable_buf bool) Σ) v,
          ⌜sz=1⌝ ∗
          ⌜gBits !! blkno = Some hG⌝ ∗
          mapsto (hG := hG) off 1 (Stable v) ∗
          ⌜ v = false ∧ data_vals = (#0 :: nil) ∨
            v = true ∧ ∃ x, data_vals = [x] ∧ x ≠ #0 ⌝
          ) ∨
        ( ∃ (hG : gen_heapG u64 (updatable_buf inode_buf) Σ) v,
          ⌜sz=inode_bits⌝ ∗
          ⌜gInodes !! blkno = Some hG⌝ ∗
          mapsto (hG := hG) off 1 (Stable v) ∗
          ⌜ inode_to_vals v = data_vals ⌝ ) ∨
        ( ∃ (hG : gen_heapG u64 (updatable_buf Block) Σ) v,
          ⌜sz=block_bits⌝ ∗
          ⌜gBlocks !! blkno = Some hG⌝ ∗
          mapsto (hG := hG) off 1 (Stable v) ∗
          ⌜ Block_to_vals v = data_vals ⌝ )
      )
  )%I.

Theorem wp_txn_CommitWait l gBits gInodes gBlocks bufs buflist :
  {{{ is_txn l gBits gInodes gBlocks ∗
      is_slice bufs (refT (struct.t buf.Buf.S)) buflist ∗
      ( [∗ list] _ ↦ buf ∈ buflist, commit_pre gBits gInodes gBlocks buf )
  }}}
    txn_CommitWait #l (slice_val bufs)
  {{{ RET #();
      is_slice bufs (refT (struct.t buf.Buf.S)) buflist ∗
      ( [∗ list] _ ↦ buf ∈ buflist, commit_post gBits gInodes gBlocks buf ) }}}.
Proof.
Admitted.

Definition unify_heaps_inner
    (gBits    : gmap u64 (gen_heapG u64 (updatable_buf bool) Σ))
    (gInodes  : gmap u64 (gen_heapG u64 (updatable_buf inode_buf) Σ))
    (gBlocks  : gmap u64 (gen_heapG u64 (updatable_buf Block) Σ))
    (gUnified : gmap addr txnObject)
    : iProp Σ :=
  (
    [∗ map] addr ↦ txnObj ∈ gUnified,
      match txnObj with
      | txnBit v =>
        ∃ hG,
          ⌜gBits !! addr.(addrBlock) = Some hG⌝ ∧
          mapsto (hG := hG) addr.(addrOff) 1 (Stable v)
      | txnInode v =>
        ∃ hG,
          ⌜gInodes !! addr.(addrBlock) = Some hG⌝ ∧
          mapsto (hG := hG) addr.(addrOff) 1 (Stable v)
      | txnBlock v =>
        ∃ hG,
          ⌜gBlocks !! addr.(addrBlock) = Some hG⌝ ∧
          mapsto (hG := hG) addr.(addrOff) 1 (Stable v)
      end
  )%I.

Definition unify_heaps
    (gBits    : gmap u64 (gen_heapG u64 (updatable_buf bool) Σ))
    (gInodes  : gmap u64 (gen_heapG u64 (updatable_buf inode_buf) Σ))
    (gBlocks  : gmap u64 (gen_heapG u64 (updatable_buf Block) Σ))
    (γUnified : gen_heapG addr txnObject Σ)
    : iProp Σ :=
  (
    ∃ gUnified,
      gen_heap_ctx (hG := γUnified) gUnified ∗
      unify_heaps_inner gBits gInodes gBlocks gUnified
  )%I.

End heap.
