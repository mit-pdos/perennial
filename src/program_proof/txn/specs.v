From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.

Record addr := {
  addr_block : u64;
  addr_offset : u64;
}.

Global Instance addr_eq_dec : EqDecision addr.
Proof.
  intros x y.
  destruct x; destruct y.
  destruct (decide (addr_block0 = addr_block1)).
  - destruct (decide (addr_offset0 = addr_offset1)).
    + left; congruence.
    + right; congruence.
  - right; congruence.
Defined.

Global Instance addr_finite : Countable addr.
Admitted.

Definition inode_bytes := Z.to_nat 128.
Definition inode_buf := vec u8 inode_bytes.

Inductive updatable_buf (T : Type) :=
| Stable : forall (v : T), updatable_buf T
| Unstable.

Arguments Unstable {T}.
Arguments Stable {T} v.

Section heap.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!gen_heapPreG u64 (gen_heapG u64 (updatable_buf Block) Σ) Σ}.
Context `{!gen_heapPreG u64 (gen_heapG u64 (updatable_buf inode_buf) Σ) Σ}.
Context `{!gen_heapPreG u64 (gen_heapG u64 (updatable_buf bool) Σ) Σ}.
Context `{!gen_heapPreG u64 Block Σ}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Definition lockN : namespace := nroot .@ "txn".

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

Definition is_txn (lt : loc) (walHeap : gen_heapG u64 Block Σ)
    (gBits   : gen_heapG u64 (gen_heapG u64 (updatable_buf bool) Σ) Σ)
    (gInodes : gen_heapG u64 (gen_heapG u64 (updatable_buf inode_buf) Σ) Σ)
    (gBlocks : gen_heapG u64 (gen_heapG u64 (updatable_buf Block) Σ) Σ)
    : iProp Σ :=
  (
    True
  )%I.

End heap.
