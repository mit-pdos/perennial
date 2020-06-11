From Perennial.goose_lang Require Import crash_modality.
From Perennial.algebra Require Import deletable_heap.

From Goose.github_com.mit_pdos.perennial_examples Require Import single_inode.
From Perennial.goose_lang.lib Require Import lock.crash_lock.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof.examples Require Import
     range_set alloc_crash_proof inode_proof.
From Perennial.program_proof Require Import proof_prelude.

Module s_inode.
  Definition t := list Block.
End s_inode.

Definition listBlockO := discreteO (list Block).

Section goose.
  Context `{!heapG Σ}.
  Context `{!lockG Σ}.
  Context `{!crashG Σ}.
  Context `{!allocG Σ}.
  Context `{!stagedG Σ}.
  Context `{!inG Σ (ghostR listBlockO)}.

  Implicit Types (l:loc) (σ: s_inode.t) (γ: gname).

  Let N := nroot.@"single_inode".
  Let allocN := nroot.@"allocator".
  Context (P: s_inode.t → iProp Σ).

  Definition is_single_inode l (sz: Z) k' k'' : iProp Σ :=
    ∃ (inode_ref alloc_ref: loc) γinode γalloc γused γblocks,
      l ↦[SingleInode.S :: "i"] #inode_ref ∗
      l ↦[SingleInode.S :: "alloc"] #alloc_ref ∗
      is_inode inode_ref k' γinode
        (λ s, own γblocks (◯ Excl' (s.(inode.blocks): listBlockO)) ∗
              own γused (●{1/2} Excl' s.(inode.addrs)))
        (U64 0) ∗
      is_allocator
        (λ s, own γused (●{1/2} Excl' (alloc.used s)))
        (λ a, ∃ b, int.val a d↦ b)
        allocN alloc_ref (rangeSet 1 (sz-1)) γalloc k'' ∗
      inv N (∃ (blocks: list Block) (used:gset u64),
                own γblocks (● Excl' (blocks: listBlockO)) ∗
                P blocks ∗
                own γused (◯ Excl' used))
  .

End goose.
