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

Section goose.
  Context `{!heapG Σ}.
  Context `{!lockG Σ}.
  Context `{!crashG Σ}.
  Context `{!allocG Σ}.
  Context `{!stagedG Σ}.

  Implicit Types (l:loc) (σ: s_inode.t) (γ: gname).

  Let N := nroot.@"single_inode".
  Let allocN := nroot.@"allocator".
  Context (P: s_inode.t → iProp Σ).

  (* TODO: is γused the right strategy for connecting the used blocks? *)
  (* (more technically, is it ok that γused is existentially quantified? I only
  imagine using it for one step, so it doesn't matter if it changes. *)

  Definition is_single_inode l (sz: Z) k' k'' : iProp Σ :=
    ∃ (inode_ref alloc_ref: loc) γinode γalloc γused,
      l ↦[SingleInode.S :: "i"] #inode_ref ∗
      l ↦[SingleInode.S :: "alloc"] #alloc_ref ∗
      is_inode inode_ref k' γinode
        (λ s, P s.(inode.blocks) ∗
              own γused (●{1/2} Excl' s.(inode.addrs))) (U64 0) ∗
      is_allocator
        (λ s, own γused (●{1/2} Excl' (alloc.used s)))
        (λ a, ∃ b, int.val a d↦ b)
        allocN alloc_ref (rangeSet 1 (sz-1)) γalloc k'' ∗
      inv N (∃ (used:gset u64), own γused (◯ Excl' used))
  .

End goose.
