From RecordUpdate Require Import RecordSet.

From Goose.github_com.mit_pdos.perennial_examples Require Import dir.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.examples Require Import alloc_proof inode_proof.

Module dir.
  Record t :=
    mk { inodes: list inode.t; }.
  Global Instance _eta : Settable t := settable! mk <inodes>.
  Global Instance _witness : Inhabited t := populate!.
End dir.

Section goose.
Context `{!heapG Σ}.
Context `{!allocG Σ}.

Record dir_names :=
  { alloc_name: @alloc_names Σ; }.

Context (P: dir.t → iProp Σ).
Implicit Types (σ: dir.t) (γ: dir_names).

Definition is_dir (l: loc) γ: iProp Σ :=
  ∃ (d_l alloc_l: loc) inodes_s,
    readonly (l ↦[Dir.S :: "d"] #d_l) ∗
    readonly (l ↦[Dir.S :: "allocator"] #alloc_l) ∗
    readonly (l ↦[Dir.S :: "inodes"] (slice_val inodes_s))
.

End goose.
