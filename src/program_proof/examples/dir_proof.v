From RecordUpdate Require Import RecordSet.

From Goose.github_com.mit_pdos.perennial_examples Require Import dir.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.examples Require Import alloc_crash_proof inode_proof.

Module dir.
  Record t :=
    mk { inodes: gmap nat (list Block); }.
  Global Instance _eta : Settable t := settable! mk <inodes>.
  Global Instance _witness : Inhabited t := populate!.
End dir.

Canonical Structure listLO A := leibnizO (list A).

Local Definition blocksR := authR $ gmapUR nat (exclR $ listLO Block).
Local Definition allocsR := authR $ gmapUR nat (exclR $ gset64O).

Section goose.
Context `{!heapG Σ}.
Context `{!allocG Σ}.
Context `{!inG Σ blocksR}.
Context `{!inG Σ allocsR}.

Record dir_names :=
  { alloc_name: @alloc_names Σ; }.

Context (P: dir.t → iProp Σ).
Implicit Types (σ: dir.t) (γ: dir_names).

(** Protocol invariant for inode library *)
Local Definition Pinode γblocks γused (s: inode.t) (idx: nat): iProp Σ :=
  "Hownblocks" ∷ own γblocks (◯ {[ idx := Excl s.(inode.blocks) ]}: blocksR) ∗
  "Hused1" ∷ own γused (◯ {[ idx := Excl s.(inode.addrs) ]} : allocsR).

(** Protocol invariant for alloc library *)
Local Definition Palloc γused (s: alloc.t): iProp Σ :=
  ∃ allocs: gmap nat (gset u64), (* per-inode used blocks *)
    "%Hused_global" ∷ ⌜alloc.used s = ⋃ (snd <$> map_to_list allocs)⌝ ∗
    "Hused2" ∷ own γused (● (Excl <$> allocs) : allocsR).

(** Our own invariant (added to this is [P dir]) *)
Definition dir_inv γblocks (dir: dir.t): iProp Σ :=
  "%Hdom" ∷ ⌜ dom (gset nat) dir.(dir.inodes) = list_to_set (seq 0 5) ⌝ ∗
  "Hγblocks" ∷ own γblocks (● (Excl <$> dir.(dir.inodes)) : blocksR).

(** In-memory state of the directory (persistent) *)
Definition is_dir (l: loc) γ: iProp Σ :=
  ∃ (d_l alloc_l: loc) inodes_s,
    readonly (l ↦[Dir.S :: "d"] #d_l) ∗
    readonly (l ↦[Dir.S :: "allocator"] #alloc_l) ∗
    readonly (l ↦[Dir.S :: "inodes"] (slice_val inodes_s))
.

End goose.
