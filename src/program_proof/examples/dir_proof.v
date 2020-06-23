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

(** Per-inode statements and lemmas about them. *)
Local Definition inode_blocks γblocks (idx: nat) (blocks: list Block): iProp Σ :=
  own γblocks (◯ {[ idx := Excl blocks ]}: blocksR).
Local Definition inode_allblocks γblocks (allblocks: gmap nat (list Block)): iProp Σ :=
  own γblocks (● (Excl <$> allblocks): blocksR).
Local Definition inode_used γused (idx: nat) (used: gset u64): iProp Σ :=
  own γused (◯ {[ idx := Excl used ]}: allocsR).
Local Definition inode_allused γused (allused: gmap nat (gset u64)): iProp Σ :=
  own γused (● (Excl <$> allused): allocsR).

Lemma inode_blocks_lookup γblocks (idx: nat) (blocks: list Block) (allblocks: gmap nat (list Block)):
  inode_blocks γblocks idx blocks -∗
  inode_allblocks γblocks allblocks -∗
  ⌜allblocks !! idx = Some blocks⌝.
Proof.
  iIntros "Hblocks Hallblocks".
  iDestruct (own_valid_2 with "Hallblocks Hblocks") as
      %[Hincl _]%auth_both_valid.
  iPureIntro.
  move: Hincl. rewrite singleton_included_l=> -[oblocks []].
  rewrite lookup_fmap fmap_Some_equiv=> -[blocks' [-> ->]].
  rewrite Excl_included leibniz_equiv_iff => -> //.
Qed.

Lemma inode_used_lookup γused (idx: nat) (used: gset u64) (allused: gmap nat (gset u64)):
  inode_used γused idx used -∗
  inode_allused γused allused -∗
  ⌜allused !! idx = Some used⌝.
Proof.
  iIntros "Hused Hallused".
  iDestruct (own_valid_2 with "Hallused Hused") as
      %[Hincl _]%auth_both_valid.
  iPureIntro.
  move: Hincl. rewrite singleton_included_l=> -[oused []].
  rewrite lookup_fmap fmap_Some_equiv=> -[used' [-> ->]].
  rewrite Excl_included leibniz_equiv_iff => -> //.
Qed.

(** Protocol invariant for inode library *)
Local Definition Pinode γblocks γused (idx: nat) (s: inode.t): iProp Σ :=
  "Hownblocks" ∷ inode_blocks γblocks idx s.(inode.blocks) ∗
  "Hused1" ∷ inode_used γused idx s.(inode.addrs).

(** Protocol invariant for alloc library *)
Local Definition Palloc γused (s: alloc.t): iProp Σ :=
  ∃ allocs: gmap nat (gset u64), (* per-inode used blocks *)
    "%Hused_global" ∷ ⌜alloc.used s = ⋃ (snd <$> map_to_list allocs)⌝ ∗
    "Hused2" ∷ inode_allused γused allocs.

(** Our own invariant (added to this is [P dir]) *)
Definition dir_inv γblocks (dir: dir.t): iProp Σ :=
  "%Hdom" ∷ ⌜ dom (gset nat) dir.(dir.inodes) = list_to_set (seq 0 5) ⌝ ∗
  "Hγblocks" ∷ inode_allblocks γblocks dir.(dir.inodes).

(** In-memory state of the directory (persistent) *)
Definition is_dir (l: loc) γ: iProp Σ :=
  ∃ (d_l alloc_l: loc) inodes_s,
    readonly (l ↦[Dir.S :: "d"] #d_l) ∗
    readonly (l ↦[Dir.S :: "allocator"] #alloc_l) ∗
    readonly (l ↦[Dir.S :: "inodes"] (slice_val inodes_s))
.

End goose.
