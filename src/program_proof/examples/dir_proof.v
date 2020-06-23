From RecordUpdate Require Import RecordSet.

From Goose.github_com.mit_pdos.perennial_examples Require Import dir.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.examples Require Import
     alloc_addrset alloc_crash_proof inode_proof.
From Perennial.goose_lang.lib Require Import typed_slice. (* shadows things, should be last *)

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
  Context `{!lockG Σ}.
  Context `{!allocG Σ}.
  Context `{!crashG Σ}.
  Context `{!stagedG Σ}.
  Context `{!inG Σ blocksR}.
  Context `{!inG Σ allocsR}.

  Let N := nroot.@"dir".
  Let localN := N.@"local".
  Let allocN := N.@"allocator".
  Let inodeN := N.@"inode".

  Definition num_inodes: nat := 5.

  Context (P: dir.t → iProp Σ).
  Implicit Types (σ: dir.t).

  (** Per-inode statements and lemmas about them. *)
  Local Definition inode_blocks γblocks (idx: nat) (blocks: list Block): iProp Σ :=
    own γblocks (◯ {[ idx := Excl blocks ]}: blocksR).
  Local Definition inode_allblocks γblocks (allblocks: gmap nat (list Block)): iProp Σ :=
    own γblocks (● (Excl <$> allblocks): blocksR).
  Local Definition inode_used γused (idx: nat) (used: gset u64): iProp Σ :=
    own γused (◯ {[ idx := Excl used ]}: allocsR).
  Local Definition inode_allused γused (allused: gmap nat (gset u64)): iProp Σ :=
    own γused (● (Excl <$> allused): allocsR).

  (* Twice the same proofs... really this should be abstracted, ideally into Iris. *)
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

  Lemma inode_blocks_update γblocks E (idx: nat) (blocks1 blocks2: list Block) (allblocks: gmap nat (list Block)):
    inode_blocks γblocks idx blocks1 -∗
    inode_allblocks γblocks allblocks ={E}=∗
    inode_blocks γblocks idx blocks2 ∗ inode_allblocks γblocks (<[ idx := blocks2 ]> allblocks).
  Proof.
    iIntros "Hblocks Hallblocks".
    iDestruct (inode_blocks_lookup with "Hblocks Hallblocks") as %Hallblocks.
    iMod (own_update_2 with "Hallblocks Hblocks") as "[Hallblocks $]".
    { apply: auth_update. apply: singleton_local_update.
      { by rewrite lookup_fmap Hallblocks. }
      apply: exclusive_local_update. done. }
    rewrite -fmap_insert. done.
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

  Lemma inode_used_update γused E (idx: nat) (used1 used2: gset u64) (allused: gmap nat (gset u64)):
    inode_used γused idx used1 -∗
    inode_allused γused allused ={E}=∗
    inode_used γused idx used2 ∗ inode_allused γused (<[ idx := used2 ]> allused).
  Proof.
    iIntros "Hused Hallused".
    iDestruct (inode_used_lookup with "Hused Hallused") as %Hallused.
    iMod (own_update_2 with "Hallused Hused") as "[Hallused $]".
    { apply: auth_update. apply: singleton_local_update.
      { by rewrite lookup_fmap Hallused. }
      apply: exclusive_local_update. done. }
    rewrite -fmap_insert. done.
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
    "%Hdom" ∷ ⌜ dom (gset nat) dir.(dir.inodes) = list_to_set (seq 0 num_inodes) ⌝ ∗
    "Hγblocks" ∷ inode_allblocks γblocks dir.(dir.inodes).

  (** In-memory state of the directory (persistent) *)
  Definition dir_state (l alloc_l: loc) (inode_refs: list loc) : iProp Σ :=
    ∃ (d_l: loc) (inodes_s: Slice.t),
      readonly (l ↦[Dir.S :: "d"] #d_l) ∗
      readonly (l ↦[Dir.S :: "allocator"] #alloc_l) ∗
      readonly (l ↦[Dir.S :: "inodes"] (slice_val inodes_s)) ∗
      readonly (is_slice_small inodes_s (struct.ptrT inode.Inode.S) 1 (inode_refs))
  .

  (** State of unallocated blocks *)
  Local Definition allocΨ (a: u64): iProp Σ := ∃ b, int.val a d↦ b.

  Definition is_dir l (sz: Z) k' : iProp Σ :=
    ∃ (alloc_ref: loc) (inode_refs: list loc) γinode γalloc γused γblocks,
      "Hro_state" ∷ dir_state l alloc_ref inode_refs ∗
      "#Hinode" ∷ [∗ list] i ↦ inode_ref ∈ inode_refs,
        is_inode inode_ref (LVL k') γinode (Pinode γblocks γused i) (U64 0) ∗
      "#Halloc" ∷ is_allocator (Palloc γused)
        allocΨ allocN alloc_ref (rangeSet 1 (sz-1)) γalloc k' ∗
      "#Hinv" ∷ inv localN (∃ σ, dir_inv γblocks σ ∗ P σ)
  .

  Theorem wpc_Read {k E2} (Q: option Block → iProp Σ) l sz k' (idx: u64) (i: u64) :
    (S k < k')%nat →
    int.nat idx < num_inodes →
    {{{ "#Hdir" ∷ is_dir l sz k' ∗
        "Hfupd" ∷ (∀ σ blocks mb,
                      ⌜σ.(dir.inodes) !! int.nat idx = Some blocks ∧
                       mb = blocks !! int.nat i⌝ -∗
                      ▷ P σ ={⊤ ∖ ↑inodeN ∖ ↑N}=∗ ▷ P σ ∗ Q mb)
    }}}
      Dir__Read #l #idx #i @ NotStuck; LVL (S k); ⊤;E2
    {{{ (s:Slice.t) mb, RET (slice_val s);
        match mb with
        | None => ⌜s = Slice.nil⌝
        | Some b => is_block s 1 b
        end ∗ Q mb }}}
    {{{ True }}}.
  Proof.
    iIntros (? Hidx Φ Φc) "Hpre HΦ"; iNamed "Hpre".
    wpc_call.
    { crash_case; auto. }
    iCache with "HΦ Hfupd".
    { crash_case; auto. }
    iNamed "Hdir". iNamed "Hro_state".
  Abort.

End goose.
