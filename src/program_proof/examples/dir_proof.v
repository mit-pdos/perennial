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

  (* The client picks our namespace *)
  Context (N: namespace).
  (* We use parts of it ourselves and assign the rest to sub-libraries. *)
  Let dirN := N.@"dir".
  Let allocN := N.@"allocator".
  Let inodeN := N.@"inode".

  Definition num_inodes: nat := 5.

  Context (P: dir.t → iProp Σ).
  Implicit Types (dir σ: dir.t).

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
  Local Definition Pinode γblocks γused (ino: nat) (s: inode.t): iProp Σ :=
    "Hownblocks" ∷ inode_blocks γblocks ino s.(inode.blocks) ∗
    "Hused1" ∷ inode_used γused ino s.(inode.addrs).

  (** Protocol invariant for alloc library *)
  Local Definition Palloc γused (s: alloc.t): iProp Σ :=
    ∃ allocs: gmap nat (gset u64), (* per-inode used blocks *)
      "%Hused_global" ∷ ⌜alloc.used s = ⋃ (snd <$> map_to_list allocs)⌝ ∗
      "Hused2" ∷ inode_allused γused allocs.

  (** Our own invariant (added to this is [P dir]) *)
  Definition dir_inv γblocks (dir: dir.t): iProp Σ :=
    "%Hdom" ∷ ⌜ ∀ idx, idx < num_inodes → is_Some (dir.(dir.inodes) !! idx) ⌝ ∗
    "Hγblocks" ∷ inode_allblocks γblocks dir.(dir.inodes).

  (** In-memory state of the directory (persistent) *)
  Definition dir_state (l alloc_l: loc) (inode_refs: list loc) : iProp Σ :=
    ∃ (d_l: loc) (inodes_s: Slice.t),
      "#d" ∷ readonly (l ↦[Dir.S :: "d"] #d_l) ∗
      "#allocator" ∷ readonly (l ↦[Dir.S :: "allocator"] #alloc_l) ∗
      "#inodes" ∷ readonly (l ↦[Dir.S :: "inodes"] (slice_val inodes_s)) ∗
      "#inodes_s" ∷ readonly (is_slice_small inodes_s (struct.ptrT inode.Inode.S) 1 (inode_refs))
  .

  (** State of unallocated blocks *)
  Local Definition allocΨ (a: u64): iProp Σ := ∃ b, int.val a d↦ b.

  Definition is_dir l (sz: Z) k' : iProp Σ :=
    ∃ (alloc_ref: loc) (inode_refs: list loc) γalloc γused γblocks,
      "%Hlen" ∷ ⌜length inode_refs = num_inodes⌝ ∗
      "Hro_state" ∷ dir_state l alloc_ref inode_refs ∗
      "#Hinodes" ∷ ([∗ list] i ↦ inode_ref ∈ inode_refs,
        is_inode inodeN inode_ref (LVL k') (Pinode γblocks γused i) (U64 (Z.of_nat i))) ∗
      "#Halloc" ∷ is_allocator (Palloc γused)
        allocΨ allocN alloc_ref (rangeSet num_inodes (sz-num_inodes)) γalloc k' ∗
      "#Hinv" ∷ inv dirN (∃ σ, dir_inv γblocks σ ∗ P σ)
  .

  Definition dir_cinv sz σ (post_crash: bool) : iProp Σ :=
    ∃ γblocks γused,
    "Hinodes" ∷ (∃ s_inodes,
                    [∗ list] i↦s_inode ∈ s_inodes,
                   "Hinode_cinv" ∷ inode_cinv (U64 (Z.of_nat i)) s_inode ∗
                    "HPinode" ∷ Pinode γblocks γused i s_inode) ∗
    "Halloc" ∷ alloc_crash_cond (Palloc γused) allocΨ (rangeSet num_inodes (sz-num_inodes)) post_crash ∗
    "Hs_inode" ∷ dir_inv γblocks σ
  .

  Lemma dir_cinv_post_crash sz σ :
    dir_cinv sz σ true -∗ dir_cinv sz σ false.
  Proof.
    iNamed 1.
    iExists _, _; iFrame.
    iApply alloc_crash_cond_from_post_crash; auto.
  Qed.

  Definition pre_dir l (sz: Z) dir : iProp Σ :=
    ∃ alloc_ref inode_refs γblocks γused,
      "%Hlen" ∷ ⌜length inode_refs = num_inodes⌝ ∗
      "Hro_state" ∷ dir_state l alloc_ref inode_refs ∗
      "Hd_inv" ∷ dir_inv γblocks dir ∗
      "Hinodes" ∷ (∃ s_inodes,
                      [∗ list] i↦inode_ref;s_inode ∈ inode_refs;s_inodes,
                     pre_inode inode_ref (U64 (Z.of_nat i)) s_inode ∗
                  Pinode γblocks γused i s_inode) ∗
      "Halloc" ∷ (∃ s_alloc,
                     "Halloc_mem" ∷ is_allocator_mem_pre alloc_ref s_alloc ∗
                     "%Halloc_dom" ∷ ⌜alloc.domain s_alloc = rangeSet num_inodes (sz-num_inodes)⌝ ∗
                     "Hunused" ∷ ([∗ set] k ∈ alloc.unused s_alloc, allocΨ k) ∗
                     "HPalloc" ∷ Palloc γused s_alloc)
  .

  Lemma wpc_openInodes {k E2} (d: loc) γused γblocks s_inodes :
    {{{ ([∗ list] i↦s_inode ∈ s_inodes,
          "Hinode_cinv" ∷ inode_cinv (U64 (Z.of_nat i)) s_inode ∗
          "HPinode" ∷ Pinode γblocks γused i s_inode)
      }}}
      openInodes #d @ NotStuck; k; ⊤; E2
    {{{ inode_s inode_refs, RET (slice_val inode_s);
        is_slice_small inode_s (struct.ptrT inode.Inode.S) 1 inode_refs ∗
        [∗ list] i↦inode_ref;s_inode ∈ inode_refs;s_inodes,
            pre_inode inode_ref (U64 (Z.of_nat i)) s_inode
    }}}
    {{{ ([∗ list] i↦s_inode ∈ s_inodes,
          "Hinode_cinv" ∷ inode_cinv (U64 (Z.of_nat i)) s_inode ∗
          "HPinode" ∷ Pinode γblocks γused i s_inode) }}}.
  Proof.
  Abort.

  Theorem wpc_OpenDir {k E2} (d: loc) (sz: u64) σ0 :
    {{{ dir_cinv (int.val sz) σ0 true }}}
      OpenDir #d #sz @ NotStuck; LVL k; ⊤; E2
    {{{ l, RET #l; pre_dir l (int.val sz) σ0 }}}
    {{{ dir_cinv (int.val sz) σ0 false }}}.
  Proof.
    iIntros (Φ Φc) "Hcinv HΦ".
    wpc_call.
    { iApply dir_cinv_post_crash; auto. }
    iNamed "Hcinv".
    iCache with "HΦ Hinodes Halloc Hs_inode".
    { crash_case.
      iApply dir_cinv_post_crash.
      iExists _, _; iFrame. }
    iDeexHyp "Hinodes".
  Abort.

  Theorem wpc_Read {k E2} (Q: option Block → iProp Σ) l sz k' (idx: u64) (i: u64) :
    (S k < k')%nat →
    int.nat idx < num_inodes →
    {{{ "#Hdir" ∷ is_dir l sz k' ∗
        "Hfupd" ∷ (∀ σ blocks mb,
                      ⌜σ.(dir.inodes) !! int.nat idx = Some blocks ∧
                       mb = blocks !! int.nat i⌝ -∗
                      ▷ P σ ={⊤ ∖ ↑N}=∗ ▷ P σ ∗ Q mb)
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
    edestruct (lookup_lt_is_Some_2 inode_refs) as [inode_ref Hinode_ref].
    { rewrite Hlen. done. }
    iDestruct (big_sepL_lookup _ _ _ _ Hinode_ref with "Hinodes") as "Hinode {Hinodes}".
    wpc_frame_seq.
    wp_loadField.
    iMod (readonly_load with "inodes_s") as (qinodes) "{inodes_s} inodes_s"; first done.
    wp_apply (wp_SliceGet _ _ _ _ _ inode_refs with "[$inodes_s //]").
    iIntros "inodes_s Hrest". iNamed "Hrest".
    wpc_pures.
    (* Now we get to the actual read operation. *)
    iApply wpc_Inode__Read; first done.
    iFrame "Hinode". iSplit.
    { iLeft in "HΦ". by iApply "HΦ". }
    iIntros "!>" (σI mb) "[%Hmb >HPI]". iNamed "HPI".
    iInv dirN as (σD) "[>Hdir HPD]".
    (* We need to learn that this inode exists in σD. *)
    rewrite /dir_inv. iNamed "Hdir".
    destruct (Hdom _ Hidx) as [σI' HσI'].
    iDestruct (inode_blocks_lookup with "Hownblocks Hγblocks") as %Hblock.
    simplify_eq.
    iMod fupd_intro_mask' as "HcloseM"; (* adjust mask *)
        last iMod ("Hfupd" with "[] HPD") as "[HPD HQ]".
    { solve_ndisj. }
    { iPureIntro. eauto. }
    iMod "HcloseM" as "_". iModIntro. iSplitL "Hγblocks HPD".
    { (* re-establish dir_inv *) eauto 10 with iFrame. }
    iModIntro. iSplitL "Hownblocks Hused1".
    { (* re-establish inode invariant *) rewrite /Pinode. eauto 10 with iFrame. }
    iSplit.
    { iLeft in "HΦ". by iApply "HΦ". }
    iIntros (s) "Hpost". iRight in "HΦ". iApply "HΦ".
    iFrame. done.
  Qed.

  (* these two fupds are easy to prove universally because the change they make
  doesn't affect the free set, which is all that Palloc talks about *)

  Lemma reserve_fupd_Palloc E γused :
    ⊢ reserve_fupd E (Palloc γused).
  Proof.
    iIntros (s s' ma Hma) "HPalloc".
    destruct ma; intuition subst; auto.
    iModIntro.
    rewrite /Palloc /named.
    rewrite alloc_used_reserve //.
  Qed.

  Lemma free_fupd_Palloc E γused :
    ⊢ ∀ a, free_fupd E (Palloc γused) a.
  Proof.
    iIntros (a s s') "HPalloc".
    iModIntro.
    rewrite /Palloc /named.
    rewrite alloc_free_reserved //.
  Qed.

End goose.
