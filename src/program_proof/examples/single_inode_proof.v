From RecordUpdate Require Import RecordSet.

From Perennial.algebra Require Import deletable_heap.
From Perennial.goose_lang Require Import crash_modality.

From Goose.github_com.mit_pdos.perennial_examples Require Import single_inode.
From Perennial.goose_lang.lib Require Import lock.crash_lock.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.examples Require Import
     alloc_addrset alloc_crash_proof inode_proof.
From Perennial.goose_lang.lib Require Export typed_slice into_val.

Remove Hints fractional.into_sep_fractional : typeclass_instances.

Module s_inode.
  Record t :=
    mk { blocks: list Block; }.
  Global Instance _eta : Settable t := settable! mk <blocks>.
  Global Instance _witness : Inhabited t := populate!.
End s_inode.

Section goose.
  Context `{!heapG Σ}.
  Context `{!allocG Σ}.
  Context `{!stagedG Σ}.
  Context `{!ghost_varG Σ (list Block)}.

  Implicit Types (l:loc) (σ: s_inode.t) (γ: gname).

  (* The client picks our namespace *)
  Context (N: namespace).
  (* We use parts of it ourselves and assign the rest to sub-libraries. *)
  Let s_inodeN := N.@"single_inode".
  Let allocN := N.@"allocator".
  Let inodeN := N.@"inode".

  (* The client picks our state interpretation *)
  Context (P: s_inode.t → iProp Σ).

  (** Protocol invariant for inode library *)
  Local Definition Pinode γblocks γused (s: inode.t): iProp Σ :=
    "Hownblocks" ∷ ghost_var γblocks (1/2) s.(inode.blocks) ∗
    "Hused1" ∷ ghost_var γused (1/2) (s.(inode.addrs)).

  (** Protocol invariant for alloc library *)
  Local Definition Palloc γused (s: alloc.t): iProp Σ :=
    "Hused2" ∷ ghost_var γused (1/2) (alloc.used s).

  (** Our own invariant (added to this is [P blocks]) *)
  Definition s_inode_inv γblocks (blocks: s_inode.t): iProp Σ :=
    "Hγblocks" ∷ ghost_var γblocks (1/2) (blocks.(s_inode.blocks)).

  (** In-memory state of the inode (persistent) *)
  Definition s_inode_state l (inode_ref alloc_ref: loc) : iProp Σ :=
    "#i" ∷ readonly (l ↦[SingleInode.S :: "i"] #inode_ref) ∗
    "#alloc" ∷ readonly (l ↦[SingleInode.S :: "alloc"] #alloc_ref).

  (** State of unallocated blocks *)
  Local Definition allocΨ (a: u64): iProp Σ := ∃ b, int.val a d↦ b.

  Definition pre_s_inode l (sz: Z) σ : iProp Σ :=
    ∃ inode_ref alloc_ref γused γblocks,
    "#Hstate" ∷ s_inode_state l inode_ref alloc_ref ∗
    "Hs_inv" ∷ s_inode_inv γblocks σ ∗
    "Hinode" ∷ (∃ s_inode, "Hpre_inode" ∷ pre_inode inode_ref (U64 0) s_inode ∗
                "HPinode" ∷ Pinode γblocks γused s_inode) ∗
    "Halloc" ∷ (∃ s_alloc, "Halloc_mem" ∷ is_allocator_mem_pre alloc_ref s_alloc ∗
                "%Halloc_dom" ∷ ⌜alloc.domain s_alloc = rangeSet 1 (sz-1)⌝ ∗
                "Hunused" ∷ ([∗ set] k ∈ alloc.unused s_alloc, allocΨ k) ∗
                "HPalloc" ∷ Palloc γused s_alloc).

  Definition is_single_inode l (sz: Z) k' : iProp Σ :=
    ∃ (inode_ref alloc_ref: loc) γalloc γused γblocks,
      "Hro_state" ∷ s_inode_state l inode_ref alloc_ref ∗
      "#Hinode" ∷ is_inode inodeN inode_ref (S k') (Pinode γblocks γused) (U64 0) ∗
      "#Halloc" ∷ is_allocator (Palloc γused)
        allocΨ allocN alloc_ref (rangeSet 1 (sz-1)) γalloc k' ∗
      "#Hinv" ∷ ncinv s_inodeN (∃ σ, s_inode_inv γblocks σ ∗ P σ)
  .

  Definition s_inode_cinv sz σ (post_crash: bool) : iProp Σ :=
    ∃ γblocks γused,
    "Hinode" ∷ (∃ s_inode, "Hinode_cinv" ∷ inode_cinv (U64 0) s_inode ∗
                           "HPinode" ∷ Pinode γblocks γused s_inode) ∗
    "Halloc" ∷ alloc_crash_cond (Palloc γused) allocΨ (rangeSet 1 (sz-1)) post_crash ∗
    "Hs_inode" ∷ s_inode_inv γblocks σ
  .
  Local Hint Extern 1 (environments.envs_entails _ (s_inode_cinv _ _ _)) => unfold s_inode_cinv : core.

  Theorem s_inode_cinv_post_crash sz σ :
    s_inode_cinv sz σ true -∗ s_inode_cinv sz σ false.
  Proof.
    iNamed 1.
    iExists _, _; iFrame.
    iApply (alloc_crash_cond_from_post_crash with "[$]").
  Qed.

  Instance s_inode_inv_Timeless :
    Timeless (s_inode_inv γblocks blocks).
  Proof. apply _. Qed.

  Theorem init_single_inode {E} (sz: Z) :
    (1 ≤ sz < 2^64)%Z →
    ([∗ list] i ∈ seqZ 0 sz, i d↦ block0) ={E}=∗
    let σ0 := s_inode.mk [] in
    s_inode_cinv sz σ0 true.
  Proof.
    iIntros (Hbound) "Hd".
    replace sz with (1 + (sz - 1))%Z at 1 by lia.
    rewrite -> seqZ_app by lia.
    change (0 + 1)%Z with 1%Z.
    rewrite big_sepL_app.
    iDestruct "Hd" as "[Hinodes Hfree]".
    iDestruct "Hinodes" as "[Hzero _]".
    change (0%nat + 0)%Z with (int.val (U64 0)).
    iDestruct (init_inode with "Hzero") as "Hinode".
    simpl.
    iMod (ghost_var_alloc (nil : list Block)) as
        (γblocks) "[Hγblocks Hownblocks]".
    iMod (ghost_var_alloc (∅ : gset u64)) as
        (γused) "[Hγused Hownused]".
    iModIntro.
    iExists γblocks, γused. iFrame "Hγblocks".
    iSplitL "Hinode Hownblocks Hownused".
    - iExists (inode.mk ∅ []).
      iFrame.
    - pose proof (new_alloc_state_properties 1 (sz-1) ∅ ltac:(set_solver))
        as (Hdom&Hpost_crash&Hused&Hunused).
      iExists (new_alloc_state 1 (sz-1) ∅).
      iSplitR; first eauto.
      iSplitR.
      { rewrite /alloc.domain in Hdom; eauto. }
      rewrite /Palloc Hused.
      iFrame "Hγused".
      rewrite Hunused difference_empty_L.
      rewrite /rangeSet.
      rewrite big_sepS_list; last first.
      { apply seq_U64_NoDup; word. }
      rewrite big_sepL_fmap.
      iApply (big_sepL_mono with "Hfree").
      iIntros (???) "H".
      iExists _.
      iExactEq "H".
      f_equiv.
      apply lookup_seqZ in H.
      word.
  Qed.

  Theorem unify_used_set γblocks γused s_alloc s_inode :
    Palloc γused s_alloc -∗
    Pinode γblocks γused s_inode -∗
    ⌜s_inode.(inode.addrs) = alloc.used s_alloc⌝.
  Proof.
    rewrite /Palloc; iNamed 1. (* TODO: shouldn't need to unfold, this is a bug
    in iNamed *)
    iNamed 1.
    iDestruct (ghost_var_agree with "Hused2 Hused1") as %->.
    auto.
  Qed.

  Theorem wpc_Open {k} (d_ref: loc) (sz: u64) k' σ0 :
    (k' < k)%nat →
    (0 < int.val sz)%Z →
    {{{ "Hcinv" ∷ s_inode_cinv (int.val sz) σ0 true }}}
      Open #d_ref #sz @ NotStuck; S k; ⊤
    {{{ l, RET #l; pre_s_inode l (int.val sz) σ0 }}}
    {{{ s_inode_cinv (int.val sz) σ0 true }}}.
  Proof.
    iIntros (?? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
    wpc_call.
    { iFrame. }
    { iFrame. }
    iNamed "Hcinv".
    iNamed "Hinode".
    iCache with "HΦ Halloc Hs_inode Hinode_cinv HPinode".
    { crash_case.
      iExists _, _. iFrame. iExists _. iFrame. }
    wpc_pures.
    wpc_apply (inode_proof.wpc_Open with "Hinode_cinv").
    iSplit.
    { iLeft in "HΦ". iModIntro. iNext. iIntros "Hinode_cinv".
      iApply "HΦ". iExists _, _. iFrame. iExists _. iFrame. }
    iIntros "!>" (inode_ref) "Hpre_inode".
    iCache with "HΦ Halloc Hs_inode Hpre_inode HPinode".
    { iDestruct (pre_inode_to_cinv with "Hpre_inode") as "Hinode_cinv".
      iFromCache. }
    (* finished opening inode *)

    wpc_pures.
    wpc_frame_seq.
    change (InjLV #()) with (zero_val (mapValT (struct.t alloc.unit.S))).
    wp_apply wp_NewMap.
    iIntros (mref) "Hused".
    iDestruct (is_addrset_from_empty with "Hused") as "Hused".
    iNamed 1.
    wpc_pures.
    iDestruct (pre_inode_read_addrs with "Hpre_inode") as (addrs) "(Hused_blocks&Hdurable&Hpre_inode)".
    wpc_bind_seq.
    wpc_frame "HΦ Halloc Hs_inode Hdurable HPinode".
    { crash_case.
      iExists _, _; iFrame.
      iExists _; iFrame.
      iExists _; iFrame. }

    (* reconstruct the used set from the inode *)
    wp_apply (wp_Inode__UsedBlocks with "Hused_blocks").
    iIntros (s) "(Haddrs&%Haddr_set&Hused_blocks)".
    iDestruct (is_slice_small_read with "Haddrs") as "[Haddrs_small Haddrs]".
    wp_apply (wp_SetAdd with "[$Hused $Haddrs_small]").
    iIntros "[Hused Haddrs_small]".
    iSpecialize ("Haddrs" with "Haddrs_small").
    iSpecialize ("Hused_blocks" with "Haddrs").
    iNamed 1.
    iSpecialize ("Hpre_inode" with "Hused_blocks Hdurable").
    wpc_pures.

    (* we need to do a little work to prove that the reconstructed used set is
    correct (since it's just stored in the one inode, this is just unifying two ghost variables) *)
    rewrite left_id_L Haddr_set.
    iDestruct "Halloc" as (s_alloc) "Halloc"; iNamed "Halloc".
    iDestruct (unify_used_set with "HPalloc HPinode") as %Hused_inode.

    iCache with "HΦ Hs_inode Hpre_inode HPinode HPalloc Hunused".
    { iAssert (alloc_crash_cond (Palloc γused) allocΨ (rangeSet 1 (int.val sz - 1)) true)
            with "[HPalloc Hunused]" as "Halloc".
      { iExists _; iFrame "∗ %". }
      iFromCache. }
    wpc_frame_seq.
    iApply (wp_newAllocator s_alloc with "Hused").
    { word. }
    { word_cleanup; auto. }
    { congruence. }
    { auto. }
    iIntros "!>" (alloc_ref) "Halloc_mem".
    iNamed 1.
    wpc_pures.
    wpc_frame.
    rewrite -wp_fupd.
    wp_apply wp_allocStruct.
    { auto. }
    iIntros (l) "Hstruct".
    iDestruct (struct_fields_split with "Hstruct") as "(i&alloc&_)".
    iMod (readonly_alloc_1 with "i") as "#i".
    iMod (readonly_alloc_1 with "alloc") as "#alloc".
    iModIntro.
    iNamed 1.
    iApply "HΦ".
    iExists inode_ref, alloc_ref, _, _.
    iFrame "Hs_inode".
    iSplitR.
    { iFrame "#". }
    iSplitL "Hpre_inode HPinode".
    { iExists _; iFrame. }
    iExists _; iFrame "∗ %".
  Qed.

  Lemma is_allocator_pre_post_crash alloc_ref s_alloc :
    is_allocator_mem_pre alloc_ref s_alloc -∗ ⌜alloc_post_crash s_alloc⌝.
  Proof.
    iNamed 1.
    iFrame "%".
  Qed.

  Theorem pre_s_inode_to_cinv l sz σ :
    pre_s_inode l sz σ -∗
    s_inode_cinv sz σ true.
  Proof.
    iNamed 1.
    iExists _, _; iFrame.
    iNamed "Hinode".
    iNamed "Halloc".
    iDestruct (is_allocator_pre_post_crash with "Halloc_mem") as %Hpost_crash.
    iSplitL "Hpre_inode HPinode".
    { iExists _; iFrame.
      iNamed "Hpre_inode".
      iApply inode_linv_to_cinv; auto. }
    iExists _; iFrame "∗ %".
  Qed.

  Theorem is_single_inode_alloc  k l (sz: Z) σ :
    (1 ≤ sz < 2^64)%Z →
    ▷ P σ -∗
    pre_s_inode l sz σ ={⊤}=∗
    is_single_inode l sz k ∗
    <disc> |C={⊤}_(S k)=> ∃ σ', s_inode_cinv sz σ' false ∗ P σ'.
  Proof.
    iIntros (?) "HP"; iNamed 1.
    iNamed "Hinode".
    iNamed "Halloc".
    iMod (is_allocator_alloc _ _ _ k with "Hunused HPalloc Halloc_mem") as (γalloc) "[Halloc Halloc_crash]".
    iMod (is_inode_alloc inodeN (k:=k) with "HPinode Hpre_inode") as "[Hinode Hinode_crash]".
    (* TODO: allocate s_inode_inv invariant *)
    iMod (ncinv_alloc s_inodeN _ (∃ σ, s_inode_inv γblocks σ ∗ P σ)%I
            with "[Hs_inv HP]") as "(#Hinv&Hinv_crash)".
    { iNext.
      iExists _; iFrame. }
    rewrite Halloc_dom.
    iModIntro.
    iSplitL "Halloc Hinode".
    { iExists _, _, _, _, _. iFrame "Hinode". iFrame "Halloc".
      iFrame "# ∗". }
    iModIntro.
    iMod "Halloc_crash" as "Halloc".
    iMod "Hinode_crash" as "Hinode".
    iMod (cfupd_weaken_all with "Hinv_crash") as "Hs_inode"; first lia.
    { solve_ndisj. }
    iModIntro. iNext.
    iDestruct "Hs_inode" as (σ') "[Hs_inv HP]".
    iExists _; iFrame.
    iExists _, _; iFrame.
  Qed.

  Theorem wpc_Read {k} (Q: option Block → iProp Σ) l sz k' (i: u64) :
    (S k < k')%nat →
    {{{ "#Hinode" ∷ is_single_inode l sz k' ∗
        "Hfupd" ∷ (∀ σ mb,
                      ⌜mb = σ.(s_inode.blocks) !! int.nat i⌝ -∗
                      ▷ P σ ={⊤ ∖ ↑N}=∗ ▷ P σ ∗ Q mb)
    }}}
      SingleInode__Read #l #i @ NotStuck; (S k); ⊤
    {{{ (s:Slice.t) mb, RET (slice_val s);
        match mb with
        | None => ⌜s = Slice.nil⌝
        | Some b => is_block s 1 b
        end ∗ Q mb }}}
    {{{ True }}}.
  Proof.
    iIntros (? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
    wpc_call.
    { crash_case; auto. }
    { crash_case; auto. }
    iCache with "HΦ Hfupd".
    { crash_case; auto. }
    iNamed "Hinode". iNamed "Hro_state".
    wpc_pures.
    wpc_loadField.
    wpc_apply (wpc_Inode__Read inodeN (k':=k') with "Hinode").
    { lia. }
    iIntros (σ mb) "[ -> >HPinode]".
    iInv "Hinv" as "Hinner".
    iDestruct "Hinner" as ([σ']) "[>Hsinv HP]".
    iMod fupd_intro_mask' as "HcloseM"; (* adjust mask *)
      last iMod ("Hfupd" with "[% //] HP") as "[HP HQ]".
    { solve_ndisj. }
    rewrite {2}/s_inode_inv. iNamed "Hsinv".
    iNamed "HPinode". simpl.
    iDestruct (ghost_var_agree with "Hγblocks Hownblocks") as %->.
    iMod "HcloseM" as "_".
    iModIntro.
    iFrame.
    iSplitR "HΦ HQ"; first by eauto with iFrame.
    iModIntro. iSplit.
    - crash_case; auto.
    - iIntros (s) "Hb".
      iApply "HΦ"; iFrame. done.
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

  Theorem wpc_Append {k} (Q: iProp Σ) l sz b_s b0 k' :
    (S k < k')%nat →
    {{{ "Hinode" ∷ is_single_inode l sz k' ∗
        "Hb" ∷ is_block b_s 1 b0 ∗
        "Hfupd" ∷ ((∀ σ σ',
          ⌜σ' = s_inode.mk (σ.(s_inode.blocks) ++ [b0])⌝ -∗
         ▷ P σ ={⊤ ∖ ↑N}=∗ ▷ P σ' ∗ Q))
    }}}
      SingleInode__Append #l (slice_val b_s) @ NotStuck; (S k); ⊤
    {{{ (ok: bool), RET #ok; if ok then Q else emp }}}
    {{{ True }}}.
  Proof.
    iIntros (? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
    wpc_call.
    { crash_case; auto. }
    { crash_case; auto. }
    iCache with "HΦ".
    { crash_case; auto. }
    wpc_pures.
    iNamed "Hinode". iNamed "Hro_state".
    wpc_loadField. wpc_loadField.
    wpc_apply (wpc_Inode__Append inodeN allocN (n:=k') (k':=k'));
      [lia|lia|solve_ndisj|..].
    iFrame "Hb Hinode Halloc".
    iSplit; [ | iSplit; [ | iSplit ] ].
    - iApply reserve_fupd_Palloc.
    - iApply free_fupd_Palloc.
    - iLeft in "HΦ". iModIntro. by iApply "HΦ".
    - iSplit.
      { (* Failure case. *) iApply "HΦ". done. }
      iNext.
      iIntros (σ σ' addr' -> Hwf s Hreserved) "(>HPinode&>HPalloc)".
      iEval (rewrite /Palloc) in "HPalloc"; iNamed.
      iNamed "HPinode".
      iDestruct (ghost_var_agree with "Hused2 Hused1") as %Heq.
      rewrite <-Heq.
      iInv "Hinv" as ([σ0]) "[>Hinner HP]" "Hclose".
      iMod (ghost_var_update (union {[addr']} σ.(inode.addrs))
              with "[$Hused2 $Hused1 //]") as
          "[Hused Hγused]".
      iDestruct (ghost_var_agree with "Hinner Hownblocks") as %?; simplify_eq/=.
      iMod (ghost_var_update ((σ.(inode.blocks) ++ [b0]))
              with "[$Hinner $Hownblocks //]") as "[Hγblocks Hownblocks]".
      iMod fupd_intro_mask' as "HcloseM"; (* adjust mask *)
        last iMod ("Hfupd" with "[% //] [$HP]") as "[HP HQ]".
      { solve_ndisj. }
      iMod "HcloseM" as "_".
      simpl. iMod ("Hclose" with "[Hγblocks HP]") as "_".
      { eauto with iFrame. }
      iModIntro.
      iFrame.
      rewrite /Palloc.
      rewrite alloc_used_insert -Heq.
      iFrame.
      iSplit; first by crash_case.
      iApply "HΦ". done.
  Qed.

End goose.
