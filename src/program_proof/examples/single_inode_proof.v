From RecordUpdate Require Import RecordSet.

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

(* discrete ofe over lists *)
Canonical Structure listLO A := leibnizO (list A).

Section goose.
  Context `{!heapG Σ}.
  Context `{!lockG Σ}.
  Context `{!crashG Σ}.
  Context `{!allocG Σ}.
  Context `{!stagedG Σ}.
  Context `{!inG Σ (ghostR (listLO Block))}.

  Implicit Types (l:loc) (σ: s_inode.t) (γ: gname).

  Let N := nroot.@"single_inode".
  Let allocN := nroot.@"allocator".
  Let inodeN := nroot.@"inode".
  Context (P: s_inode.t → iProp Σ).

  Definition Pinode γblocks γused (s: inode.t): iProp Σ :=
    "Hownblocks" ∷ own γblocks (◯ Excl' (s.(inode.blocks): listLO Block)) ∗
    "Hused1" ∷ own γused (●{1/2} Excl' s.(inode.addrs)).

  Definition Palloc γused (s: alloc.t): iProp Σ :=
    "Hused2" ∷ own γused (●{1/2} Excl' (alloc.used s)).

  Definition s_inode_inv γblocks γused (blocks: list Block) (used: gset u64): iProp Σ :=
    "Hγblocks" ∷ own γblocks (● Excl' (blocks : listLO Block)) ∗
    "Hγused" ∷ own γused (◯ Excl' used).

  Definition s_inode_state l (inode_ref alloc_ref: loc) : iProp Σ :=
    "#i" ∷ readonly (l ↦[SingleInode.S :: "i"] #inode_ref) ∗
    "#alloc" ∷ readonly (l ↦[SingleInode.S :: "alloc"] #alloc_ref).

  Definition allocΨ (a: u64): iProp Σ := ∃ b, int.val a d↦ b.

  Definition pre_s_inode l sz k'  : iProp Σ :=
    ∃ inode_ref alloc_ref
      γinode γalloc γused γblocks,
    s_inode_state l inode_ref alloc_ref ∗
    (∃ s_inode, pre_inode inode_ref γinode (U64 0) s_inode ∗
                Pinode γblocks γused s_inode) ∗
    (* TODO: is_allocator_pre and the allocator's initialization are very
    different from the others - it consumes P, and the crash obligation can be
    initialized without the allocator (because the allocator manages durable
    state separate from its physical state) *)
    (∃ s_alloc, is_allocator_pre (Palloc γused)
                allocΨ allocN γalloc k' (rangeSet 1 (sz-1)) s_alloc).

  Definition is_single_inode l (sz: Z) k' : iProp Σ :=
    ∃ (inode_ref alloc_ref: loc) γinode γalloc γused γblocks,
      "Hro_state" ∷ s_inode_state l inode_ref alloc_ref ∗
      "#Hinode" ∷ is_inode inode_ref (LVL k') γinode (Pinode γblocks γused) (U64 0) ∗
      "#Halloc" ∷ is_allocator (Palloc γused)
        allocΨ allocN alloc_ref (rangeSet 1 (sz-1)) γalloc k' ∗
      "#Hinv" ∷ inv N (∃ σ (used:gset u64),
                          s_inode_inv γblocks γused σ used ∗
                          P σ)
  .

  Definition s_inode_cinv σ : iProp Σ :=
    ∃ γblocks γused,
    "Hinode" ∷ (∃ s_inode, "Hinode_cinv" ∷ inode_cinv (U64 0) s_inode ∗
                           "HPinode" ∷ Pinode γblocks γused s_inode) ∗
    "Halloc" ∷ alloc_crash_cond (Palloc γused) allocΨ ∗
    "Hs_inode" ∷ (∃ used, s_inode_inv γblocks γused σ used)
  .

  Instance s_inode_inv_Timeless :
    Timeless (s_inode_inv γblocks γused blocks used).
  Proof. apply _. Qed.

  Theorem wpc_Open {k E2} (d_ref: loc) (sz: u64) k' σ0 :
    (k' < k)%nat →
    {{{ "Hcinv" ∷ s_inode_cinv σ0 ∗ "HP" ∷ P σ0 }}}
      Open #d_ref #sz @ NotStuck; LVL (S k); ⊤; E2
    {{{ l, RET #l; pre_s_inode l (int.val sz) k' }}}
    {{{ ∃ σ', s_inode_cinv σ' ∗ P σ' }}}.
  Proof.
    iIntros (? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
    wpc_call.
    { eauto with iFrame. }
    iNamed "Hcinv".
    iNamed "Hinode".
    iCache with "HΦ HP Halloc Hs_inode Hinode_cinv HPinode".
    { crash_case.
      iExists _; iFrame.
      iExists _, _; iFrame.
      iExists _; iFrame. }
    wpc_apply (inode_proof.wpc_Open with "Hinode_cinv").
    iSplit.
    { iIntros  "Hinode_cinv".
      iFromCache. }
    iIntros "!>" (l γ) "Hpre_inode".
    iApply (inode_crash_obligation _ _ k' with "HPinode Hpre_inode").
    { lia. }
    iIntros "Hinode".
    iCache with "HΦ HP Halloc Hs_inode".
    { iDestruct 1 as (s_inode') "(Hinode_cinv&HPinode)".
      crash_case.
      (* TODO: replace with eauto automation *)
      iExists _; iFrame.
      iExists _, _; iFrame.
      iExists _; iFrame. }
    wpc_pures.
    wpc_frame_seq.
    change (InjLV #()) with (zero_val (mapValT (struct.t alloc.unit.S))).
    wp_apply wp_NewMap.
    iIntros (mref) "Hused".
    iNamed 1.
    wpc_pures.
    wpc_frame_seq.
    (* TODO: we need to run this before initializing the inode with
    [inode_crash_obligation], but that is necessary to dismiss the inode stuff
    from the crash obligation after opening. What went wrong? *)
    wp_apply wp_Inode__UsedBlocks.
  Abort.

  Theorem wpc_Read {k E2} (Q: option Block → iProp Σ) l sz k' (i: u64) :
    (S k < k')%nat →
    {{{ "#Hinode" ∷ is_single_inode l sz k' ∗
        "Hfupd" ∷ (∀ σ mb,
                      ⌜mb = σ !! int.nat i⌝ -∗
                      ▷ P σ ={⊤ ∖ ↑inodeN ∖ ↑N}=∗ ▷ P σ ∗ Q mb)
    }}}
      SingleInode__Read #l #i @ NotStuck; LVL (S (S k)); ⊤;E2
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
    iCache with "HΦ Hfupd".
    { crash_case; auto. }
    iNamed "Hinode". iNamed "Hro_state".
    wpc_bind (struct.loadF _ _ _); wpc_frame.
    wp_loadField.
    iNamed 1.
    wpc_apply (wpc_Inode__Read Q with "[$Hinode Hfupd]").
    { lia. }
    { clear.
      iIntros (σ σ' mb) "[ [-> ->] HPinode]".
      iInv "Hinv" as "Hinner".
      iDestruct "Hinner" as (σ' used) "[>Hsinv HP]".
      iMod ("Hfupd" with "[% //] HP") as "[HP HQ]".
      iNamed "Hsinv".
      iNamed "HPinode".
      iDestruct (ghost_var_agree with "Hγblocks Hownblocks") as %->.
      iModIntro.
      iFrame.
      iSplitL; auto.
      iNext.
      iExists _, _; iFrame. }
    iSplit.
    - iIntros "_".
      crash_case; auto.
    - iIntros "!>" (s mb) "[Hb HQ]".
      iApply "HΦ"; iFrame.
  Qed.

  Lemma alloc_used_reserve s u :
    u ∈ alloc.free s →
    alloc.used (<[u:=block_reserved]> s) =
    alloc.used s.
  Proof.
    rewrite /alloc.free /alloc.used.
    intros Hufree.
    apply elem_of_dom in Hufree as [status Hufree].
    apply map_filter_lookup_Some in Hufree as [Hufree ?];
      simpl in *; subst.
    rewrite map_filter_insert_not_strong //=.
  Admitted.

  Lemma alloc_free_reserved s a :
    s !! a = Some block_reserved →
    alloc.used (<[a := block_free]> s) =
    alloc.used s.
  Proof.
    rewrite /alloc.used.
    intros Hareserved.
    rewrite map_filter_insert_not_strong //=.
  Admitted.

  Lemma alloc_used_insert s a :
    alloc.used (<[a := block_used]> s) = {[a]} ∪ alloc.used s.
  Proof.
    rewrite /alloc.used.
    rewrite map_filter_insert //.
    set_solver.
  Qed.

  Theorem wpc_Append {k E2} (Q: iProp Σ) l sz b_s b0 k' :
    (3 + k < k')%nat →
    {{{ "Hinode" ∷ is_single_inode l sz k' ∗
        "Hb" ∷ is_block b_s 1 b0 ∗
        "Hfupd" ∷ ((∀ σ σ',
          ⌜σ' = σ ++ [b0]⌝ -∗
        (* TODO: to be able to use an invariant within another HOCAP fupd I had
        to make this fupd from [▷ P(σ)] to [▷ P(σ')] rather than our usual
        [P(σ)] to [P(σ')]; normally we seem to get around this by linearizing at
        a Skip? *)
         ▷ P σ ={⊤ ∖ ↑allocN ∖ ↑inodeN ∖ ↑N}=∗ ▷ P σ' ∗ Q))
    }}}
      SingleInode__Append #l (slice_val b_s) @ NotStuck; LVL (S (S (S (S k)))); ⊤; E2
    {{{ (ok: bool), RET #ok; if ok then Q else emp }}}
    {{{ True }}}.
  Proof.
    iIntros (? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
    wpc_call.
    { crash_case; auto. }
    iCache with "HΦ".
    { crash_case; auto. }
    iNamed "Hinode". iNamed "Hro_state".
    wpc_bind (struct.loadF _ _ _); wpc_frame "HΦ".
    wp_loadField.
    iNamed 1.
    wpc_bind (struct.loadF _ _ _); wpc_frame "HΦ".
    wp_loadField.
    iNamed 1.
    wpc_apply (wpc_Inode__Append Q emp%I
                 with "[$Hb $Hinode $Halloc Hfupd]");
      try lia; try solve_ndisj.
    {
      iSplitR.
      { by iIntros "_". }
      iSplit; [ | iSplit; [ | iSplit ] ]; try iModIntro.
      - iIntros (s s' ma Hma) "HPalloc".
        destruct ma; intuition subst; auto.
        iEval (rewrite /Palloc) in "HPalloc"; iNamed.
        iEval (rewrite /Palloc /named).
        rewrite alloc_used_reserve //.
      - iIntros (a s s') "HPalloc".
        iEval (rewrite /Palloc) in "HPalloc"; iNamed.
        iEval (rewrite /Palloc /named).
        rewrite alloc_free_reserved //.
      - iIntros (σ σ' addr' -> Hwf s Hreserved) "(HPinode&HPalloc)".
        iEval (rewrite /Palloc) in "HPalloc"; iNamed.
        iNamed "HPinode".
        iDestruct (ghost_var_frac_frac_agree with "Hused1 Hused2") as %Heq;
          rewrite -Heq.
        iCombine "Hused1 Hused2" as "Hused".
        iInv "Hinv" as (σ0 used) "[>Hinner HP]" "Hclose".
        iNamed "Hinner".
        iDestruct (ghost_var_agree with "Hused Hγused") as %?; subst.
        iMod (ghost_var_update _ (union {[addr']} σ.(inode.addrs))
                               with "Hused Hγused") as
            "[Hused Hγused]".
        iDestruct (ghost_var_agree with "Hγblocks Hownblocks") as %?; subst.
        iMod (ghost_var_update _ ((σ.(inode.blocks) ++ [b0]) : listLO Block)
                with "Hγblocks Hownblocks") as "[Hγblocks Hownblocks]".
        iMod ("Hfupd" with "[% //] [$HP]") as "[HP HQ]".
        iDestruct "Hused" as "[Hused1 Hused2]".
        iMod ("Hclose" with "[Hγused Hγblocks HP]") as "_".
        { iNext.
          iExists _, _; iFrame. }
        iModIntro.
        iFrame.
        rewrite /Palloc.
        rewrite alloc_used_insert -Heq.
        iFrame.
      - auto.
    }
    iSplit.
    { iIntros "_".
      iFromCache. }
    iNext.
    iIntros (ok) "HQ".
    iApply "HΦ"; auto.
  Qed.

End goose.
