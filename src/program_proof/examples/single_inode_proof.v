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

Module s_inode.
  Record t :=
    mk { blocks: list Block; }.
  Global Instance _eta : Settable t := settable! mk <blocks>.
  Global Instance _witness : Inhabited t := populate!.
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
    "Hownblocks" ∷ own γblocks (◯ Excl' (s.(inode.blocks): listLO Block)) ∗
    "Hused1" ∷ own γused (◯ Excl' s.(inode.addrs)).

  (** Protocol invariant for alloc library *)
  Local Definition Palloc γused (s: alloc.t): iProp Σ :=
    "Hused2" ∷ own γused (● Excl' (alloc.used s)).

  (** Our own invariant (added to this is [P blocks]) *)
  Definition s_inode_inv γblocks (blocks: s_inode.t): iProp Σ :=
    "Hγblocks" ∷ own γblocks (● Excl' (blocks.(s_inode.blocks) : listLO Block)).

  (** In-memory state of the inode (persistent) *)
  Definition s_inode_state l (inode_ref alloc_ref: loc) : iProp Σ :=
    "#i" ∷ readonly (l ↦[SingleInode.S :: "i"] #inode_ref) ∗
    "#alloc" ∷ readonly (l ↦[SingleInode.S :: "alloc"] #alloc_ref).

  (** State of unallocated blocks *)
  Local Definition allocΨ (a: u64): iProp Σ := ∃ b, int.val a d↦ b.

  Definition pre_s_inode l (sz: Z) : iProp Σ :=
    ∃ inode_ref alloc_ref
      γinode γused γblocks,
    s_inode_state l inode_ref alloc_ref ∗
    (∃ s_inode, pre_inode inode_ref γinode (U64 0) s_inode ∗
                Pinode γblocks γused s_inode) ∗
    (∃ s_alloc, is_allocator_mem_pre alloc_ref s_alloc ∗
                ⌜alloc.domain s_alloc = rangeSet 1 (sz-1)⌝ ∗
                Palloc γused s_alloc).

  Definition is_single_inode l (sz: Z) k' : iProp Σ :=
    ∃ (inode_ref alloc_ref: loc) γinode γalloc γused γblocks,
      "Hro_state" ∷ s_inode_state l inode_ref alloc_ref ∗
      "#Hinode" ∷ is_inode inodeN inode_ref (LVL k') γinode (Pinode γblocks γused) (U64 0) ∗
      "#Halloc" ∷ is_allocator (Palloc γused)
        allocΨ allocN alloc_ref (rangeSet 1 (sz-1)) γalloc k' ∗
      "#Hinv" ∷ inv s_inodeN (∃ σ, s_inode_inv γblocks σ ∗ P σ)
  .

  Definition s_inode_cinv sz σ : iProp Σ :=
    ∃ γblocks γused,
    "Hinode" ∷ (∃ s_inode, "Hinode_cinv" ∷ inode_cinv (U64 0) s_inode ∗
                           "HPinode" ∷ Pinode γblocks γused s_inode) ∗
    "Halloc" ∷ alloc_crash_cond (Palloc γused) allocΨ (rangeSet 1 (sz-1)) ∗
    "Hs_inode" ∷ (s_inode_inv γblocks σ)
  .
  Local Hint Extern 1 (environments.envs_entails _ (s_inode_cinv _)) => unfold s_inode_cinv : core.

  Instance s_inode_inv_Timeless :
    Timeless (s_inode_inv γblocks blocks).
  Proof. apply _. Qed.

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

  Theorem wpc_Open {k E2} (d_ref: loc) (sz: u64) k' σ0 :
    (k' < k)%nat →
    ↑allocN ⊆ E2 →
    (0 < int.val sz)%Z →
    {{{ "Hcinv" ∷ s_inode_cinv (int.val sz) σ0 ∗ "HP" ∷ ▷ P σ0 }}}
      Open #d_ref #sz @ NotStuck; LVL (S (S (S k + (int.nat sz-1)))); ⊤; E2
    {{{ l, RET #l; pre_s_inode l (int.val sz) }}}
    {{{ ∃ σ', s_inode_cinv (int.val sz) σ' ∗ ▷ P σ' }}}.
  Proof.
    iIntros (??? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
    wpc_call.
    { eauto with iFrame. }
    iNamed "Hcinv".
    iNamed "Hinode".
    iCache with "HΦ HP Halloc Hs_inode Hinode_cinv HPinode".
    { crash_case. iExists _. iFrame. iExists _, _. iFrame. iExists _. iFrame. }
    wpc_apply (inode_proof.wpc_Open with "Hinode_cinv").
    iSplit.
    { iIntros  "Hinode_cinv".
      iFromCache. }
    iIntros "!>" (inode_ref γ) "Hpre_inode".
    iCache with "HΦ HP Halloc Hs_inode Hpre_inode HPinode".
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
    wpc_frame "HΦ HP Halloc Hs_inode Hdurable HPinode".
    { crash_case.
      iExists _; iFrame.
      iExists _, _; iFrame.
      iExists _; iFrame.
      iExists _; iFrame. }

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
    wpc_frame_seq.
    (* TODO: provide the reconstructed allocator state (a map constructed from
    the used set and the domain) *)
    iApply (wp_newAllocator with "[$Hused]").
    { word. }

    (*
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
    iExists _, _, _, _, _, _; iFrame "# ∗".
*)
  Abort.

  Theorem wpc_Read {k E2} (Q: option Block → iProp Σ) l sz k' (i: u64) :
    (S k < k')%nat →
    {{{ "#Hinode" ∷ is_single_inode l sz k' ∗
        "Hfupd" ∷ (∀ σ mb,
                      ⌜mb = σ.(s_inode.blocks) !! int.nat i⌝ -∗
                      ▷ P σ ={⊤ ∖ ↑N}=∗ ▷ P σ ∗ Q mb)
    }}}
      SingleInode__Read #l #i @ NotStuck; LVL (S k); ⊤;E2
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
    wpc_apply (wpc_Inode__Read_triple inodeN Q with "[$Hinode Hfupd]").
    { lia. }
    { clear.
      iIntros (σ σ' mb) "[ [-> ->] >HPinode]".
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
      iSplitL; auto.
      eauto with iFrame. }
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
    (2 + k < k')%nat →
    nroot.@"readonly" ## N →
    {{{ "Hinode" ∷ is_single_inode l sz k' ∗
        "Hb" ∷ is_block b_s 1 b0 ∗
        "Hfupd" ∷ ((∀ σ σ',
          ⌜σ' = s_inode.mk (σ.(s_inode.blocks) ++ [b0])⌝ -∗
         ▷ P σ ={⊤ ∖ ↑N}=∗ ▷ P σ' ∗ Q))
    }}}
      SingleInode__Append #l (slice_val b_s) @ NotStuck; LVL (S (S k)); ⊤; E2
    {{{ (ok: bool), RET #ok; if ok then Q else emp }}}
    {{{ True }}}.
  Proof.
    iIntros (?? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
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
    wpc_apply (wpc_Inode__Append inodeN allocN Q emp%I
                 with "[$Hb $Hinode $Halloc Hfupd]");
      [lia|lia|solve_ndisj|solve_ndisj|solve_ndisj|..].
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
      - iIntros (σ σ' addr' -> Hwf s Hreserved) "(>HPinode&>HPalloc)".
        iEval (rewrite /Palloc) in "HPalloc"; iNamed.
        iNamed "HPinode".
        iDestruct (ghost_var_agree with "Hused2 Hused1") as %Heq;
          rewrite -Heq.
        iInv "Hinv" as ([σ0]) "[>Hinner HP]" "Hclose".
        iNamed "Hinner".
        iMod (ghost_var_update _ (union {[addr']} σ.(inode.addrs))
                               with "Hused2 Hused1") as
            "[Hused Hγused]".
        iDestruct (ghost_var_agree with "Hinner Hownblocks") as %?; simplify_eq/=.
        iMod (ghost_var_update _ ((σ.(inode.blocks) ++ [b0]) : listLO Block)
                with "Hinner Hownblocks") as "[Hγblocks Hownblocks]".
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
