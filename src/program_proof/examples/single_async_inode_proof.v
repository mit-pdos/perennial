From RecordUpdate Require Import RecordSet.

From Perennial.goose_lang Require Import crash_modality.

From Perennial.algebra Require Import mlist.
From Goose.github_com.mit_pdos.perennial_examples Require Import single_async_inode.
From Perennial.goose_lang.lib Require Import lock.crash_lock.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import disk_prelude.
From Perennial.program_proof.examples Require Import
     alloc_addrset alloc_crash_proof async_inode_proof.
From Perennial.goose_lang.lib Require Export typed_slice into_val.

Remove Hints fractional.into_sep_fractional : typeclass_instances.

Module s_inode.
  Record t :=
    mk { durable_blocks: list Block;
         buffered_blocks: list Block
       }.
  Global Instance _eta : Settable t := settable! mk <durable_blocks; buffered_blocks>.
  Global Instance _witness : Inhabited t := populate!.
End s_inode.

Section goose.
  Context `{!heapG Σ}.
  Context `{!allocG Σ}.
  Context `{!stagedG Σ}.
  Context `{fmlistG Block Σ}.
  Context `{!ghost_varG Σ (list Block)}.

  Implicit Types (l:loc) (σ: s_inode.t) (γ: gname).

  (* The client picks our namespace *)
  Context (N: namespace).
  (* We use parts of it ourselves and assign the rest to sub-libraries. *)
  Let s_inodeN := N.@"single_inode".
  Let allocN := N.@"allocator".
  Let inodeN := N.@"inode".

  (* CONVENTION: γ is used to prefix resource names exported to the client, δ is
     used for internal resources used to coordinate with async_inode and
     allocator library *)

  (* For γdur, we store the full permission, to allow any thread to call flush.
     For γbuf blocks, we store 1/2 permission. The other 1/2 is given to the exclusive permission
     needed in a call to append.  *)
  Definition P γdur γbuf (s: s_inode.t) : iProp Σ :=
    "Hfm_dur_blocks" ∷ fmlist γdur 1 (s.(s_inode.durable_blocks)) ∗
    "Hfm_all_blocks" ∷ fmlist γbuf (1/2) (s.(s_inode.durable_blocks) ++ s.(s_inode.buffered_blocks)).

  (** Protocol invariant for inode library *)
  Local Definition Pinode δdur δbuf δused (s: inode.t): iProp Σ :=
    "Hown_dur_blocks" ∷ ghost_var δdur (1/2) s.(inode.durable_blocks) ∗
    "Hown_buf_blocks" ∷ ghost_var δbuf (1/2) s.(inode.buffered_blocks) ∗
    "Hused1" ∷ ghost_var δused (1/2) s.(inode.addrs).

  Local Definition Pinode_cinv δdur δused (s: inode.t): iProp Σ :=
    "Hown_dur_blocks" ∷ ghost_var δdur (1/2) s.(inode.durable_blocks) ∗
    "Hused1" ∷ ghost_var δused (1/2) s.(inode.addrs).

  (** Protocol invariant for alloc library *)
  Local Definition Palloc δused (s: alloc.t): iProp Σ :=
    "Hused2" ∷ ghost_var δused (1/2) (alloc.used s).

  (** Our own invariant (added to this is [P blocks]) *)
  Definition s_inode_inv δdur δbuf (σ: s_inode.t): iProp Σ :=
    "Hδdurable_blocks" ∷ ghost_var δdur (1/2) σ.(s_inode.durable_blocks) ∗
    "Hδbuffered_blocks" ∷ ghost_var δbuf (1/2) σ.(s_inode.buffered_blocks).

  (** In-memory state of the inode (persistent) *)
  Definition s_inode_state l (inode_ref alloc_ref: loc) : iProp Σ :=
    "#i" ∷ readonly (l ↦[SingleInode :: "i"] #inode_ref) ∗
    "#alloc" ∷ readonly (l ↦[SingleInode :: "alloc"] #alloc_ref).

  (** State of unallocated blocks *)
  Local Definition allocΨ (a: u64): iProp Σ := ∃ b, int.Z a d↦ b.

  Definition pre_s_inode γdur γbuf l (sz: Z) σ : iProp Σ :=
    ∃ inode_ref alloc_ref δused δdur δbuf,
    "#Hstate" ∷ s_inode_state l inode_ref alloc_ref ∗
    "Hs_inv" ∷ s_inode_inv δdur δbuf σ ∗
    "Hinode" ∷ (∃ s_inode, "Hpre_inode" ∷ pre_inode inode_ref (U64 0) s_inode ∗
                "HPinode" ∷ Pinode δdur δbuf δused s_inode) ∗
    "Halloc" ∷ (∃ s_alloc, "Halloc_mem" ∷ is_allocator_mem_pre alloc_ref s_alloc ∗
                "%Halloc_dom" ∷ ⌜alloc.domain s_alloc = rangeSet 1 (sz-1)⌝ ∗
                "Hunused" ∷ ([∗ set] k ∈ alloc.unused s_alloc, allocΨ k) ∗
                "HPalloc" ∷ Palloc δused s_alloc) ∗
    "HP" ∷ P γdur γbuf σ.

  Definition is_single_inode γdur γbuf l (sz: Z) k' : iProp Σ :=
    ∃ (inode_ref alloc_ref: loc) δalloc δused δdur δbuf,
      "Hro_state" ∷ s_inode_state l inode_ref alloc_ref ∗
      "#Hinode" ∷ is_inode inodeN inode_ref (S k') (Pinode δdur δbuf δused) (U64 0) ∗
      "#Halloc" ∷ is_allocator (Palloc δused)
        allocΨ allocN alloc_ref (rangeSet 1 (sz-1)) δalloc k' ∗
      "#Hinv" ∷ ncinv s_inodeN (∃ σ, s_inode_inv δdur δbuf σ ∗ P γdur γbuf σ)
  .

  (* P is internal here, so we include it as part of s_inode_cinv, unlike the synch inode *)

  Definition s_inode_cinv γdur γbuf sz σ (post_crash: bool) : iProp Σ :=
    ∃ δdur δused,
    "Hinode" ∷ (∃ s_inode, "Hinode_cinv" ∷ inode_cinv (U64 0) s_inode ∗
                           "HPinode" ∷ Pinode_cinv δdur δused s_inode) ∗
    "Halloc" ∷ alloc_crash_cond (Palloc δused) allocΨ (rangeSet 1 (sz-1)) post_crash ∗
    "Hδdurable_blocks" ∷ ghost_var δdur (1/2) σ.(s_inode.durable_blocks) ∗
    "HP" ∷ P γdur γbuf σ
  .
  Local Hint Extern 1 (environments.envs_entails _ (s_inode_cinv _ _ _ _ _)) => unfold s_inode_cinv : core.

  Theorem s_inode_cinv_post_crash γdur γbuf sz σ :
    s_inode_cinv γdur γbuf sz σ true -∗ s_inode_cinv γdur γbuf sz σ false.
  Proof.
    iNamed 1.
    iExists _, _; iFrame.
    iApply (alloc_crash_cond_from_post_crash with "[$]").
  Qed.

  Instance s_inode_inv_Timeless δdur δbuf blocks :
    Timeless (s_inode_inv δdur δbuf blocks).
  Proof. apply _. Qed.

  (* inode_mapsto is an exclusive permission used for calls to append *)
  Definition inode_mapsto γbuf blocks : iProp Σ :=
    fmlist γbuf (1/2) blocks.

  (* inode_durable_lb is persistent and ensures that the specified list is a prefix of
     durable blocks *)
  Definition inode_durable_lb γdur γbuf blocks : iProp Σ :=
    fmlist_lb γdur blocks ∗
    fmlist_lb γbuf blocks.

  Lemma inode_mapsto_agree γbuf blocks blocks' :
    inode_mapsto γbuf blocks -∗ inode_mapsto γbuf blocks' -∗ ⌜ blocks = blocks' ⌝.
  Proof.
    iApply fmlist_agree_1.
  Qed.

  (* inode_current_lb is persistent, and states that the specified list is a
     prefix of the combination of durable + buffered blocks. It can be promoted
     to inode_durable_lb durable fact with a flush *)
  Definition inode_current_lb γbuf blocks : iProp Σ :=
    fmlist_lb γbuf blocks.

  Lemma inode_mapsto_lb_agree γbuf blocks blocks' :
    inode_mapsto γbuf blocks -∗ inode_current_lb γbuf blocks' -∗ ⌜ blocks' `prefix_of` blocks ⌝.
  Proof. iApply fmlist_agree_2. Qed.

  Lemma inode_mapsto_append γbuf blocks blocks' :
    inode_mapsto γbuf blocks -∗ inode_mapsto γbuf blocks ==∗
    inode_mapsto γbuf (blocks ++ blocks') ∗ inode_mapsto γbuf (blocks ++ blocks').
  Proof.
    iIntros "H1 H2".
    iCombine "H1 H2" as "H".
    iMod (fmlist_update with "H") as "(($&$)&?)"; eauto.
    econstructor; eauto.
  Qed.

  Theorem init_single_inode {E} (sz: Z) :
    (1 ≤ sz < 2^64)%Z →
    ([∗ list] i ∈ seqZ 0 sz, i d↦ block0) ={E}=∗
    let σ0 := s_inode.mk [] [] in
    ∃ γdur γbuf, s_inode_cinv γdur γbuf sz σ0 true ∗
                 inode_mapsto γbuf [].
  Proof.
    iIntros (Hbound) "Hd".
    replace sz with (1 + (sz - 1))%Z at 1 by lia.
    rewrite -> seqZ_app by lia.
    change (0 + 1)%Z with 1%Z.
    rewrite big_sepL_app.
    iDestruct "Hd" as "[Hinodes Hfree]".
    iDestruct "Hinodes" as "[Hzero _]".
    change (0%nat + 0)%Z with (int.Z (U64 0)).
    iDestruct (init_inode with "Hzero") as "Hinode".
    simpl.
    iMod (ghost_var_alloc (nil : list Block)) as
        (δdur) "[Hδdur Howndur]".
    iMod (ghost_var_alloc (∅ : gset u64)) as
        (δused) "[Hδused Hownused]".
    iMod (fmlist_alloc []) as
        (γdur) "Hγdur".
    iMod (fmlist_alloc []) as
        (γbuf) "(Hγbuf1&Hγbuf2)".
    iModIntro.
    iExists γdur, γbuf; iSplitR "Hγbuf2"; last by iFrame.
    iExists δdur, δused; iFrame "Hδdur Hγdur Hγbuf1".
    iSplitL "Hinode Howndur Hownused".
    - iExists (inode.mk ∅ [] []).
      iFrame.
    - pose proof (new_alloc_state_properties 1 (sz-1) ∅ ltac:(set_solver))
        as (Hdom&Hpost_crash&Hused&Hunused).
      iExists (new_alloc_state 1 (sz-1) ∅).
      iSplitR; first eauto.
      iSplitR.
      { rewrite /alloc.domain in Hdom; eauto. }
      rewrite /Palloc Hused.
      iFrame "Hδused".
      rewrite Hunused difference_empty_L.
      rewrite /rangeSet.
      rewrite big_sepS_list_to_set; last first.
      { apply seq_U64_NoDup; word. }
      rewrite big_sepL_fmap.
      iApply (big_sepL_mono with "Hfree").
      iIntros (?? Hseq) "H".
      iExists _.
      iExactEq "H".
      f_equiv.
      apply lookup_seqZ in Hseq.
      word.
  Qed.

  Theorem unify_used_set δdur δused s_alloc s_inode :
    Palloc δused s_alloc -∗
    Pinode_cinv δdur δused s_inode -∗
    ⌜s_inode.(inode.addrs) = alloc.used s_alloc⌝.
  Proof.
    rewrite /Palloc; iNamed 1. (* TODO: shouldn't need to unfold, this is a bug
    in iNamed *)
    iNamed 1.
    iDestruct (ghost_var_agree with "Hused2 Hused1") as %->.
    auto.
  Qed.

  Global Instance s_inode_cinv_discretizable γdur γbuf sz σ b:
    Discretizable (s_inode_cinv γdur γbuf sz σ b).
  Proof. apply _. Qed.

  Lemma P_get_lbs γdur γbuf σ:
    P γdur γbuf σ ==∗
    P γdur γbuf σ ∗
    inode_durable_lb γdur γbuf (s_inode.durable_blocks σ) ∗
    inode_current_lb γbuf (s_inode.durable_blocks σ ++ s_inode.buffered_blocks σ).
  Proof.
    iNamed 1.
    iMod (fmlist_get_lb with "Hfm_dur_blocks") as "($&$)".
    iMod (fmlist_get_lb with "Hfm_all_blocks") as "(Hfm_all_blocks&$)".
    iMod (fmlist_get_lb with "Hfm_all_blocks") as "($&Hlb)".
    iModIntro. iApply (fmlist_lb_mono with "Hlb"). eexists; eauto.
  Qed.

  Theorem wpc_Open {k} γdur γbuf (d_ref: loc) (sz: u64) k' σ0 :
    (k' < k)%nat →
    (0 < int.Z sz)%Z →
    {{{ "Hcinv" ∷ s_inode_cinv γdur γbuf (int.Z sz) σ0 true }}}
      Open #d_ref #sz @ S k; ⊤
    {{{ l, RET #l;
       ∃ γbuf', pre_s_inode γdur γbuf' l (int.Z sz) (set s_inode.buffered_blocks (λ _, []) σ0) ∗
                (* New buf points to fact *)
                inode_mapsto γbuf' (s_inode.durable_blocks σ0) ∗
                (* Durable lb for current state *)
                inode_durable_lb γdur γbuf' (s_inode.durable_blocks σ0) ∗
                (* Old buf points to fact *)
                inode_mapsto γbuf (s_inode.durable_blocks σ0 ++ s_inode.buffered_blocks σ0)
    }}}
    {{{ s_inode_cinv γdur γbuf (int.Z sz) σ0 true }}}.
  Proof.
    iIntros (?? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
    wpc_call.
    { iFrame. }
    { iFrame. }
    iNamed "Hcinv".
    iNamed "Hinode".
    iAssert (⌜ inode.wf s_inode ⌝)%I with "[Hinode_cinv]" as %Hswf.
    { iNamed "Hinode_cinv". eauto. }
    iCache with "HΦ Halloc Hδdurable_blocks Hinode_cinv HPinode HP".
    { crash_case.
      iExists _, _. iFrame. iExists _. iFrame. }
    wpc_pures.
    wpc_apply (async_inode_proof.wpc_Open with "Hinode_cinv").
    iSplit.
    { iLeft in "HΦ". iModIntro. iNext. iIntros "Hinode_cinv".
      iApply "HΦ". iExists _, _. iFrame. iExists _. iFrame. }
    iIntros "!>" (inode_ref) "Hpre_inode".
    iCache with "HΦ Halloc Hδdurable_blocks Hpre_inode HPinode HP".
    {
      iDestruct (pre_inode_to_cinv with "Hpre_inode") as "Hinode_cinv".
      crash_case.
      iExists _, _. iFrame. iExists _. iFrame. }

    (* finished opening inode *)
    wpc_pures.
    wpc_frame_seq.
    wp_apply (wp_NewMap _ (t:=struct.t alloc.unit)).
    iIntros (mref) "Hused".
    iDestruct (is_addrset_from_empty with "Hused") as "Hused".
    iNamed 1.
    wpc_pures.
    iDestruct (pre_inode_read_addrs with "Hpre_inode") as (addrs) "(Hused_blocks&Hdurable&Hpre_inode)".
    wpc_bind_seq.
    wpc_frame "HΦ Halloc Hδdurable_blocks Hdurable HPinode HP".
    { crash_case.
      iExists _, _; iFrame.
      iExists _; iFrame.
      iExists _; iFrame.
      iNamed "Hdurable". iExists _. iFrame.
      iNext. eauto.
    }

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

    iMod (P_get_lbs with "HP") as "(HP&Hdurable_lb&Hcurr_lb)".
    iCache with "HΦ Hδdurable_blocks Hpre_inode HPinode HPalloc Hunused HP".
    { iAssert (alloc_crash_cond (Palloc δused) allocΨ (rangeSet 1 (int.Z sz - 1)) true)
            with "[HPalloc Hunused]" as "Halloc".
      { iExists _; iFrame "∗ %". }
      iFromCache. }
    wpc_frame_seq.
    iApply (wp_newAllocator s_alloc with "Hused").
    { word. }
    { word_cleanup; auto. }
    { rewrite /=. congruence. }
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
    iMod (ghost_var_alloc (nil : list Block)) as
        (δbuf) "[Hδbuf Hownbuf]".
    iMod (fmlist_alloc (σ0.(s_inode.durable_blocks))) as
        (γbuf') "(Hγbuf1&Hγbuf2)".
    iMod (fmlist_get_lb with "Hγbuf1") as "(Hγbuf1&Hbuf_lb)".
    iModIntro.
    iNamed 1.
    iApply "HΦ".
    iExists γbuf'.
    iFrame "Hγbuf1".
    iNamed "HP".
    iFrame "Hfm_all_blocks".
    iDestruct "Hdurable_lb" as "($&_)".
    iFrame "Hbuf_lb".

    iExists inode_ref, alloc_ref, _, _, _.
    rewrite /s_inode_inv.
    iFrame "Hδdurable_blocks".
    iSplitR.
    { iFrame "#". }
    iSplitL "Hδbuf".
    { iApply "Hδbuf". }
    iSplitL "Hpre_inode HPinode Hownbuf".
    { iExists _; iFrame. rewrite /Pinode.
      iNamed "HPinode".
      iFrame "Hownbuf". iFrame. }
    iSplitR "Hfm_dur_blocks Hγbuf2".
    { iExists _. iFrame "∗ %". }
    iFrame. simpl. rewrite app_nil_r. iFrame.
  Qed.

  Lemma is_allocator_pre_post_crash alloc_ref s_alloc :
    is_allocator_mem_pre alloc_ref s_alloc -∗ ⌜alloc_post_crash s_alloc⌝.
  Proof.
    iNamed 1.
    iFrame "%".
  Qed.

  Theorem pre_s_inode_to_cinv γdur γbuf l sz σ :
    pre_s_inode γdur γbuf l sz σ -∗
    s_inode_cinv γdur γbuf sz σ true.
  Proof.
    iNamed 1.
    iExists _, _; iFrame.
    iNamed "Hinode".
    iNamed "Halloc".
    iDestruct (is_allocator_pre_post_crash with "Halloc_mem") as %Hpost_crash.
    iSplitL "Hpre_inode HPinode".
    { iExists _; iFrame.
      iSplitL "Hpre_inode".
      { iNamed "Hpre_inode".
        iApply inode_linv_to_cinv; auto. }
      iNamed "HPinode". iFrame.
    }
    iFrame "∗ %".
    iSplitL "Halloc_mem HPalloc Hunused".
    { iExists _. iFrame "∗ %". }
    iNamed "Hs_inv". iFrame.
  Qed.

  Theorem is_single_inode_alloc k γdur γbuf l (sz: Z) σ :
    (1 ≤ sz < 2^64)%Z →
    pre_s_inode γdur γbuf l sz σ ={⊤}=∗
    is_single_inode γdur γbuf l sz k ∗
    <disc> |C={⊤}_(S k)=> ∃ σ', s_inode_cinv γdur γbuf sz σ' false.
  Proof.
    iIntros (?); iNamed 1.
    iNamed "Hinode".
    iNamed "Halloc".
    iMod (is_allocator_alloc _ _ _ k with "Hunused HPalloc Halloc_mem") as (γalloc) "[Halloc Halloc_crash]".
    iMod (is_inode_alloc inodeN (k:=k) with "HPinode Hpre_inode") as "[Hinode Hinode_crash]".
    (* TODO: allocate s_inode_inv invariant *)
    iMod (ncinv_alloc s_inodeN _ (∃ σ, s_inode_inv δdur δbuf σ ∗ P γdur γbuf σ)%I
            with "[Hs_inv HP]") as "(#Hinv&Hinv_crash)".
    { iNext.
      iExists _; iFrame. }
    rewrite Halloc_dom.
    iModIntro.
    iSplitL "Halloc Hinode".
    { iExists _, _, _, _, _, _. iFrame "Hinode". iFrame "Halloc".
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
    iSplitL "Hinode".
    { iDestruct "Hinode" as (?) "(?&H)". iExists _. iFrame. iNamed "H".
      iFrame. }
    { iNamed "Hs_inv". iFrame. }
  Qed.

  Theorem wpc_SingleInode__Read {k} (Q: option Block → iProp Σ) γdur γbuf l sz k' (i: u64) :
    (S k < k')%nat →
    {{{ "#Hinode" ∷ is_single_inode γdur γbuf l sz k' ∗
        "Hfupd" ∷ ∀ blks, inode_mapsto γbuf blks ={⊤ ∖ ↑N}=∗ inode_mapsto γbuf blks ∗ Q (blks !! int.nat i)
    }}}
      SingleInode__Read #l #i @ (S k); ⊤
    {{{ (s:Slice.t) mb, RET (slice_val s);
        match mb with
        | None => ⌜s = Slice.nil⌝
        | Some b => (∃ q, is_block s q b)
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
    wpc_apply (wpc_Inode__Read inodeN (k':=k')).
    { lia. }
    iFrame "Hinode". iSplit; first iFromCache. clear.
    iIntros "!>" (σ mb) "[ -> >HPinode]".
    iInv "Hinv" as "Hinner".
    iDestruct "Hinner" as ([durable_blocks buffered_blocks]) "[>Hsinv >HP]".
    iNamed "HP".
    simpl.
    iMod fupd_mask_subseteq as "HcloseM"; last
      iMod ("Hfupd" with "Hfm_all_blocks") as "(Hcurr&HQ)".
    { solve_ndisj. }
    rewrite {2}/s_inode_inv. iNamed "Hsinv".
    iNamed "HPinode". simpl.
    iDestruct (ghost_var_agree with "Hδdurable_blocks Hown_dur_blocks") as %->.
    iDestruct (ghost_var_agree with "Hδbuffered_blocks Hown_buf_blocks") as %->.
    iMod "HcloseM" as "_".
    iModIntro.
    iFrame.
    iSplitR "HΦ HQ".
    { iNext. iExists {| s_inode.durable_blocks := inode.durable_blocks σ;
                        s_inode.buffered_blocks := inode.buffered_blocks σ; |}.
      iFrame. }
    iModIntro. iSplit.
    - crash_case; auto.
    - iIntros (s) "Hb".
      iApply "HΦ"; iFrame.  done.
  Qed.

  (* If you have the full inode_mapsto (or rather, can get it by a view-shift, then
     you know the exact results of your read, compare with wp_Read_fupd_triple for disk *)

  Theorem wpc_SingleInode__Read1 {k} (Q: option Block → iProp Σ) E γdur γbuf l sz k' (i: u64) :
    (S k < k')%nat →
    {{{ "#Hinode" ∷ is_single_inode γdur γbuf l sz k' ∗
        "Hfupd" ∷ |={⊤∖↑N, E}=> ∃ blks, inode_mapsto γbuf blks ∗
                                (inode_mapsto γbuf blks -∗ |={E, ⊤∖↑N}=> Q (blks !! int.nat i))
    }}}
      SingleInode__Read #l #i @ (S k); ⊤
    {{{ (s:Slice.t) mb, RET (slice_val s);
        match mb with
        | None => ⌜s = Slice.nil⌝
        | Some b => (∃ q, is_block s q b)
        end ∗ Q mb }}}
    {{{ True }}}.
  Proof.
    iIntros (? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
    wpc_apply (wpc_SingleInode__Read Q with "[$Hinode Hfupd]"); try eassumption.
    { iIntros (blks) "Hpts". iMod "Hfupd" as (blks') "(Hpts'&Hclo)".
      iDestruct (inode_mapsto_agree with "[$] [$]") as %->.
      iMod ("Hclo" with "[$]"). iFrame. eauto.
    }
    eauto.
  Qed.

  (* If you have only a lower bound inode_mapsto (or rather, can get it by a view-shift), then
     you know the exact results of your read. One can prove a corresponding thing for if the read
     is out of bounds, saying that you can get either nothing or something (and then a new lb *)

  Theorem wpc_SingleInode__Read2 {k} (Q: Block → iProp Σ) E γdur γbuf l sz k' (i: u64) :
    (S k < k')%nat →
    {{{ "#Hinode" ∷ is_single_inode γdur γbuf l sz k' ∗
        "Hfupd" ∷ |={⊤∖↑N, E}=> ∃ blks b, ⌜ blks !! int.nat i = Some b ⌝ ∧ inode_current_lb γbuf blks
                                 ∗ |={E, ⊤∖↑N}=> Q b
    }}}
      SingleInode__Read #l #i @ (S k); ⊤
    {{{ (s:Slice.t) b, RET (slice_val s); (∃ q, is_block s q b) ∗ Q b }}}
    {{{ True }}}.
  Proof.
    iIntros (? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
    wpc_apply (wpc_SingleInode__Read (λ mb, match mb with None => False | Some b => Q b end)%I
                 with "[$Hinode Hfupd]"); try eassumption.
    { iIntros (blks) "Hpts". iMod "Hfupd" as (blks' b Hlookup') "(Hpts'&Hclo)".
      iDestruct (inode_mapsto_lb_agree with "[$] [$]") as %Hprefix.
      iMod ("Hclo"). iFrame. iModIntro.
      eapply prefix_lookup in Hlookup'; last eassumption.
      rewrite Hlookup'. iFrame.
    }
    iSplit.
    - by iLeft in "HΦ".
    - iNext. iRight in "HΦ".
      iIntros (? []).
      * iApply "HΦ".
      * iIntros "(?&[])".
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

  (* FIXME: in case of failure, the resources put into "Hfupd" are lost! *)
  Theorem wpc_SingleInode__Append {k} (Q Qc: iProp Σ) γdur γbuf q l sz b_s b0 k' :
    (S k < k')%nat →
    {{{ "Hinode" ∷ is_single_inode γdur γbuf l sz k' ∗
        "Hb" ∷ is_block b_s q b0 ∗
        "Hfupd" ∷ (<disc> ▷ Qc ∧ ∀ blks, inode_mapsto γbuf blks ={⊤ ∖ ↑N}=∗
                                inode_mapsto γbuf (blks ++ [b0]) ∗ (<disc> ▷ Qc ∧ Q))
    }}}
      SingleInode__Append #l (slice_val b_s) @ (S k); ⊤
    {{{ (ok: bool), RET #ok; if ok then Q else emp }}}
    {{{ Qc }}}.
  Proof.
    iIntros (? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
    iCache with "HΦ Hfupd".
    { iLeft in "HΦ". iLeft in "Hfupd". iModIntro. iNext. by iApply "HΦ". }
    rewrite /SingleInode__Append. wpc_pures.
    iCache with "HΦ Hfupd".
    { iLeft in "HΦ". iLeft in "Hfupd". iModIntro. iNext. by iApply "HΦ". }
    wpc_pures.
    iNamed "Hinode". iNamed "Hro_state".
    wpc_loadField.
    wpc_apply (wpc_Inode__Append inodeN q (k' := k'));
      [lia|].
    iFrame "Hb Hinode".
    iSplit.
    - iLeft in "HΦ". iLeft in "Hfupd". iModIntro. by iApply "HΦ".
    - iSplit.
      { (* Failure case. *) iApply "HΦ". done. }
      iNext.
      iIntros (σ σ' Heq1 Heq2) ">HPinode".
      iNamed "HPinode".
      iInv "Hinv" as ([σ0]) "[>Hinner >HP]" "Hclose".
      iNamed "Hinner".
      iDestruct (ghost_var_agree with "Hδdurable_blocks Hown_dur_blocks") as %?; simplify_eq/=.
      iDestruct (ghost_var_agree with "Hδbuffered_blocks Hown_buf_blocks") as %?; simplify_eq/=.
      iMod (ghost_var_update_halves (σ.(inode.buffered_blocks) ++ [b0])
              with "Hδbuffered_blocks Hown_buf_blocks") as "[Hδbuffered_blocks Hown_buf_blocks]".
      iNamed "HP".
      iMod fupd_mask_subseteq as "HcloseM"; (* adjust mask *)
        last iMod ("Hfupd" with "[$Hfm_all_blocks]") as "[Hfm_all_blocks HQ]".
      { solve_ndisj. }
      iMod "HcloseM" as "_".
      simpl. iMod ("Hclose" with "[Hδdurable_blocks Hδbuffered_blocks Hfm_all_blocks Hfm_dur_blocks]") as "_".
      { iNext. iExists {| s_inode.durable_blocks := inode.durable_blocks σ;
                          s_inode.buffered_blocks := inode.buffered_blocks σ ++ [b0]; |}.
        iFrame. rewrite /= assoc. iFrame. }
      iModIntro.
      iFrame.
      rewrite /Palloc.
      iSplit.
      * iLeft in "HΦ". iLeft in "HQ". iModIntro. by iApply "HΦ".
      * iApply "HΦ". by iRight in "HQ".
  Qed.

  Theorem wpc_SingleInode__Append1 {k} (Q Qc: iProp Σ) E γdur γbuf q l sz b_s b0 k' :
    (S k < k')%nat →
    {{{ "Hinode" ∷ is_single_inode γdur γbuf l sz k' ∗
        "Hb" ∷ is_block b_s q b0 ∗
        "Hfupd" ∷ (<disc> ▷ Qc ∧ |={⊤ ∖ ↑N, E}=> ∃ blks, inode_mapsto γbuf blks ∗
                                  (inode_mapsto γbuf (blks ++ [b0]) ={E, ⊤ ∖ ↑N}=∗ <disc> ▷ Qc ∧ Q))
    }}}
      SingleInode__Append #l (slice_val b_s) @ (S k); ⊤
    {{{ (ok: bool), RET #ok; if ok then Q else emp }}}
    {{{ Qc }}}.
  Proof.
    iIntros (? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
    wpc_apply (wpc_SingleInode__Append Q Qc with "[$Hinode Hfupd $Hb]"); try eassumption.
    { iSplit.
      { by iLeft in "Hfupd". }
      iRight in "Hfupd".
      iIntros (blks) "Hpts". iMod "Hfupd" as (blks') "(Hpts'&Hclo)".
      iDestruct (inode_mapsto_agree with "[$] [$]") as %->.
      iMod (inode_mapsto_append with "Hpts' Hpts") as "($&?)".
      iMod ("Hclo" with "[$]"). iModIntro; eauto.
    }
    eauto.
  Qed.

  Theorem wpc_SingleInode__Flush {k} (Q Qc: iProp Σ) γdur γbuf l sz k' :
    (S k < k')%nat →
    {{{ "Hinode" ∷ is_single_inode γdur γbuf l sz k' ∗
        "Hfupd" ∷ (<disc> ▷ Qc ∧ ∀ blks, inode_mapsto γbuf blks ∗ fmlist γdur 1 blks ={⊤ ∖ ↑N}=∗
                                inode_mapsto γbuf blks ∗ fmlist γdur 1 blks ∗ (<disc> ▷ Qc ∧ Q))
    }}}
      SingleInode__Flush #l @ (S k); ⊤
    {{{ (ok: bool), RET #ok; if ok then Q else emp }}}
    {{{ Qc }}}.
  Proof.
    iIntros (? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
    iCache with "HΦ Hfupd".
    { iLeft in "HΦ". iLeft in "Hfupd". iModIntro. iNext. by iApply "HΦ". }
    rewrite /SingleInode__Flush. wpc_pures.
    iCache with "HΦ Hfupd".
    { iLeft in "HΦ". iLeft in "Hfupd". iModIntro. iNext. by iApply "HΦ". }
    iNamed "Hinode". iNamed "Hro_state".
    wpc_loadField. wpc_loadField.
    wpc_apply (wpc_Inode__Flush inodeN allocN (n:=k') (k':=k'));
      [lia|lia|solve_ndisj|..].
    iFrame "Hinode Halloc".
    iSplit; [ | iSplit; [ | iSplit ] ].
    - iApply reserve_fupd_Palloc.
    - iApply free_fupd_Palloc.
    - iLeft in "Hfupd". iLeft in "HΦ". iModIntro. by iApply "HΦ".
    - iIntros (σ).
      remember σ.(inode.buffered_blocks) as blks eqn:Heqblocks.
      iInduction blks as [| b blks] "IH" forall (σ Heqblocks).
      { iSplit.
        * iLeft in "Hfupd". iLeft in "HΦ". iModIntro. iNext. by iApply "HΦ".
        * iRight in "Hfupd".
          iSplit.
          ** by iApply "HΦ".
          ** iIntros ">HPinode". iNamed "HPinode".
             iInv "Hinv" as ([durable_blks buffered_blks]) "[>Hinner >HP]" "Hclose".
             iNamed "Hinner".
             simpl.
             rewrite -Heqblocks.
             iDestruct (ghost_var_agree with "Hδdurable_blocks Hown_dur_blocks") as %->.
             iDestruct (ghost_var_agree with "Hδbuffered_blocks Hown_buf_blocks") as %->.
             iNamed "HP". simpl. rewrite app_nil_r.
             iMod fupd_mask_subseteq as "HcloseM";
               last iMod ("Hfupd" with "[$]") as "(Hfm_all_blocks&Hfm_dur_blocks&Hfupd)".
             { solve_ndisj. }
             iMod "HcloseM" as "_".
             iMod ("Hclose" with "[Hδdurable_blocks Hδbuffered_blocks Hfm_all_blocks Hfm_dur_blocks]").
             { iNext. iExists {| s_inode.buffered_blocks := [];
                                 s_inode.durable_blocks := σ.(inode.durable_blocks)
                              |}. iFrame. simpl. rewrite app_nil_r. iFrame.
             }
             iModIntro.
             iSplitL "Hused1 Hown_dur_blocks Hown_buf_blocks".
             { iNext. rewrite /Pinode. rewrite Heqblocks. iFrame. }
             iSplit.
             { iLeft in "Hfupd".
               iLeft in "HΦ". iModIntro. iNext. by iApply "HΦ".
             }
             iRight in "HΦ". iRight in "Hfupd". by iApply "HΦ".
      }
      simpl.
      iSplit.
      { iLeft in "Hfupd".
        iLeft in "HΦ". iModIntro. iNext. by iApply "HΦ". }
      iNext.
      iSplit.
      { iRight in "HΦ". by iApply "HΦ". }
      iIntros (addr' Hwf s Hlookup) "(>HPinode&>HPalloc)".
      iNamed "HPinode".
      rewrite -Heqblocks.
      iInv "Hinv" as ([durable_blks buffered_blks]) "[>Hinner >HP]" "Hclose".
      iNamed "Hinner".
      iNamed "HP". simpl.
      iDestruct (ghost_var_agree with "Hδdurable_blocks Hown_dur_blocks") as %->.
      iDestruct (ghost_var_agree with "Hδbuffered_blocks Hown_buf_blocks") as %->.
      iDestruct (ghost_var_agree with "HPalloc Hused1") as %Heq_alloc.
      iMod (ghost_var_update_halves (σ.(inode.durable_blocks) ++ [b])
              with "Hδdurable_blocks Hown_dur_blocks") as "[Hδdurable_blocks Hown_dur_blocks]".
      iMod (ghost_var_update_halves blks
              with "Hδbuffered_blocks Hown_buf_blocks") as "[Hδbuffered_blocks Hown_buf_blocks]".
      iMod (fmlist_update (σ.(inode.durable_blocks) ++ [b]) with "Hfm_dur_blocks") as "(Hfm_dur_blocks&?)"; eauto.
      { econstructor; eauto. }
      rewrite /Pinode.
      simpl.
      iMod (ghost_var_update_halves ({[addr']} ∪ (alloc.used s))
              with "HPalloc Hused1") as "[HPalloc Hused1]".
      iMod ("Hclose" with "[Hδdurable_blocks Hδbuffered_blocks Hfm_all_blocks Hfm_dur_blocks]") as "_".
      { iNext. iExists {| s_inode.buffered_blocks := blks;
                          s_inode.durable_blocks := σ.(inode.durable_blocks) ++ [b]
                       |}. iFrame. simpl. rewrite -app_assoc /=. iFrame.
      }
      iModIntro. iFrame. rewrite /Palloc.
      rewrite alloc_used_insert. rewrite Heq_alloc. iFrame.
      iApply ("IH" with "[] Hfupd HΦ").
      { eauto. }
  Qed.

  Theorem wpc_SingleInode__Flush1 {k} (Q: iProp Σ) γdur γbuf blks l sz k' :
    (S k < k')%nat →
    {{{ "Hinode" ∷ is_single_inode γdur γbuf l sz k' ∗
        "Hlb" ∷ inode_current_lb γbuf blks
    }}}
      SingleInode__Flush #l @ (S k); ⊤
    {{{ (ok: bool), RET #ok; if ok then inode_durable_lb γdur γbuf blks else emp }}}
    {{{ True }}}.
  Proof.
    iIntros (? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
    iDestruct "Hlb" as "#Hlb".
    wpc_apply (wpc_SingleInode__Flush (inode_durable_lb γdur γbuf blks) True with "[$Hinode Hlb]"); try eassumption.
    { iSplit.
      * iModIntro; eauto.
      * iIntros (blks') "(Hcurr&Hdur)".
        iDestruct (inode_mapsto_lb_agree with "[$] [$]") as %Hpre.
        iFrame "Hcurr".
        iMod (fmlist_get_lb with "Hdur") as "($&Hlb')".
        iDestruct (fmlist_lb_mono _ _ _ Hpre with "Hlb'") as "Hlb''".
        iModIntro. iSplit; first by iModIntro.
        iFrame. iApply "Hlb".
    }
    eauto.
  Qed.

End goose.
