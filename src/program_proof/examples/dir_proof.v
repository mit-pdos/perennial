From RecordUpdate Require Import RecordSet.
From Perennial.Helpers Require Import ipm Map.

From Goose.github_com.mit_pdos.perennial_examples Require Import dir.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import disk_prelude.
From Perennial.goose_lang.lib Require Import slice.crash_slice.
From Perennial.program_proof.examples Require Import
     alloc_addrset alloc_crash_proof inode_proof.
From Perennial.goose_lang.lib Require Import typed_slice. (* shadows things, should be last *)

Module dir.
  Record t :=
    mk { inodes: gmap nat (list Block); }.
  Global Instance _eta : Settable t := settable! mk <inodes>.
  Global Instance _witness : Inhabited t := populate!.
End dir.

(* FIXME: port to [auth_map]; then these instances likely also can disappear. *)
Canonical Structure listLO A := leibnizO (list A).
Canonical Structure gset64O := leibnizO (gset u64).

Local Definition blocksR := authR $ gmapUR nat (exclR $ listLO Block).
Local Definition allocsR := authR $ gmapUR nat (exclR $ gset64O).

Section goose.
  Context `{!heapGS Σ}.
  Context `{!allocG Σ}.
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
  Hint Unfold num_inodes : word.

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
        %[Hincl _]%auth_both_valid_discrete.
    iPureIntro.
    move: Hincl. rewrite singleton_included_l=> -[oblocks []].
    rewrite lookup_fmap fmap_Some_equiv=> -[blocks' [-> ->]].
    rewrite Excl_included leibniz_equiv_iff => -> //.
  Qed.

  Lemma inode_blocks_update {γblocks E} {idx: nat} (blocks1 blocks2: list Block) (allblocks: gmap nat (list Block)):
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

  Lemma inode_blocks_alloc E (allblocks: gmap nat (list Block)):
    ⊢ |={E}=> ∃ γblocks, ([∗ map] idx ↦ blocks ∈ allblocks, inode_blocks γblocks idx blocks) ∗ inode_allblocks γblocks allblocks.
  Proof.
    set allblocksR: gmapUR nat (exclR $ listLO Block) := Excl <$> allblocks.
    iMod (own_alloc (● allblocksR ⋅ ◯ allblocksR)) as (γ) "[Ha Hf]".
    { rewrite auth_both_valid_discrete. split; first done.
      intros i. rewrite /allblocksR lookup_fmap. by destruct (allblocks !! i). }
    iModIntro. iExists γ. iFrame "Ha".
    iInduction allblocks as [|i x m Hnew] "IH" using map_ind.
    { rewrite big_sepM_empty. done. }
    rewrite big_sepM_insert // /allblocksR fmap_insert.
    rewrite (insert_singleton_op (Excl <$> m) i (Excl x: exclR $ listLO Block)); last first.
    { rewrite lookup_fmap Hnew. done. }
    rewrite auth_frag_op. iDestruct "Hf" as "[$ Hf]".
    iApply "IH". done.
  Qed.

  Lemma inode_used_lookup γused (idx: nat) (used: gset u64) (allused: gmap nat (gset u64)):
    inode_used γused idx used -∗
    inode_allused γused allused -∗
    ⌜allused !! idx = Some used⌝.
  Proof.
    iIntros "Hused Hallused".
    iDestruct (own_valid_2 with "Hallused Hused") as
        %[Hincl _]%auth_both_valid_discrete.
    iPureIntro.
    move: Hincl. rewrite singleton_included_l=> -[oused []].
    rewrite lookup_fmap fmap_Some_equiv=> -[used' [-> ->]].
    rewrite Excl_included leibniz_equiv_iff => -> //.
  Qed.

  Lemma inode_used_update {γused E} {idx: nat} (used1 used2: gset u64) (allused: gmap nat (gset u64)):
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

  Lemma inode_used_alloc E (allused: gmap nat (gset u64)):
    ⊢ |={E}=> ∃ γused, ([∗ map] idx ↦ used ∈ allused, inode_used γused idx used) ∗ inode_allused γused allused.
  Proof.
    set allusedR: gmapUR nat (exclR $ gset64O) := Excl <$> allused.
    iMod (own_alloc (● allusedR ⋅ ◯ allusedR)) as (γ) "[Ha Hf]".
    { rewrite auth_both_valid_discrete. split; first done.
      intros i. rewrite /allusedR lookup_fmap. by destruct (allused !! i). }
    iModIntro. iExists γ. iFrame "Ha".
    iInduction allused as [|i x m Hnew] "IH" using map_ind.
    { rewrite big_sepM_empty. done. }
    rewrite big_sepM_insert // /allusedR fmap_insert.
    rewrite (insert_singleton_op (Excl <$> m) i (Excl x: exclR $ gset64O)); last first.
    { rewrite lookup_fmap Hnew. done. }
    rewrite auth_frag_op. iDestruct "Hf" as "[$ Hf]".
    iApply "IH". done.
  Qed.

  (** Protocol invariant for inode library *)
  Local Definition Pinode γblocks γused (ino: nat) (s: inode.t): iProp Σ :=
    "Hownblocks" ∷ inode_blocks γblocks ino s.(inode.blocks) ∗
    "Hused1" ∷ inode_used γused ino s.(inode.addrs).

  (** Protocol invariant for alloc library *)
  Local Definition Palloc γused (s: alloc.t): iProp Σ :=
    ∃ allocs: gmap nat (gset u64), (* per-inode used blocks *)
      "%Halloc_size" ∷ ⌜size allocs = num_inodes⌝ ∗
      "%Hused_global" ∷ ⌜alloc.used s = ⋃ (snd <$> map_to_list allocs)⌝ ∗
      "Hused2" ∷ inode_allused γused allocs.

  (** Our own invariant (added to this is [P dir]) *)
  Definition dir_inv γblocks (dir: dir.t): iProp Σ :=
    "%Hdom" ∷ ⌜ ∀ idx, idx < num_inodes → is_Some (dir.(dir.inodes) !! idx) ⌝ ∗
    "Hγblocks" ∷ inode_allblocks γblocks dir.(dir.inodes).

  (** In-memory state of the directory (persistent) *)
  Definition dir_state (l alloc_l: loc) (inode_refs: list loc) : iProp Σ :=
    ∃ d (inodes_s: Slice.t),
      "#d" ∷ readonly (l ↦[Dir :: "d"] (disk_val d)) ∗
      "#allocator" ∷ readonly (l ↦[Dir :: "allocator"] #alloc_l) ∗
      "#inodes" ∷ readonly (l ↦[Dir :: "inodes"] (slice_val inodes_s)) ∗
      "#inodes_s" ∷ readonly (own_slice_small inodes_s ptrT (DfracOwn 1) (inode_refs))
  .

  (** State of unallocated blocks *)
  Local Definition allocΨ (a: u64): iProp Σ := ∃ b, uint.Z a d↦ b.

  Definition is_dir l (sz: Z) : iProp Σ :=
    ∃ (alloc_ref: loc) (inode_refs: list loc) γalloc γused γblocks,
      "%Hlen" ∷ ⌜length inode_refs = num_inodes⌝ ∗
      "Hro_state" ∷ dir_state l alloc_ref inode_refs ∗
      "#Hinodes" ∷ ([∗ list] i ↦ inode_ref ∈ inode_refs,
        is_inode inodeN inode_ref (Pinode γblocks γused i) (W64 (Z.of_nat i))) ∗
      "#Halloc" ∷ is_allocator (Palloc γused)
        allocΨ allocN alloc_ref (rangeSet num_inodes (sz-num_inodes)) γalloc ∗
      "#Hinv" ∷ ncinv dirN (∃ σ, dir_inv γblocks σ ∗ P σ)
  .

  Definition dir_cinv sz σ (post_crash: bool) : iProp Σ :=
    ∃ γblocks γused,
    "Hinodes" ∷ (∃ s_inodes,
                    "%Hinode_len" ∷ ⌜length s_inodes = num_inodes⌝ ∗
                    "Hinodes" ∷ ([∗ list] i↦s_inode ∈ s_inodes,
                   "Hinode_cinv" ∷ inode_cinv (W64 (Z.of_nat i)) s_inode ∗
                    "HPinode" ∷ Pinode γblocks γused i s_inode)) ∗
    "Halloc" ∷ alloc_crash_cond_no_later (Palloc γused) allocΨ (rangeSet num_inodes (sz-num_inodes)) post_crash ∗
    "Hs_inode" ∷ dir_inv γblocks σ
  .

  Lemma dir_cinv_post_crash sz σ :
    dir_cinv sz σ true -∗ dir_cinv sz σ false.
  Proof.
    iNamed 1.
    iExists _, _; iFrame.
    iApply alloc_crash_cond_no_later_from_post_crash; auto.
  Qed.

  Definition pre_dir l (sz: Z) dir : iProp Σ :=
    ∃ alloc_ref inode_refs γblocks γused,
      "%Hlen" ∷ ⌜length inode_refs = num_inodes⌝ ∗
      "Hro_state" ∷ dir_state l alloc_ref inode_refs ∗
      "Hd_inv" ∷ dir_inv γblocks dir ∗
      "Hinodes" ∷ (∃ s_inodes,
                      [∗ list] i↦inode_ref;s_inode ∈ inode_refs;s_inodes,
                     pre_inode inode_ref (W64 (Z.of_nat i)) s_inode ∗
                  Pinode γblocks γused i s_inode) ∗
      "Halloc" ∷ (∃ s_alloc,
                     "Halloc_mem" ∷ is_allocator_mem_pre alloc_ref s_alloc ∗
                     "%Halloc_dom" ∷ ⌜alloc.domain s_alloc = rangeSet num_inodes (sz-num_inodes)⌝ ∗
                     "Hunused" ∷ ([∗ set] k ∈ alloc.unused s_alloc, allocΨ k) ∗
                     "HPalloc" ∷ Palloc γused s_alloc)
  .

  Theorem big_sepM_const_seq {PROP:bi} {A} start sz (def: A) (Φ: nat → A → PROP) :
    ([∗ map] i↦x ∈ gset_to_gmap def (set_seq start sz), Φ i x) -∗
    ([∗ list] i ∈ seq start sz, Φ i def).
  Proof.
    (iInduction sz as [|sz] "IH" forall (start)).
    - rewrite gset_to_gmap_empty big_sepM_empty /=.
      auto.
    - simpl.
      rewrite gset_to_gmap_union_singleton.
      rewrite big_sepM_insert; last first.
      { apply lookup_gset_to_gmap_None.
        rewrite elem_of_set_seq.
        lia. }
      iIntros "[$ Hm]".
      iApply ("IH" with "Hm").
  Qed.

  (* for compatibility with Coq v8.11 *)
  Lemma seq_S : forall len start, seq start (S len) = seq start len ++ [start + len].
  Proof.
    intros len start.
    change [start + len] with (seq (start + len) 1).
    rewrite <- seq_app.
    rewrite <- plus_n_Sm, <- plus_n_O; reflexivity.
  Qed.

  Theorem init_dir {E} (sz: Z) :
    (num_inodes ≤ sz < 2^64)%Z →
    ([∗ list] i ∈ seqZ 0 sz, i d↦ block0) ={E}=∗
    let σ0 := dir.mk $ gset_to_gmap [] $ set_seq 0 num_inodes in
    dir_cinv sz σ0 true.
  Proof.
    (* Proof outline:
       - split disk blocks into first num_inodes and [num_inodes,sz-num_inodes)
       - create inode_cinv using init_inode for each of the first 5
       - create allocator free blocks from remainder, prove something about
         remainder's domain being same as [rangeSet num_inodes (sz -
         num_inodes)]
       - allocate ghost variables for each Pinode and Palloc
     *)
    iIntros (Hbound) "Hd".
    replace (sz) with ((Z.of_nat num_inodes) + ((sz - Z.of_nat num_inodes)))%Z by lia.
    rewrite -> seqZ_app by lia.
    change (0 + Z.of_nat num_inodes)%Z with (Z.of_nat num_inodes).
    rewrite big_sepL_app.
    iDestruct "Hd" as "[Hinodes Hfree]".

    iMod (inode_used_alloc _ (gset_to_gmap ∅ $ set_seq 0 num_inodes)) as (γused) "[Hinode_used Hallused]".
    iMod (inode_blocks_alloc _ (gset_to_gmap [] $ set_seq 0 num_inodes)) as (γblocks) "[Hinode_blocks Hallblocks]".
    iModIntro.
    iApply big_sepM_const_seq in "Hinode_used".
    iApply big_sepM_const_seq in "Hinode_blocks".

    iExists γblocks, γused; iFrame.
    iSplitL "Hinodes Hinode_blocks Hinode_used".
    {
      iInduction num_inodes as [|n Sn] "IH".
      + iExists []; auto.
      + iAssert (⌜(n <= sz)%Z ∧ (sz < 2^64)%Z⌝)%I as "IHbound"; [iPureIntro; word|].
        rewrite !seq_S.
        rewrite seqZ_S.
        repeat change (0+n) with n.
        change (0+n)%Z with (Z.of_nat n).
        rewrite !big_sepL_app.
        iDestruct "Hinodes" as "[Hrest Hinode]".
        iDestruct "Hinode_blocks" as "[Hrest_blocks Hinode_block]".
        iDestruct "Hinode_used" as "[Hrest_used Hinode_used]".
        iSpecialize ("IH" with "IHbound Hrest Hrest_blocks Hrest_used").
        iDestruct "IH" as (s_inodes) "H"; iNamed "H".

        iExists (s_inodes ++ [(inode.mk ∅ [])]).
        iSplitR.
        ++ iPureIntro. rewrite app_length; simpl. lia.
        ++ rewrite big_sepL_app. iFrame "Hinodes".
           repeat rewrite big_sepL_singleton.
           replace (Z.of_nat n) with (uint.Z (W64 n)) by word.
           rewrite Hinode_len.
           replace (n+0)%nat with n by word.
           replace (Z.of_nat n) with (uint.Z (W64 n)) by word.
           iDestruct (init_inode with "Hinode") as "Hinode".
           iFrame.
    }
    iSplitL "Hfree".
    { pose proof (new_alloc_state_properties num_inodes (sz-num_inodes) ∅ ltac:(set_solver))
        as (Hdom&Hpost_crash&Hused&Hunused).
      iExists (new_alloc_state num_inodes (sz-num_inodes) ∅).
      iSplitR; first eauto.
      iSplitR.
      { replace ((num_inodes + (sz - num_inodes) - Z.of_nat num_inodes)%Z) with ((sz - num_inodes)%Z) by word.
        rewrite /alloc.domain in Hdom; eauto.
      }
      rewrite /Palloc Hused.
      iSplitR.
      + iSplit; iPureIntro; set_unfold; lia.
      + rewrite Hunused difference_empty_L.
        rewrite /rangeSet.
        rewrite big_sepS_list_to_set; last first.
        { apply seq_U64_NoDup; word. }
        rewrite big_sepL_fmap.
        unfold allocΨ.
        iApply (big_sepL_mono with "Hfree").
        iIntros (???) "H".
        iExists _.
        iExactEq "H".
        f_equiv.
        * apply lookup_seqZ in H. word.
        * eauto.
    }

    iPureIntro.
    intros idx Hidx.
    exists [].
    apply lookup_gset_to_gmap_Some; split; auto.
    set_unfold. lia.
  Qed.

  Lemma pre_inodes_to_cinv inode_refs s_inodes :
    ([∗ list] i↦inode_ref;s_inode ∈ inode_refs;s_inodes,
        pre_inode inode_ref i s_inode) -∗
    ([∗ list] i↦s_inode ∈ s_inodes,
        inode_cinv i s_inode).
  Proof.
    iIntros "Hpre".
    iApply big_sepL2_to_sepL_2 in "Hpre".
    iApply (big_sepL_mono with "Hpre").
    iIntros (???) "Hpre".
    iDestruct "Hpre" as (inode_ref) "(?&Hpre)".
    iApply pre_inode_to_cinv; eauto.
  Qed.

  Instance into_disc_pre_inodes s_inodes inode_refs:
    IntoDiscrete ([∗ list] i↦inode_ref;s_inode ∈ inode_refs;s_inodes, pre_inode inode_ref i s_inode)
                 ([∗ list] i↦s_inode ∈ s_inodes, inode_cinv i s_inode).
  Proof.
    rewrite /IntoDiscrete. iIntros "H". iDestruct (pre_inodes_to_cinv with "H") as "H". by iModIntro.
  Qed.

  Lemma pre_dir_to_cinv l sz dir :
    pre_dir l sz dir -∗ dir_cinv sz dir true.
  Proof.
    iNamed 1.
    iDestruct "Hinodes" as (s_inodes) "Hpre_inodes".
    iNamed "Halloc".
    iExists _, _; iFrame.
    iSplitL "Hpre_inodes".
    - iDestruct (big_sepL2_length with "Hpre_inodes") as %Hlen'.
      iExists s_inodes; iFrame.
      iSplit.
      { iPureIntro; congruence. }
      iApply big_sepL2_flip in "Hpre_inodes".
      iApply (big_sepL2_elim_big_sepL with "[] Hpre_inodes"); first auto.
      iIntros "!>" (???????) "[Hpre HP]".
      assert (x = z) by congruence; subst.
      iFrame.
      iApply pre_inode_to_cinv; eauto.
    - iDestruct (is_allocator_pre_post_crash with "Halloc_mem") as %?.
      done.
  Qed.

  Theorem is_dir_alloc l (sz: Z) σ :
    (5 ≤ sz < 2^64)%Z →
    ▷ P σ -∗
    pre_dir l sz σ ={⊤}=∗
    init_cancel (is_dir l sz)
                (∃ σ', dir_cinv sz σ' false ∗ ▷ P σ').
  Proof.
    iIntros (?) "HP"; iNamed 1.
    iNamed "Hinodes".
    iNamed "Halloc".
    iMod (is_allocator_alloc with "Hunused HPalloc Halloc_mem") as "Halloc".

    (* allocate all the inodes into a list of is_inodes and a cfupd for all the
    crash obligations *)
    iDestruct (big_sepL2_length with "Hinodes") as %Hs_inodes_len.
    iDestruct (big_sepL2_mono with "Hinodes") as "inode_fupds".
    { iIntros (?????) "[Hpre HP]".
      iDestruct (is_inode_alloc inodeN with "HP Hpre") as "H".
      iDestruct (bupd_fupd with "H") as "H". iExact "H". }
    cbv beta.
    iMod (big_sepL2_fupd with "inode_fupds") as "Hinodes".
    iDestruct (big_sepL2_init_cancel with "Hinodes") as "Hinodes".
    (*
    iDestruct (big_sepL2_sep with "Hinodes") as "[His_inodes Hcfupds]".
     *)
    (*
    iApply big_sepL2_to_sepL_1 in "Hinodes".
    iApply big_sepL2_to_sepL_1 in "His_inodes".
    iApply big_sepL2_to_sepL_2 in "Hcfupds".
    iDestruct (big_sepL_mono with "Hcfupds") as "Hinodes_crash".
    { iIntros (???) "Hpre".
      iDestruct "Hpre" as (s_inode) "(_&Hcfupd)".
      iAccu. }
    iApply big_sepL_own_disc_fupd in "Hinodes_crash".
    rewrite cfupd_big_sepL.
    replace (length s_inodes) with num_inodes by lia.
    *)

    iMod (ncinv_alloc dirN _ (∃ σ, dir_inv γblocks σ ∗ P σ)
         with "[Hd_inv HP]") as "(#Hinv&Hinv_crash)".
    { iNext.
      iExists _; iFrame. }
    iMod (own_disc_fupd_elim with "Hinv_crash") as "Hinv_crash".
    rewrite Halloc_dom.
    iModIntro.
    (* Combine then use init_cancel wand *)
    iDestruct (init_cancel_sep with "Halloc Hinodes") as "H".

    iApply (init_cancel_cfupd ⊤).
    iApply (init_cancel_fupd ⊤).
    iApply (init_cancel_wand with "H [Hro_state] [Hinv_crash]").
    { iIntros "H". iDestruct "H" as "(H1&Hinodes)".
      iDestruct "H1" as (γ) "Halloc".
      iModIntro. iExists _, _, _, _, _. iFrame.
      iSplit; first eauto.
      iFrame "Hinv".
      iApply big_sepL2_to_sepL_1' in "Hinodes"; eauto.
      iApply (big_sepL_mono with "Hinodes"); eauto.
      iIntros (???) "H". iDestruct "H" as (s_inode) "(_&$)".
    }
    iIntros "(Halloc&Hinodes)".
    iModIntro.
    iMod (cfupd_weaken_mask with "Hinv_crash") as "Hdir"; auto.
    iDestruct "Hdir" as (σ') "(>Hdir_inv&HP)".
    iIntros "Hc". iExists _. iFrame.
    iMod (alloc_crash_cond_strip_later with "Halloc") as "Halloc".
    iModIntro. iFrame.
    (* here's a bit of gymnastics to maneuver the existential in the big_sepL: *)
    iDestruct (big_sepL2_const_sepL_r with "Hinodes") as "(_&Hinodes)".
    iDestruct (big_sepL_exists_list with "Hinodes") as (s_inodes') "[%Hlen' Hinodes]".
    iApply big_sepL2_to_sepL_1' in "Hinodes"; auto.
    iApply big_sepL2_to_sepL_2 in "Hinodes".
    iExists s_inodes'.
    iSplit; first (iPureIntro; congruence).

    iApply (big_sepL_mono with "Hinodes").
    iIntros (???) "H".
    iDestruct "H" as (s_inode) "(_&H)".
    iFrame.
  Qed.

  (* TODO: use this to replace list_lookup_lt (it's much easier to remember) *)
  Local Tactic Notation "list_elem" constr(l) constr(i) "as" simple_intropattern(x) :=
    let H := fresh "H" x "_lookup" in
    let i := lazymatch type of i with
            | nat => i
            | Z => constr:(Z.to_nat i)
            | u64 => constr:(uint.nat i)
            end in
    destruct (list_lookup_lt _ l i) as [x H];
    [ try solve [ len ]
    | ].

  Lemma wpc_openInodes d s_inodes :
    length s_inodes = num_inodes →
    {{{ ([∗ list] i↦s_inode ∈ s_inodes,
          inode_cinv (W64 (Z.of_nat i)) s_inode)
      }}}
      openInodes (disk_val d) @ ⊤
    {{{ inode_s inode_refs, RET (slice_val inode_s);
        own_slice_small inode_s ptrT (DfracOwn 1) inode_refs ∗
        [∗ list] i↦inode_ref;s_inode ∈ inode_refs;s_inodes,
            pre_inode inode_ref (W64 (Z.of_nat i)) s_inode
    }}}
    {{{ ([∗ list] i↦s_inode ∈ s_inodes,
          inode_cinv (W64 (Z.of_nat i)) s_inode) }}}.
  Proof.
    iIntros (? Φ Φc) "Hinode_cinvs HΦ".
    rewrite /openInodes; wpc_pures.
    { iLeft in "HΦ". by iApply "HΦ". }
    iCache with "HΦ Hinode_cinvs".
    { crash_case; auto. }
    wpc_frame_seq.
    wp_apply wp_ref_of_zero.
    { auto. }
    iIntros (ino_l) "Hinodes". iNamed 1.
    wpc_pures.
    wpc_frame_seq.
    wp_apply wp_ref_to.
    { auto. }
    iIntros (addr_ref) "Haddr". iNamed 1.
    wpc_pures.
    set (inodeT:=(struct.t inode.Inode)).
    wpc_apply (wpc_forUpto
               (λ n, ∃ (inode_s: Slice.t) (inode_refs: list loc),
                   "Hinodes" ∷ ino_l ↦[slice.T ptrT] (slice_val inode_s) ∗
                   "Hinode_slice" ∷ own_slice inode_s ptrT (DfracOwn 1) inode_refs ∗
                   "Hpre_inodes" ∷ ([∗ list] i↦inode_ref;s_inode ∈ inode_refs;(take (uint.nat n) s_inodes),
                    pre_inode inode_ref i s_inode) ∗
                   "Hinode_cinvs" ∷ ([∗ list] i↦s_inode ∈ (drop (uint.nat n) s_inodes),
                                     inode_cinv (uint.nat n+i) s_inode)
               )%I
              (λ n,
               "Hpre_inodes" ∷ ([∗ list] i↦s_inode ∈ take (uint.nat n) s_inodes,
                                inode_cinv i s_inode) ∗
               "Hinode_cinvs" ∷ ([∗ list] i↦s_inode ∈ drop (uint.nat n) s_inodes,
                      inode_cinv (uint.nat n + i) s_inode)
              )%I
              with "[] [Hinodes $Haddr Hinode_cinvs]").
    { word. }
    { iIntros (i Hbound); iNamed 1. iFrame. by iApply pre_inodes_to_cinv. }
    { iIntros (n Φ' Φc') "!> (inv&Haddr&%Hbound) HΦ".
      iNamed "inv".
      wpc_pures.
      { crash_case. iLeft. iFrame. by iApply pre_inodes_to_cinv. }
      iCache with "HΦ Hpre_inodes Hinode_cinvs".
      { crash_case. iLeft. iFrame. by iApply pre_inodes_to_cinv. }
      wpc_bind (load_ty _ _). wpc_frame. wp_load. iModIntro. iNamed 1.
      wpc_bind (inode.Open _ _).
      change (uint.Z (W64 5)) with (Z.of_nat num_inodes) in Hbound.
      list_elem s_inodes n as s_inode.
      rewrite [drop (uint.nat n) s_inodes](drop_S _ s_inode); last by auto.
      iDestruct (big_sepL_cons with "Hinode_cinvs") as "[Hs_inode Hinode_cinvs]".
      wpc_apply (inode_proof.wpc_Open with "[Hs_inode]").
      { replace (W64 $ uint.nat n + 0) with n by word.
        iFrame. }
      iSplit.
      { iLeft in "HΦ". iIntros "Hs_inode".
        iDestruct (big_sepL_cons (λ k y, inode_cinv (uint.nat n + k) y) with "[Hs_inode $Hinode_cinvs]") as "Hinode_cinvs".
        { replace (W64 $ uint.nat n + 0) with n by word.
          iFrame. }
        iApply ("HΦ").
        iLeft. iFrame.
        by iApply pre_inodes_to_cinv.
      }
      iIntros "!>" (inode_ref) "Hpre_inode".
      wpc_frame "HΦ Hpre_inode Hpre_inodes Hinode_cinvs".
      { crash_case. iLeft. iApply (pre_inodes_to_cinv) in "Hpre_inodes". iFrame.
        iApply pre_inode_to_cinv. iExactEq "Hpre_inode". f_equal. word. }
      wp_load.
      wp_apply (wp_SliceAppend with "Hinode_slice").
      iIntros (inode_s') "Hinode_slice".
      wp_store. iModIntro.
      iNamed 1.
      iRight in "HΦ"; iApply "HΦ".
      iFrame.
      iDestruct (big_sepL2_length with "Hpre_inodes") as %Hlens;
          autorewrite with len in Hlens.
      replace (uint.nat (word.add n 1%Z)) with (S (uint.nat n)); last first.
      { unfold num_inodes in Hbound; word. }
      iSplitR "Hinode_cinvs".
      - erewrite take_S_r by eauto.
        iApply (big_sepL2_app with "Hpre_inodes").
        simpl. iSplitL; last done.
        iExactEq "Hpre_inode".
        f_equal.
        word.
      - iApply (big_sepL_mono with "Hinode_cinvs").
        iIntros (?? ?) "Hpre".
        iExactEq "Hpre".
        repeat (f_equal; try word). }
    { iExists Slice.nil, [].
      iFrame.
      rewrite big_sepL2_nil.
      rewrite -own_slice_zero.
      rewrite /named //. }
    iSplit.
    { (* loop crash condition implies overall crash condition *)
      iLeft in "HΦ".
      iIntros "Hinv".
      iDestruct "Hinv" as (i) "(Hpre&%Hbound')".
      iNamed "Hpre".
      iApply "HΦ".
      iEval (rewrite -[l in big_opL _ _ l](take_drop (uint.nat i))).
      rewrite big_sepL_app.
      iSplitL "Hpre_inodes".
      - iApply (big_sepL_mono with "Hpre_inodes").
        iIntros (???) "Hpre".
        iDestruct "Hpre" as (?) "Hpre".
        iExists _. iFrame.
      - iApply (big_sepL_mono with "Hinode_cinvs").
        iIntros (???) "Hpre".
        change (uint.Z (W64 5)) with 5%Z in Hbound'.
        iExactEq "Hpre".
        f_equal; len.
        rewrite H /num_inodes.
        replace (uint.nat i `min` 5)%nat with (uint.nat i) by lia.
        f_equal. }
    iIntros "!> (Hinv&Haddr)". iNamed "Hinv".
    change (uint.Z (W64 5)) with 5%Z.
    rewrite -> take_ge by word.
    rewrite -> drop_ge by word.
    wpc_frame_compl "Hinodes".
    { crash_case. iApply pre_inodes_to_cinv. eauto. }
    wp_load. iModIntro.
    iNamed 1.
    iRight in "HΦ"; iApply "HΦ".
    iFrame.
    iApply (own_slice_to_small with "Hinode_slice").
  Qed.

  Theorem wpc_inodeUsedBlocks inode_s inode_refs s_inodes :
    {{{ "Hinode_s" ∷ own_slice_small inode_s ptrT (DfracOwn 1) inode_refs ∗
        "Hpre_inodes" ∷ [∗ list] i↦inode_ref;s_inode ∈ inode_refs;s_inodes,
                    pre_inode inode_ref i s_inode }}}
      inodeUsedBlocks (slice_val inode_s) @ ⊤
    {{{ (addrs_ref:loc) used, RET #addrs_ref;
        "Hused_set" ∷ is_addrset addrs_ref used ∗
        "%Hused_eq" ∷ ⌜used = ⋃ (inode.addrs <$> s_inodes)⌝ ∗
        "Hinode_s" ∷ own_slice_small inode_s ptrT (DfracOwn 1) inode_refs ∗
        "Hpre_inodes" ∷ [∗ list] i↦inode_ref;s_inode ∈ inode_refs;s_inodes,
                  pre_inode inode_ref i s_inode }}}
    {{{ [∗ list] i↦s_inode ∈ s_inodes,
       inode_cinv i s_inode
    }}}.
  Proof.
    iIntros (Φ Φc) "Hpre HΦ"; iNamed "Hpre".
    rewrite /inodeUsedBlocks.
    wpc_pures.
    { iLeft in "HΦ". iApply "HΦ". by iApply pre_inodes_to_cinv. }
    iCache with "HΦ Hpre_inodes".
    { crash_case. by iApply pre_inodes_to_cinv. }
    wpc_frame_seq.
    wp_apply wp_NewMap.
    iIntros (addrs_ref) "Hused_set".
    iApply is_addrset_from_empty in "Hused_set".
    iNamed 1.
    wpc_pures.
    iDestruct (own_slice_small_sz with "Hinode_s") as %Hinode_ref_len.
    wpc_apply (wpc_forSlice (V:=loc)
                (λ n, "Hpre_inodes" ∷ ([∗ list] i↦inode_ref;s_inode ∈ inode_refs;s_inodes,
                                  pre_inode inode_ref i s_inode) ∗
               "Hused_set" ∷ is_addrset addrs_ref
                  (⋃ (take (uint.nat n) (inode.addrs <$> s_inodes))))%I
                ([∗ list] i↦s_inode ∈ s_inodes, inode_cinv i s_inode)%I
             with "[] [] [$Hinode_s $Hpre_inodes $Hused_set]").
    { iIntros "!>" (x) "Hpre"; iNamed "Hpre". iApply pre_inodes_to_cinv. eauto. }
    { iIntros (i inode_ref) "!>".
      iIntros (Φ' Φc') "(Hpre&%Hbound&%Hlookup) HΦ"; iNamed "Hpre".
      wpc_pures.
      { crash_case. by iApply pre_inodes_to_cinv. }
      iDestruct (big_sepL2_lookup_1_some with "Hpre_inodes") as "%Hs_inode_lookup"; eauto.
      destruct Hs_inode_lookup as [s_inode Hs_inode_lookup].
      iDestruct (big_sepL2_lookup_acc_and _ (λ i inode_ref s_inode, inode_cinv i s_inode) with "Hpre_inodes") as "(Hinode&Hpre_inodes)"; eauto.
      { clear.
        iIntros (k inode_ref s_inode ??) "Hpre".
        iApply pre_inode_to_cinv; eauto. }
      wpc_pures.
      { iRight in "Hpre_inodes".
        crash_case.
        iApply pre_inode_to_cinv in "Hinode".
        iSpecialize ("Hpre_inodes" with "Hinode").
        iApply big_sepL2_to_sepL_2 in "Hpre_inodes".
        iApply (big_sepL_mono with "Hpre_inodes").
        iIntros (???) "Hcinv".
        iDestruct "Hcinv" as (?) "(_&$)". }
      wpc_apply (wpc_Inode__UsedBlocks with "Hinode").
      iSplit.
      { iRight in "Hpre_inodes".
        crash_case. iLeft in "HΦ". iIntros. iApply "HΦ".
        iSpecialize ("Hpre_inodes" with "[$]").
        iApply big_sepL2_to_sepL_2 in "Hpre_inodes".
        iApply (big_sepL_mono with "Hpre_inodes").
        iIntros (???) "Hcinv".
        iDestruct "Hcinv" as (?) "(_&$)". }
      iIntros "!>" (addrs_s addrs) "(Hused_addrs&%Haddrset&Hpre_inode)".
      wpc_frame "HΦ Hpre_inodes Hpre_inode".
      {
        iRight in "Hpre_inodes".
        iRight in "Hpre_inode".
        crash_case. iSpecialize ("Hpre_inodes" with "Hpre_inode").
        iFrame.
        iApply big_sepL2_to_sepL_2 in "Hpre_inodes".
        iApply (big_sepL_mono with "Hpre_inodes").
        iIntros (???) "Hcinv".
        iDestruct "Hcinv" as (?) "(_&$)". }
      iDestruct (own_slice_small_acc with "Hused_addrs") as "(Hused_addrs&Hused_cap)".
      wp_apply (wp_SetAdd with "[$Hused_set $Hused_addrs]").
      iIntros "(Hused_set&Hused_addrs)".
      iDestruct ("Hused_cap" with "Hused_addrs") as "Hused_addrs".
      iNamed 1.
      iApply "HΦ".
      iSplitR "Hused_set".
      { iLeft in "Hpre_inodes".
        iApply ("Hpre_inodes" with "(Hpre_inode Hused_addrs)"). }
      rewrite Haddrset.
      iExactEq "Hused_set".
      rewrite /named.
      f_equal.
      replace (uint.nat (word.add i 1%Z)) with (S (uint.nat i)) by word.
      erewrite take_S_r; last first.
      { rewrite list_lookup_fmap.
        rewrite Hs_inode_lookup //. }
      rewrite union_list_app_L /= right_id_L //. }
    iSplit.
    { iLeft in "HΦ". eauto. }
    iIntros "!> (Hinv&Hinode_s)"; iNamed "Hinv".
    wpc_pures.
    iDestruct (big_sepL2_length with "Hpre_inodes") as %Hlens.
    iApply "HΦ"; iFrame.
    rewrite -> take_ge by len; eauto.
  Qed.

  Fixpoint delete_below `(m : gmap nat T) (off : nat) :=
    match off with
    | O => m
    | S off' => delete off' (delete_below m off')
    end.

  Lemma delete_below_insert : forall (off : nat) (pos : nat) `(m : gmap nat T) v,
    off <= pos ->
    delete_below (<[pos:=v]> m) off = <[pos:=v]> (delete_below m off).
  Proof.
    induction off; intros; simpl; eauto.
    rewrite IHoff; last by lia.
    rewrite delete_insert_ne //. lia.
  Qed.

  Lemma delete_below_delete : forall (off : nat) (pos : nat) `(m : gmap nat T),
    off <= pos ->
    delete_below (delete pos m) off = delete pos (delete_below m off).
  Proof.
    induction off; intros; simpl; eauto.
    rewrite IHoff; last by lia.
    rewrite delete_commute //.
  Qed.

  Lemma unify_alloc_inodes_used_helper γused γblocks allocs s_inodes off :
    ([∗ list] i↦s_inode ∈ s_inodes, Pinode γblocks γused (off + i) s_inode) -∗
    inode_allused γused allocs -∗
    ⌜length s_inodes = length (map_to_list (delete_below allocs off)) ->
     ⋃ (map_to_list (delete_below allocs off)).*2 = ⋃ (inode.addrs <$> s_inodes)⌝.
  Proof.
    rewrite /Pinode.
    iIntros "Hinodes Hall".
    iInduction s_inodes as [|] "IH" forall (off).
    { iPureIntro. intros.
      generalize dependent (map_to_list (delete_below allocs off)). intros.
      destruct l; simpl in *; congruence. }
    iDestruct "Hinodes" as "[Ha Hinodes]". iNamed "Ha".
    iDestruct (inode_used_lookup with "Hused1 Hall") as "%".
    replace (allocs) with (<[off := a.(inode.addrs)]> (delete off allocs)) at 2 3.
    2: { rewrite insert_delete //. replace (off) with (off + 0) by lia. done. }
    rewrite delete_below_insert; last by lia.
    rewrite map_to_list_insert.
    2: { rewrite delete_below_delete; last by lia. rewrite lookup_delete //. }
    rewrite ?fmap_cons ?union_list_cons /=.
    iDestruct ("IH" $! (S off) with "[Hinodes] Hall") as "%IH".
    { setoid_rewrite plus_n_Sm. iFrame. }
    rewrite delete_below_delete; last by lia.
    iPureIntro. intros.
    rewrite -IH /=; last by lia. done.
  Qed.

  Lemma unify_alloc_inodes_used γused γblocks s_alloc s_inodes :
    length s_inodes = num_inodes →
    ([∗ list] i↦s_inode ∈ s_inodes, Pinode γblocks γused i s_inode) -∗
    Palloc γused s_alloc -∗
    ⌜alloc.used s_alloc = ⋃ (inode.addrs <$> s_inodes)⌝.
  Proof.
    rewrite /Palloc.
    iIntros (Hlen) "Hinodes". iNamed 1. rewrite Hused_global.
    iDestruct (unify_alloc_inodes_used_helper _ _ _ _ 0 with "Hinodes Hused2") as "%Hhelper".
    iPureIntro. rewrite -Hhelper /=; eauto.
    rewrite length_gmap_to_list.
    congruence.
  Qed.

  Theorem wpc_Open d (sz: u64) σ0 :
    (5 ≤ uint.Z sz)%Z →
    {{{ dir_cinv (uint.Z sz) σ0 true }}}
      Open (disk_val d) #sz @ ⊤
    {{{ l, RET #l; pre_dir l (uint.Z sz) σ0 }}}
    {{{ dir_cinv (uint.Z sz) σ0 false }}}.
  Proof using Type* - P.
    iIntros (? Φ Φc) "Hcinv HΦ".
    wpc_call.
    { iApply dir_cinv_post_crash; auto. }
    { iApply dir_cinv_post_crash; auto. }
    iNamed "Hcinv".
    iCache with "HΦ Hinodes Halloc Hs_inode".
    { crash_case.
      iApply dir_cinv_post_crash.
      iExists _, _; iFrame. }
    wpc_pures.
    iNamed "Hinodes".
    iDestruct (big_sepL_sep with "Hinodes") as "(Hinode_cinvs&HPinodes)".
    wpc_apply (wpc_openInodes with "Hinode_cinvs"); auto.
    iSplit.
    { iLeft in "HΦ". iIntros "Hinode_cinvs".
      iApply "HΦ".
      iApply dir_cinv_post_crash.
      iExists _, _; iFrame.
      iExists _; iFrame "%".
      iApply big_sepL_sep; iFrame. }
    iIntros "!>" (inode_s inode_refs) "(Hinode_s & Hpre_inodes)".
    iCache with "HΦ Hpre_inodes HPinodes Halloc Hs_inode".
    { crash_case.
      iApply dir_cinv_post_crash.
      iExists _, _; iFrame.
      iExists _; iFrame "%".
      iApply big_sepL_sep; iFrame.
      iApply pre_inodes_to_cinv. eauto.
    }
    wpc_pures.
    wpc_apply (wpc_inodeUsedBlocks with "[$Hinode_s $Hpre_inodes]").
    iSplit.
    { iLeft in "HΦ". iIntros "Hinode_cinvs".
      iApply "HΦ".
      iApply dir_cinv_post_crash.
      iExists _, _; iFrame.
      iExists _; iFrame "%".
      iApply big_sepL_sep; iFrame. }
    iIntros "!>" (addrs_ref used); iNamed 1.
    iDestruct "Halloc" as (s_alloc) "Halloc"; iNamed "Halloc".
    iDestruct (unify_alloc_inodes_used with "HPinodes HPalloc") as %Hused; auto.
    wpc_frame "HΦ Hpre_inodes HPinodes HPalloc Hunused Hs_inode".
    { crash_case.
      iApply dir_cinv_post_crash.
      iExists _, _; iFrame.
      iSplitL "Hpre_inodes HPinodes"; last done.
      iExists s_inodes; iFrame "∗ %".
      iApply big_sepL_sep; iFrame.
      iApply pre_inodes_to_cinv. eauto. }
    rewrite -wp_fupd.
    wp_apply (wp_newAllocator s_alloc with "Hused_set").
    { word. }
    { word_cleanup.
      rewrite /alloc.domain.
      rewrite Halloc_dom.
      f_equal; lia. }
    { congruence. }
    { auto. }
    iIntros (alloc_ref) "Halloc_mem".
    wp_apply wp_allocStruct; first val_ty.
    iIntros (inode_ref) "Hinode_fields".
    iDestruct (struct_fields_split with "Hinode_fields") as "(d&allocator&inodes&_)".
    iMod (readonly_alloc_1 with "d") as "#d".
    iMod (readonly_alloc_1 with "allocator") as "#allocator".
    iMod (readonly_alloc_1 with "inodes") as "#inodes".
    iMod (readonly_alloc_1 with "Hinode_s") as "#inode_s".
    iModIntro.
    iNamed 1.
    iApply "HΦ".
    iDestruct (big_sepL2_length with "Hpre_inodes") as %Hlens.
    iExists alloc_ref, inode_refs, _, _; iFrame.
    iSplit.
    { iPureIntro; lia. }
    iSplitR.
    { iExists _, _; iFrame "#". }
    iSplit; last done.
    iExists s_inodes; iFrame.
    rewrite big_sepL2_sep; iFrame.
    iAssert ([∗ list] k↦v ∈ inode_refs, emp)%I as "Hinode_refs".
    { iApply big_sepL_emp. done. }
    iDestruct (big_sepL2_sepL_2 with "Hinode_refs HPinodes") as "Hmerge"; eauto.
    iApply (big_sepL2_mono with "Hmerge").
    iIntros (?????) "[_ H]". iFrame.
  Qed.

  Theorem wpc_Dir__Read (Q: option Block → iProp Σ) l sz (idx: u64) (i: u64) :
    uint.nat idx < num_inodes →
    {{{ "#Hdir" ∷ is_dir l sz ∗
        "Hfupd" ∷ (∀ σ blocks mb,
                      ⌜σ.(dir.inodes) !! uint.nat idx = Some blocks ∧
                       mb = blocks !! uint.nat i⌝ -∗
                      ▷ P σ ={⊤ ∖ ↑N}=∗ ▷ P σ ∗ Q mb)
    }}}
      Dir__Read #l #idx #i @ ⊤
    {{{ (s:Slice.t) mb, RET (slice_val s);
        match mb with
        | None => ⌜s = Slice.nil⌝
        | Some b => is_block s (DfracOwn 1) b
        end ∗ Q mb }}}
    {{{ True }}}.
  Proof.
    iIntros (Hidx Φ Φc) "Hpre HΦ"; iNamed "Hpre".
    wpc_call.
    { crash_case; auto. }
    { crash_case; auto. }
    iCache with "HΦ Hfupd".
    { crash_case; auto. }
    iNamed "Hdir". iNamed "Hro_state".
    edestruct (lookup_lt_is_Some_2 inode_refs) as [inode_ref Hinode_ref].
    { rewrite Hlen. done. }
    iDestruct (big_sepL_lookup _ _ _ _ Hinode_ref with "Hinodes") as "Hinode {Hinodes}".
    wpc_pures.
    wpc_frame_seq.
    wp_loadField.
    iMod (readonly_load with "inodes_s") as (qinodes) "{inodes_s} inodes_s".
    wp_apply (wp_SliceGet _ _ _ _ _ inode_refs with "[$inodes_s //]").
    iIntros "inodes_s Hrest". iNamed "Hrest".
    wpc_pures.
    (* Now we get to the actual read operation. *)
    iApply (wpc_step_strong_mono _ _ _ _ _
         (λ v, (∃ s mb, ⌜ v = slice_val s ⌝ ∗
                match mb with
                | Some b => is_block s (DfracOwn 1) b
                | None => ⌜s = Slice.nil⌝
                end ∗ Q mb))%I _ True with "[-HΦ] [HΦ]"); auto.
    2: { iSplit.
         * iNext. iIntros (?) "H". iDestruct "H" as (??) "(%&?)". subst.
           iModIntro. iRight in "HΦ". by iApply "HΦ".
         * iLeft in "HΦ". iIntros. iModIntro. by iApply "HΦ". }
    iApply (wpc_Inode__Read with "[Hinode]"); first done.
    iSplit; first eauto.
    iIntros "!>" (σI mb) "[%Hmb HPI]". iNamed "HPI".
    iInv dirN as (σD) "[>Hdir HPD]".
    (* We need to learn that this inode exists in σD. *)
    rewrite /dir_inv. iNamed "Hdir".
    destruct (Hdom _ Hidx) as [σI' HσI'].
    iDestruct (inode_blocks_lookup with "Hownblocks Hγblocks") as %Hblock.
    simplify_eq.
    iMod fupd_mask_subseteq as "HcloseM"; (* adjust mask *)
        last iMod ("Hfupd" with "[] HPD") as "[HPD HQ]".
    { solve_ndisj. }
    { iPureIntro. eauto. }
    iMod "HcloseM" as "_". iModIntro. iSplitL "Hγblocks HPD".
    { (* re-establish dir_inv *) eauto 10 with iFrame. }
    iModIntro. iSplitL "Hownblocks Hused1".
    { (* re-establish inode invariant *) rewrite /Pinode. eauto 10 with iFrame. }
    iSplit.
    { eauto. }
    iIntros (s) "Hpost".
    iExists _, _; iSplit; first eauto; iFrame; eauto.
  Qed.

  Theorem wpc_Dir__Size (Q: u64 → iProp Σ) l sz (idx: u64):
    uint.nat idx < num_inodes →
    {{{ "#Hdir" ∷ is_dir l sz ∗
        "Hfupd" ∷ (∀ σ blocks sz,
                      ⌜σ.(dir.inodes) !! uint.nat idx = Some blocks ∧
                       uint.nat sz = length blocks⌝ -∗
                      ▷ P σ ={⊤ ∖ ↑N}=∗ ▷ P σ ∗ Q sz)
    }}}
      Dir__Size #l #idx @ ⊤
    {{{ sz, RET #sz; Q sz }}}
    {{{ True }}}.
  Proof.
    iIntros (Hidx Φ Φc) "Hpre HΦ"; iNamed "Hpre".
    wpc_call.
    { crash_case; auto. }
    { crash_case; auto. }
    iCache with "HΦ Hfupd".
    { crash_case; auto. }
    wpc_pures.
    iNamed "Hdir". iNamed "Hro_state".
    edestruct (lookup_lt_is_Some_2 inode_refs) as [inode_ref Hinode_ref].
    { rewrite Hlen. done. }
    iDestruct (big_sepL_lookup _ _ _ _ Hinode_ref with "Hinodes") as "Hinode {Hinodes}".
    wpc_frame_seq.
    wp_loadField.
    iMod (readonly_load with "inodes_s") as (qinodes) "{inodes_s} inodes_s".
    wp_apply (wp_SliceGet _ _ _ _ _ inode_refs with "[$inodes_s //]").
    iIntros "inodes_s Hrest". iNamed "Hrest".
    wpc_pures.
    (* Now we get to the actual size operation. *)
    iApply (wpc_step_strong_mono _ _ _ _ _
           (λ v, ∃ (sz : u64), ⌜ v = #sz ⌝ ∗ Q sz)%I _ _ with "[-HΦ] [HΦ]"); auto.
    2: { iSplit.
         * iNext. iIntros (?) "H". iDestruct "H" as (?) "(%&?)". subst.
           iModIntro. iRight in "HΦ". by iApply "HΦ".
         * iLeft in "HΦ". iIntros. iModIntro. by iApply "HΦ". }
    iApply (wpc_Inode__Size with "[$Hinode]").
    iSplit; first eauto.
    iIntros "!>" (σI mb) "[%Hmb HPI]". iNamed "HPI".
    iInv dirN as (σD) "[>Hdir HPD]".
    (* We need to learn that this inode exists in σD. *)
    rewrite /dir_inv. iNamed "Hdir".
    destruct (Hdom _ Hidx) as [σI' HσI'].
    iDestruct (inode_blocks_lookup with "Hownblocks Hγblocks") as %Hblock.
    simplify_eq.
    iMod fupd_mask_subseteq as "HcloseM"; (* adjust mask *)
        last iMod ("Hfupd" with "[] HPD") as "[HPD HQ]".
    { solve_ndisj. }
    { iPureIntro. eauto. }
    iMod "HcloseM" as "_". iModIntro. iSplitL "Hγblocks HPD".
    { (* re-establish dir_inv *) eauto 10 with iFrame. }
    iModIntro. iSplitL "Hownblocks Hused1".
    { (* re-establish inode invariant *) rewrite /Pinode. eauto 10 with iFrame. }
    iSplit.
    - eauto.
    - iIntros "_". eauto.
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

  Lemma dir_cinv_crash_true E sz σ :
    dir_cinv sz σ false ={E}=∗ dir_cinv sz σ true.
  Proof.
    iNamed 1. rewrite /dir_cinv.
    iMod (alloc_crash_cond_no_later_crash_true with "[] Halloc").
    {
      iIntros (σ0). rewrite /Palloc/named. rewrite used_revert_reserved.
      iIntros "H". eauto.
    }
    iModIntro. iExists _, _. iFrame.
  Qed.

  Lemma alloc_insert_dom idx (new_addrs old_addrs inode_addrs: gset u64)
        (allocs: gmap nat (gset u64)) :
    old_addrs = ⋃ (snd <$> map_to_list allocs) →
    allocs !! idx = Some inode_addrs →
    new_addrs ∪ old_addrs =
    ⋃ (snd <$> map_to_list (<[idx:=new_addrs ∪ inode_addrs]> allocs)).
  Proof.
    intros -> Hidx.
    revert idx Hidx; induction allocs using map_ind; intros idx Hidx.
    { exfalso. rewrite lookup_empty in Hidx. done. }
    destruct (decide (idx = i)) as [->|Hne].
    - (* Induction reached the updated idx. We bottom out. *)
      rewrite insert_insert. rewrite !map_to_list_insert //.
      rewrite !fmap_cons !union_list_cons /=.
      rewrite lookup_insert in Hidx. simplify_eq/=. set_solver+.
    - (* The updated element is a different one. Recurse. *)
      rewrite insert_commute //. rewrite map_to_list_insert //.
      rewrite map_to_list_insert; last first.
      { rewrite lookup_insert_ne //. }
      rewrite !fmap_cons !union_list_cons /=.
      rewrite -IHallocs; last first.
      { rewrite -Hidx lookup_insert_ne //. }
      set_solver+.
  Qed.

  (* FIXME: in case of failure, the resources put into "Hfupd" are lost! *)
  Theorem wpc_Dir__Append (Q: iProp Σ) l sz b_s b0 (idx: u64) :
    uint.nat idx < num_inodes →
    {{{ "#Hdir" ∷ is_dir l sz ∗
        "Hb" ∷ is_block b_s (DfracOwn 1) b0 ∗
        "Hfupd" ∷ (∀ σ blocks,
                      ⌜σ.(dir.inodes) !! uint.nat idx = Some blocks⌝ -∗
                      ▷ P σ ={⊤ ∖ ↑N}=∗ ▷ P (dir.mk $ <[ uint.nat idx := blocks ++ [b0] ]> σ.(dir.inodes)) ∗ Q)
    }}}
      Dir__Append #l #idx (slice_val b_s) @ ⊤
    {{{ (ok: bool), RET #ok; if ok then Q else emp }}}
    {{{ True }}}.
  Proof.
    iIntros (Hidx Φ Φc) "Hpre HΦ"; iNamed "Hpre".
    wpc_call.
    { crash_case; auto. }
    { crash_case; auto. }
    iCache with "HΦ Hfupd".
    { crash_case; auto. }
    wpc_pures.
    iNamed "Hdir". iNamed "Hro_state".
    edestruct (lookup_lt_is_Some_2 inode_refs) as [inode_ref Hinode_ref].
    { rewrite Hlen. done. }
    iDestruct (big_sepL_lookup _ _ _ _ Hinode_ref with "Hinodes") as "Hinode {Hinodes}".
    wpc_frame_seq.
    wp_loadField.
    iMod (readonly_load with "inodes_s") as (qinodes) "{inodes_s} inodes_s".
    wp_apply (wp_SliceGet _ _ _ _ _ inode_refs with "[$inodes_s //]").
    iIntros "inodes_s Hrest". iNamed "Hrest".
    wpc_pures.
    wpc_loadField.
    (* Now we get to the actual append operation. *)
    iApply (wpc_step_strong_mono _ _ _ _ _
           (λ v, ∃ (ok: bool), ⌜ v = #ok ⌝ ∗ if ok then Q else emp)%I _ _ with "[-HΦ] [HΦ]"); auto.
    2: { iSplit.
         * iNext. iIntros (?) "H". iDestruct "H" as (?) "(%&?)". subst.
           iModIntro. iRight in "HΦ". by iApply "HΦ".
         * iLeft in "HΦ". iIntros. iModIntro. by iApply "HΦ". }
    iApply (wpc_Inode__Append inodeN allocN);
      [solve_ndisj|..].
    iFrame "Hinode Hb Halloc".
    iSplit; [ | iSplit; [ | iSplit ] ].
    - iApply reserve_fupd_Palloc.
    - iApply free_fupd_Palloc.
    - eauto.
    - iSplit.
      { (* Failure case *) iNext. iExists _; iSplit; eauto. }
      iIntros "!>" (σ σ' addr' -> Hwf s Hreserved) "(HPinode&>HPalloc)".
      iEval (rewrite /Palloc) in "HPalloc". iNamed "HPalloc".
      iNamed "HPinode".
      iDestruct (inode_used_lookup with "Hused1 Hused2") as %Heq.
      iInv "Hinv" as ([σ0]) "[>Hinner HP]" "Hclose".
      iNamed "Hinner".
      iMod (inode_used_update _ (union {[addr']} σ.(inode.addrs)) with "Hused1 Hused2") as
          "[Hγused Hused]".
      iDestruct (inode_blocks_lookup with "Hownblocks Hγblocks") as %Heq2.
      simplify_eq/=.
      iMod (inode_blocks_update  _ (σ.(inode.blocks) ++ [b0]) with "Hownblocks Hγblocks") as
          "[Hownblocks Hγblocks]".
      iSpecialize ("Hfupd" $! {| dir.inodes := σ0 |}). rewrite Heq2.
      iMod fupd_mask_subseteq as "HcloseM"; last (* adjust mask *)
        iMod ("Hfupd" with "[% //] [$HP]") as "[HP HQ]".
      { solve_ndisj. }
      iMod "HcloseM" as "_".
      simpl. iMod ("Hclose" with "[Hγblocks HP]") as "_".
      { iNext. iExists _. iFrame "HP". rewrite /dir_inv /=. iFrame.
        (* Show that the first 5 inodes are still all allocated. *)
        iPureIntro. intros idx' Hidx'. destruct (decide ((uint.nat idx) = idx')) as [->|Hne].
        - rewrite lookup_insert. eauto.
        - rewrite lookup_insert_ne //. apply Hdom. done.
      }
      iModIntro.
      iFrame.
      rewrite /Palloc.
      iSplitR "HQ".
      { (* Show that the domain bookeeping worked out. *)
        iPureIntro. split.
        - rewrite map_size_insert_Some //.
        - rewrite alloc_used_insert.
          apply alloc_insert_dom; auto.
      }
      iSplit; eauto.
  Qed.

End goose.

From Perennial.goose_lang Require Import crash_modality recovery_lifting.

Section crash_stable.
  Context `{!heapGS Σ}.
  Context `{!stagedG Σ}.
  Context `{!inG Σ blocksR}.
  Context `{!inG Σ allocsR}.

  Instance allocΨ_crash_stable k:
    IntoCrash (allocΨ k) (λ _, allocΨ k).
  Proof.
    rewrite /IntoCrash. iNamed 1.
    iCrash. iExists _; eauto.
  Qed.

  Instance Palloc_crash_stable γ σ:
    IntoCrash (Palloc γ σ) (λ _, Palloc γ σ).
  Proof. rewrite /IntoCrash. iApply post_crash_nodep. Qed.

  Instance Pinode_crash_stable γblocks γused i s_inode:
    IntoCrash (Pinode γblocks γused i s_inode) (λ _, Pinode γblocks γused i s_inode).
  Proof. rewrite /IntoCrash. iApply post_crash_nodep. Qed.

  Existing Instance inode_cinv_stable.

  Global Instance dir_cinv_crash sz σ0 :
    IntoCrash (dir_cinv sz σ0 false) (λ _, dir_cinv sz σ0 false).
  Proof.
    rewrite /IntoCrash /dir_cinv.
    iNamed 1.
    iNamed "Hinodes".
    rewrite (allocator_crash_cond_no_later_stable (λ _, Palloc γused)).
    rewrite /dir_inv.
    iNamed "Hs_inode".
    rewrite /inode_allblocks.
    iPoseProof (post_crash_nodep with "Hγblocks") as "Hγblocks".
    iCrash.
    iExists _, _. iFrame. done.
  Qed.

End crash_stable.

Section recov.
  Context `{!heapGS Σ}.
  Context `{!allocG Σ}.
  Context `{!stagedG Σ}.
  Context `{!inG Σ blocksR}.
  Context `{!inG Σ allocsR}.

  Set Nested Proofs Allowed.

  (* Just a simple example of using idempotence *)
  Theorem wpr_Open (d: ()) (sz: u64) σ0:
    (5 ≤ uint.Z sz)%Z →
    dir_cinv (uint.Z sz) σ0 true -∗
    wpr NotStuck ⊤
        (Open (disk_val d) #sz)
        (Open (disk_val d) #sz)
        (λ _, True%I)
        (λ _, True%I)
        (λ _ _, True%I).
  Proof using Type*.
    iIntros (Hsz) "Hstart".
    iApply (idempotence_wpr NotStuck ⊤ _ _ (λ _, True)%I (λ _, True)%I (λ _ _, True)%I (λ _, ∃ σ', dir_cinv (uint.Z sz) σ' false)%I with "[Hstart] []").
    { wpc_apply (wpc_Open with "Hstart"); auto 10. }
    iModIntro. iIntros (????) "H".
    iDestruct "H" as (σ'') "Hstart".
    (* TODO(Joe): why does iCrash not work after the iNext? *)
    iNext. rewrite dir_cinv_crash. iRevert "Hstart".
    iApply @post_crash_mono.
    iIntros (?) "Hstart _".
    iSplit; first done.
    iMod (dir_cinv_crash_true with "Hstart") as "Hstart".
    wpc_apply (wpc_Open with "Hstart").
    { eauto. }
    eauto 10.
  Qed.
End recov.
