From RecordUpdate Require Import RecordSet.

From Goose.github_com.mit_pdos.perennial_examples Require Import dir.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import slice.crash_slice.
From Perennial.Helpers Require Import ipm.
From Perennial.program_proof.examples Require Import
     alloc_addrset alloc_crash_proof inode_proof.
From Perennial.goose_lang.lib Require Import typed_slice. (* shadows things, should be last *)

(* extra big_sepL2 lemmas *)
(* TODO: move to big_op.v *)
Section bi.
  Context {PROP: bi}.

  Lemma wlog_assume_pure (φ: Prop) (P Q: PROP) :
    (P -∗ ⌜φ⌝) →
    (Q -∗ ⌜φ⌝) →
    (φ → P ⊣⊢ Q) →
    P ⊣⊢ Q.
  Proof.
    intros HP HQ HPQ.
    iSplit.
    - iIntros "H".
      iDestruct (HP with "H") as %H.
      rewrite HPQ //.
    - iIntros "H".
      iDestruct (HQ with "H") as %H.
      rewrite HPQ //.
  Qed.

  Local Lemma big_sepL_exists_list_aux {A T} n (Φ: nat → A → T → PROP) l :
    ([∗ list] i↦a ∈ l, ∃ (x:T), Φ (n+i) a x) -∗
    ∃ (xs: list T), ⌜length xs = length l⌝ ∧
                    ([∗ list] i ↦ a ∈ l, ∃ (x: T), ⌜xs !! i = Some x⌝ ∧ Φ (n+i) a x).
  Proof.
    iInduction l as [|a l] "IH" forall (n).
    - simpl.
      iIntros "H".
      iExists [].
      eauto.
    - simpl.
      iIntros "[HΦ Hl]".
      iDestruct "HΦ" as (x) "HΦ".
      assert (∀ k, n + S k = S n + k) as Harith by lia.
      setoid_rewrite Harith.
      iDestruct ("IH" with "Hl") as (xs) "Hl".
      iDestruct "Hl" as "[%Hlen Hl]".
      iExists (x::xs); simpl; eauto 10 with iFrame.
  Qed.

  Lemma big_sepL_exists_list {A T} (Φ: nat → A → T → PROP) l :
    ([∗ list] i↦a ∈ l, ∃ (x:T), Φ i a x) -∗
    ∃ (xs: list T), ⌜length xs = length l⌝ ∧
                    ([∗ list] i ↦ a ∈ l, ∃ (x: T), ⌜xs !! i = Some x⌝ ∧ Φ i a x).
  Proof.
    apply (big_sepL_exists_list_aux 0 Φ).
  Qed.

  Context {A B: Type}.
  Implicit Types (Φ: nat → A → B → PROP).

  Lemma big_sepL2_app_equiv Φ l1 l2 l1' l2' :
    length l1 = length l1' →
    ([∗ list] k↦y1;y2 ∈ l1; l1', Φ k y1 y2) ∗
    ([∗ list] k↦y1;y2 ∈ l2; l2', Φ (length l1 + k) y1 y2) ⊣⊢
    ([∗ list] k↦y1;y2 ∈ l1 ++ l2; l1' ++ l2', Φ k y1 y2).
  Proof.
    intros.
    iSplit.
    - iIntros "[H1 H2]".
      iApply (big_sepL2_app with "H1 H2").
    - iIntros "H".
      iDestruct (big_sepL2_app_inv with "H") as "[$ $]"; auto.
  Qed.

  Lemma big_sepL2_delete Φ l1 l2 i x1 x2 :
    l1 !! i = Some x1 →
    l2 !! i = Some x2 →
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢
    Φ i x1 x2 ∗ ([∗ list] k↦y1;y2 ∈ l1;l2, if decide (k = i) then emp else Φ k y1 y2).
  Proof.
    intros.

    apply (wlog_assume_pure (length l1 = length l2)).
    { rewrite big_sepL2_length; auto. }
    { rewrite big_sepL2_length.
      iIntros "[_ $]". }

    intros Hlen.
    rewrite !big_sepL2_to_sepL_1' //.
    rewrite big_sepL_delete; eauto.
    f_equiv.
    - iSplit; iIntros "H"; eauto with iFrame.
      iDestruct "H" as (?) "(%&H)".
      iExactEq "H"; congruence.
    - f_equiv.
      intros k y1.
      destruct (decide (k = i)); subst; eauto.
      iSplit; auto.
  Qed.

  (* this is a general theorem but we use Φ and Φc to suggest that Φc is the
  weaker crash condition for each element in the big_sepL2 *)
  Theorem big_sepL2_lookup_acc_and Φ Φc l1 l2 i x1 x2 :
    (* this is a pure assumption (instead of a persistent implication) because
    that's how big_sepL2_mono is written *)
    (∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → Φ k y1 y2 -∗ Φc k y1 y2) →
    l1 !! i = Some x1 →
    l2 !! i = Some x2 →
    big_sepL2 Φ l1 l2 -∗
    Φ i x1 x2 ∗ ((Φ i x1 x2 -∗ big_sepL2 Φ l1 l2) ∧ (Φc i x1 x2 -∗ big_sepL2 Φc l1 l2)).
  Proof.
    iIntros (Himpl Hx1 Hx2) "H".
    rewrite big_sepL2_delete; eauto.
    iDestruct "H" as "[HΦ Hl]"; iFrame.
    iSplit.
    - iIntros "$"; iFrame.
    - iIntros "HΦ".
      iDestruct (big_sepL2_delete with "[HΦ Hl]") as "H"; eauto.
      iFrame.
      iApply (big_sepL2_mono with "Hl").
      intros; simpl.
      destruct (decide (k = i)); eauto.
  Qed.

  Context `{BiFUpd PROP}.
  Theorem big_sepL2_fupd {E} Φ l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1; l2, |={E}=> Φ k y1 y2) -∗
    |={E}=> [∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2.
  Proof.
    iIntros "H".
    iDestruct (big_sepL2_length with "H") as %Hlen.
    rewrite !big_sepL2_to_sepL_1'; auto.
    iApply big_sepL_fupd.
    iApply (big_sepL_mono with "H").
    iIntros (???) "H".
    iDestruct "H" as (y2) "[% H]".
    iMod "H".
    eauto with iFrame.
  Qed.

End bi.

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
        %[Hincl _]%auth_both_valid.
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
    { rewrite auth_both_valid. split; first done.
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
        %[Hincl _]%auth_both_valid.
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
    { rewrite auth_both_valid. split; first done.
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
                    "%Hinode_len" ∷ ⌜length s_inodes = num_inodes⌝ ∗
                    "Hinodes" ∷ ([∗ list] i↦s_inode ∈ s_inodes,
                   "Hinode_cinv" ∷ inode_cinv (U64 (Z.of_nat i)) s_inode ∗
                    "HPinode" ∷ Pinode γblocks γused i s_inode)) ∗
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

  Theorem init_dir {E} (sz: Z) :
    (5 ≤ sz < 2^64)%Z →
    ([∗ list] i ∈ seq 0 (Z.to_nat sz), (Z.of_nat i) d↦ block0) ={E}=∗
    let σ0 := dir.mk $ gset_to_gmap [] $ set_seq 0 5 in
    dir_cinv sz σ0 true.
  Proof.
    (* TODO: rough plan is to:

       - split disk blocks into first 5 and [5,sz-5)
       - create inode_cinv using init_inode for each of the first 5
       - create allocator free blocks from remainder, prove something about
         remainder's domain being same as [rangeSet num_inodes (sz -
         num_inodes)]
       - allocate ghost variables for each Pinode and Palloc
     *)
    iIntros (Hbound) "Hd".
    replace (Z.to_nat sz) with (5 + (Z.to_nat (sz - 5))) by lia.
    rewrite seq_app big_sepL_app.
    iDestruct "Hd" as "[Hinodes Hfree]".
    iMod (inode_used_alloc _ (gset_to_gmap ∅ $ set_seq 0 5)) as (γused) "[Hinode_used Hallused]".
    iMod (inode_blocks_alloc _ (gset_to_gmap [] $ set_seq 0 5)) as (γblocks) "[Hinode_blocks Hallblocks]".
    iApply big_sepM_const_seq in "Hinode_used".
    iApply big_sepM_const_seq in "Hinode_blocks".
  Abort.

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
      assert (a0 = a2) by congruence; subst.
      iFrame.
      iApply pre_inode_to_cinv; eauto.
    - iDestruct (is_allocator_pre_post_crash with "Halloc_mem") as %?.
      iExists _; iFrame "∗ %".
  Qed.

  Theorem is_dir_alloc {E2} k l (sz: Z) σ :
    (5 ≤ sz < 2^64)%Z →
    ↑allocN ⊆ E2 →
    ↑dirN ⊆ E2 →
    ▷ P σ -∗
    pre_dir l sz σ ={⊤}=∗
    is_dir l sz k ∗
    |C={⊤,E2}_(LVL (Z.to_nat sz + num_inodes + 2 * S (S k)))=>
      ∃ σ', dir_cinv sz σ' false ∗ P σ'.
  Proof.
    iIntros (???) "HP"; iNamed 1.
    iNamed "Hinodes".
    iNamed "Halloc".
    iMod (is_allocator_alloc with "Hunused HPalloc Halloc_mem") as (γalloc) "[Halloc Halloc_crash]".

    (* allocate all the inodes into a list of is_inodes and a cfupd for all the
    crash obligations *)
    iDestruct (big_sepL2_length with "Hinodes") as %Hs_inodes_len.
    iDestruct (big_sepL2_mono with "Hinodes") as "inode_fupds".
    { iIntros (?????) "[Hpre HP]".
      iApply (is_inode_alloc inodeN (k:=k) with "HP Hpre"). }
    cbv beta.
    iMod (big_sepL2_fupd with "inode_fupds") as "Hinodes".
    iDestruct (big_sepL2_sep with "Hinodes") as "[His_inodes Hcfupds]".
    iApply big_sepL2_to_sepL_1 in "His_inodes".
    iApply big_sepL2_to_sepL_2 in "Hcfupds".
    iDestruct (big_sepL_mono with "Hcfupds") as "Hinodes_crash".
    { iIntros (???) "Hpre".
      iDestruct "Hpre" as (s_inode) "(_&Hcfupd)".
      iAccu. }
    iApply cfupd_big_sepL in "Hinodes_crash".
    replace (length s_inodes) with num_inodes by lia.

    iMod (inv_alloc dirN _ (∃ σ, dir_inv γblocks σ ∗ P σ)
         with "[Hd_inv HP]") as "#Hinv".
    { iNext.
      iExists _; iFrame. }
    iDestruct (inv_cfupd1 _ ⊤ with "Hinv") as "Hinv_crash"; auto.
    rewrite Halloc_dom.
    iModIntro.
    iSplitL "Hro_state Halloc His_inodes".
    { iExists _, _, _, _, _; iFrame "# ∗".
      iSplit; first (iPureIntro; congruence).
      iApply (big_sepL_mono with "His_inodes").
      iIntros (???) "H".
      iDestruct "H" as (?) "[_ $]". }
    iMod "Halloc_crash" as "_".
    { rewrite rangeSet_size; try word.
      apply LVL_le.
      lia. }
    iMod "Hinodes_crash" as "_".
    { admit. }
    iMod "Hinv_crash" as "_".
    { admit. }
    { rewrite difference_empty_L.
      solve_ndisj. }
    iModIntro. iNext.
    iIntros "Hdir Hinodes Halloc".
    iDestruct "Hdir" as (σ') "(Hdir_inv&HP)".
    iExists _; iFrame.
    iExists _, _; iFrame.

    (* here's a bit of gymnastics to maneuver big_sepL: *)
    iDestruct (big_sepL_exists_list with "Hinodes") as (s_inodes') "[%Hlen' Hinodes]".
    iApply big_sepL2_to_sepL_1' in "Hinodes"; auto.
    iApply big_sepL2_to_sepL_2 in "Hinodes".
    iExists s_inodes'.

    iSplit; first (iPureIntro; congruence).
    iApply (big_sepL_mono with "Hinodes").
    iIntros (???) "H".
    iDestruct "H" as (s_inode) "(_&$&$)".
    Fail idtac.
  Admitted.

  Opaque struct.t.

  (* TODO: use this to replace list_lookup_lt (it's much easier to remember) *)
  Local Ltac list_elem_as l i x :=
    let H := fresh "H" x "_lookup" in
    destruct (list_lookup_lt _ l i) as [x H];
    [ try solve [ len ]
    | ].

  Tactic Notation "list_elem" constr(l) constr(i) "as" ident(x) :=
    list_elem_as l i x.

  Lemma wpc_openInodes {k E2} (d: loc) s_inodes :
    length s_inodes = num_inodes →
    {{{ ([∗ list] i↦s_inode ∈ s_inodes,
          inode_cinv (U64 (Z.of_nat i)) s_inode)
      }}}
      openInodes #d @ NotStuck; k; ⊤; E2
    {{{ inode_s inode_refs, RET (slice_val inode_s);
        is_slice_small inode_s (struct.ptrT inode.Inode.S) 1 inode_refs ∗
        [∗ list] i↦inode_ref;s_inode ∈ inode_refs;s_inodes,
            pre_inode inode_ref (U64 (Z.of_nat i)) s_inode
    }}}
    {{{ ([∗ list] i↦s_inode ∈ s_inodes,
          inode_cinv (U64 (Z.of_nat i)) s_inode) }}}.
  Proof.
    iIntros (? Φ Φc) "Hinode_cinvs HΦ".
    rewrite /openInodes; wpc_pures.
    { auto. }
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
    set (inodeT:=(struct.t inode.Inode.S)).
    wpc_apply (wpc_forUpto
               (λ n, ∃ (inode_s: Slice.t) (inode_refs: list loc),
                   "Hinodes" ∷ ino_l ↦[slice.T (refT inodeT)] (slice_val inode_s) ∗
                   "Hinode_slice" ∷ is_slice inode_s (struct.ptrT inode.Inode.S) 1 inode_refs ∗
                   "Hpre_inodes" ∷ ([∗ list] i↦inode_ref;s_inode ∈ inode_refs;(take (int.nat n) s_inodes),
                    pre_inode inode_ref i s_inode) ∗
                   "Hinode_cinvs" ∷ ([∗ list] i↦s_inode ∈ (drop (int.nat n) s_inodes),
                                     inode_cinv (int.nat n+i) s_inode)
               )%I
              (λ n,
               "Hpre_inodes" ∷ ([∗ list] i↦s_inode ∈ take (int.nat n) s_inodes,
                                ∃ inode_ref, pre_inode inode_ref i s_inode) ∗
               "Hinode_cinvs" ∷ ([∗ list] i↦s_inode ∈ drop (int.nat n) s_inodes,
                      inode_cinv (int.nat n + i) s_inode)
              )%I
              with "[] [Hinodes $Haddr Hinode_cinvs]").
    { word. }
    { iIntros (i Hbound); iNamed 1.
      iFrame "Hinode_cinvs".
      iDestruct (big_sepL2_to_sepL_2 with "Hpre_inodes") as "Hpre_inodes".
      iApply (big_sepL_mono with "Hpre_inodes").
      iIntros (? ? ?) "Hpre".
      iDestruct "Hpre" as (? ?) "Hpre".
      eauto. }
    { iIntros (n Φ' Φc') "!> (inv&Haddr&%Hbound) HΦ".
      iNamed "inv".
      wpc_pures.
      { crash_case.
        iLeft.
        iFrame.
        admit. (* TODO: re-use earlier proof *) }
      iCache with "HΦ Hpre_inodes Hinode_cinvs".
      { crash_case.
        iLeft.
        iFrame.
        admit. (* TODO: re-use earlier proof *) }
      wpc_bind (load_ty _ _). wpc_frame. wp_load. iNamed 1.
      wpc_bind (inode.Open _ _).
      change (int.val (U64 5)) with (Z.of_nat num_inodes) in Hbound.
      list_elem s_inodes (int.nat n) as s_inode.
      rewrite [drop (int.nat n) s_inodes](drop_S _ s_inode); last by auto.
      iDestruct (big_sepL_cons with "Hinode_cinvs") as "[Hs_inode Hinode_cinvs]".
      wpc_apply (inode_proof.wpc_Open with "[Hs_inode]").
      { replace (U64 $ int.nat n + 0) with n by word.
        iFrame. }
      iSplit.
      { iIntros "Hs_inode".
        iDestruct (big_sepL_cons (λ k y, inode_cinv (int.nat n + k) y) with "[Hs_inode $Hinode_cinvs]") as "Hinode_cinvs".
        { replace (U64 $ int.nat n + 0) with n by word.
          iFrame. }
        iFromCache. }
      iIntros "!>" (inode_ref) "Hpre_inode".
      wpc_frame "HΦ Hpre_inode Hpre_inodes Hinode_cinvs".
      { crash_case.
        iLeft.
        iFrame.
        iSplitL "Hpre_inodes".
        { admit. (* TODO: re-use earlier proof *) }
        iApply pre_inode_to_cinv.
        iExactEq "Hpre_inode".
        f_equal; word.
      }
      wp_load.
      wp_apply (wp_SliceAppend' with "Hinode_slice").
      iIntros (inode_s') "Hinode_slice".
      wp_store.
      iNamed 1.
      iRight in "HΦ"; iApply "HΦ".
      iFrame.
      iExists _, _; iFrame.
      iDestruct (big_sepL2_length with "Hpre_inodes") as %Hlens;
          autorewrite with len in Hlens.
      replace (int.nat (word.add n 1%Z)) with (S (int.nat n)); last first.
      { unfold num_inodes in Hbound; word. }
      iSplitR "Hinode_cinvs".
      - erewrite take_S_r by eauto.
        iApply (big_sepL2_app with "Hpre_inodes").
        simpl.
        rewrite right_id.
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
      rewrite -is_slice_zero.
      rewrite /named //. }
    iSplit.
    { (* loop crash condition implies overall crash condition *)
      iIntros "Hinv".
      iDestruct "Hinv" as (i) "(Hpre&%Hbound')".
      iNamed "Hpre".
      crash_case.
      iEval (rewrite -[l in big_opL _ _ l](take_drop (int.nat i))).
      rewrite big_sepL_app.
      iSplitL "Hpre_inodes".
      - iApply (big_sepL_mono with "Hpre_inodes").
        iIntros (???) "Hpre".
        iDestruct "Hpre" as (?) "Hpre".
        iApply pre_inode_to_cinv; eauto.
      - iApply (big_sepL_mono with "Hinode_cinvs").
        iIntros (???) "Hpre".
        change (int.val (U64 5)) with 5%Z in Hbound'.
        iExactEq "Hpre".
        f_equal; len.
        rewrite H /num_inodes.
        replace (int.nat i `min` 5)%nat with (int.nat i) by lia.
        f_equal. }
    iIntros "!> (Hinv&Haddr)". iNamed "Hinv".
    change (int.val (U64 5)) with 5%Z.
    rewrite -> take_ge by word.
    rewrite -> drop_ge by word.
    wpc_frame_compl "Hinodes".
    { crash_case.
      iApply (pre_inodes_to_cinv with "Hpre_inodes"). }
    wp_load.
    iNamed 1.
    iRight in "HΦ"; iApply "HΦ".
    iFrame.
    iApply (is_slice_to_small with "Hinode_slice").
    Fail idtac.
  Admitted.

  Theorem wpc_inodeUsedBlocks {k E2} inode_s inode_refs s_inodes :
    {{{ "Hinode_s" ∷ is_slice_small inode_s (struct.ptrT inode.Inode.S) 1 inode_refs ∗
        "Hpre_inodes" ∷ [∗ list] i↦inode_ref;s_inode ∈ inode_refs;s_inodes,
                    pre_inode inode_ref i s_inode }}}
      inodeUsedBlocks (slice_val inode_s) @ NotStuck; k; ⊤; E2
    {{{ (addrs_ref:loc) used, RET #addrs_ref;
        "Hused_set" ∷ is_addrset addrs_ref used ∗
        "%Hused_eq" ∷ ⌜used = ⋃ (inode.addrs <$> s_inodes)⌝ ∗
        "Hinode_s" ∷ is_slice_small inode_s (struct.ptrT inode.Inode.S) 1 inode_refs ∗
        "Hpre_inodes" ∷ [∗ list] i↦inode_ref;s_inode ∈ inode_refs;s_inodes,
                  pre_inode inode_ref i s_inode }}}
    {{{ [∗ list] i↦s_inode ∈ s_inodes,
       inode_cinv i s_inode
    }}}.
  Proof.
    iIntros (Φ Φc) "Hpre HΦ"; iNamed "Hpre".
    rewrite /inodeUsedBlocks.
    wpc_pures.
    { iApply (pre_inodes_to_cinv with "Hpre_inodes"). }
    iCache with "HΦ Hpre_inodes".
    { crash_case.
      iApply (pre_inodes_to_cinv with "Hpre_inodes"). }
    wpc_frame_seq.
    wp_apply wp_NewMap.
    iIntros (addrs_ref) "Hused_set".
    iApply is_addrset_from_empty in "Hused_set".
    iNamed 1.
    wpc_pures.
    iDestruct (is_slice_small_sz with "Hinode_s") as %Hinode_ref_len.
    rewrite /list.untype fmap_length in Hinode_ref_len.
    wpc_apply (wpc_forSlice (V:=loc)
                (λ n, "Hpre_inodes" ∷ ([∗ list] i↦inode_ref;s_inode ∈ inode_refs;s_inodes,
                                  pre_inode inode_ref i s_inode) ∗
               "Hused_set" ∷ is_addrset addrs_ref
                  (⋃ (take (int.nat n) (inode.addrs <$> s_inodes))))%I
                ([∗ list] i↦s_inode ∈ s_inodes, inode_cinv i s_inode)%I
             with "[] [] [$Hinode_s $Hpre_inodes $Hused_set]").
    { iIntros "!>" (x) "Hpre"; iNamed "Hpre".
      iApply (pre_inodes_to_cinv with "Hpre_inodes"). }
    { iIntros (i inode_ref) "!>".
      iIntros (Φ' Φc') "(Hpre&%Hbound&%Hlookup) HΦ"; iNamed "Hpre".
      wpc_pures.
      { iApply (pre_inodes_to_cinv with "Hpre_inodes"). }
      iDestruct (big_sepL2_lookup_1_some with "Hpre_inodes") as "%Hs_inode_lookup"; eauto.
      destruct Hs_inode_lookup as [s_inode Hs_inode_lookup].
      iDestruct (big_sepL2_lookup_acc_and _ (λ i inode_ref s_inode, inode_cinv i s_inode) with "Hpre_inodes") as "(Hinode&Hpre_inodes)"; eauto.
      { clear.
        iIntros (k inode_ref s_inode ??) "Hpre".
        iApply pre_inode_to_cinv; eauto. }
      wpc_apply (wpc_Inode__UsedBlocks with "Hinode").
      iSplit.
      { iIntros "Hinode".
        iRight in "Hpre_inodes".
        iSpecialize ("Hpre_inodes" with "Hinode").
        crash_case.
        iApply big_sepL2_to_sepL_2 in "Hpre_inodes".
        iApply (big_sepL_mono with "Hpre_inodes").
        iIntros (???) "Hcinv".
        iDestruct "Hcinv" as (?) "(_&$)". }
      iIntros "!>" (addrs_s addrs) "(Hused_addrs&%Haddrset&Hpre_inode)".
      wpc_frame "HΦ Hpre_inodes Hpre_inode".
      { crash_case.
        iRight in "Hpre_inodes".
        iRight in "Hpre_inode".
        iSpecialize ("Hpre_inodes" with "Hpre_inode").
        iFrame.
        iApply big_sepL2_to_sepL_2 in "Hpre_inodes".
        iApply (big_sepL_mono with "Hpre_inodes").
        iIntros (???) "Hcinv".
        iDestruct "Hcinv" as (?) "(_&$)". }
      iDestruct (is_slice_small_acc with "Hused_addrs") as "(Hused_addrs&Hused_cap)".
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
      replace (int.nat (word.add i 1%Z)) with (S (int.nat i)) by word.
      erewrite take_S_r; last first.
      { rewrite list_lookup_fmap.
        rewrite Hs_inode_lookup //. }
      rewrite union_list_app_L /= right_id_L //. }
    iSplit.
    { iIntros "Hinode_cinv".
      crash_case; auto. }
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
    2: { rewrite insert_delete insert_id //. replace (off) with (off + 0) by lia. done. }
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

  Lemma length_gmap_to_list `{Countable K} `(m: gmap K A) :
    length (map_to_list m) = size m.
  Proof.
    induction m using map_ind.
    - rewrite map_to_list_empty //.
    - rewrite map_to_list_insert /= //.
      rewrite map_size_insert /= //.
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

  Theorem wpc_Open {k E2} (d: loc) (sz: u64) σ0 :
    (5 ≤ int.val sz)%Z →
    {{{ dir_cinv (int.val sz) σ0 true }}}
      Open #d #sz @ NotStuck; LVL k; ⊤; E2
    {{{ l, RET #l; pre_dir l (int.val sz) σ0 }}}
    {{{ dir_cinv (int.val sz) σ0 false }}}.
  Proof using allocG0 crashG0 heapG0 inG0 inG1 Σ.
    iIntros (? Φ Φc) "Hcinv HΦ".
    wpc_call.
    { iApply dir_cinv_post_crash; auto. }
    iNamed "Hcinv".
    iCache with "HΦ Hinodes Halloc Hs_inode".
    { crash_case.
      iApply dir_cinv_post_crash.
      iExists _, _; iFrame. }
    iNamed "Hinodes".
    iDestruct (big_sepL_sep with "Hinodes") as "(Hinode_cinvs&HPinodes)".
    wpc_apply (wpc_openInodes with "Hinode_cinvs"); auto.
    iSplit.
    { iIntros "Hinode_cinvs".
      crash_case.
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
      iDestruct (big_sepL2_length with "Hpre_inodes") as %Hlen.
      iDestruct (big_sepL2_to_sepL_2 with "Hpre_inodes") as "Hpre_inodes".
      iApply (big_sepL_mono with "Hpre_inodes").
      iIntros (???) "Hpre".
      iDestruct "Hpre" as (?) "(?&Hpre)".
      iApply pre_inode_to_cinv; eauto. }
    wpc_pures.
    wpc_apply (wpc_inodeUsedBlocks with "[$Hinode_s $Hpre_inodes]").
    iSplit.
    { iIntros "Hinode_cinvs".
      crash_case.
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
      iSplitL "Hpre_inodes HPinodes".
      - iExists s_inodes; iFrame "∗ %".
        iApply big_sepL_sep; iFrame.
        iDestruct (big_sepL2_to_sepL_2 with "Hpre_inodes") as "Hpre_inodes".
        iApply (big_sepL_mono with "Hpre_inodes").
        iIntros (???) "Hpre".
        iDestruct "Hpre" as (?) "(_&Hpre)".
        iApply pre_inode_to_cinv; eauto.
      - iExists _; iFrame "∗ %". }
    rewrite -wp_fupd.
    wp_apply (wp_newAllocator s_alloc with "Hused_set").
    { word. }
    { word_cleanup.
      rewrite /alloc.domain.
      rewrite σ1.
      f_equal; lia. }
    { congruence. }
    { auto. }
    iIntros (alloc_ref) "Halloc_mem".
    Transparent struct.t.
    wp_apply wp_allocStruct; first val_ty.
    Opaque struct.t.
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
    iSplitL "Hpre_inodes HPinodes".
    { iExists s_inodes; iFrame.
      rewrite big_sepL2_sep; iFrame.
      iAssert ([∗ list] k↦v ∈ inode_refs, emp)%I as "Hinode_refs".
      { iApply big_sepL_emp. done. }
      iDestruct (big_sepL_merge_big_sepL2 with "Hinode_refs HPinodes") as "Hmerge"; eauto.
      iApply (big_sepL2_mono with "Hmerge").
      iIntros (?????) "[_ H]". iFrame.
    }
    iExists _; iFrame "∗ %".
  Qed.

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
    { by iApply "HΦ". }
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
    { by iApply "HΦ". }
    iIntros (s) "Hpost". iApply "HΦ".
    iFrame. done.
  Qed.

  Theorem wpc_Size {k E2} (Q: u64 → iProp Σ) l sz k' (idx: u64):
    (S k < k')%nat →
    int.nat idx < num_inodes →
    {{{ "#Hdir" ∷ is_dir l sz k' ∗
        "Hfupd" ∷ (∀ σ blocks sz,
                      ⌜σ.(dir.inodes) !! int.nat idx = Some blocks ∧
                       int.nat sz = length blocks⌝ -∗
                      ▷ P σ ={⊤ ∖ ↑N}=∗ ▷ P σ ∗ Q sz)
    }}}
      Dir__Size #l #idx @ NotStuck; LVL (S k); ⊤;E2
    {{{ sz, RET #sz; Q sz }}}
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
    (* Now we get to the actual size operation. *)
    iApply wpc_Inode__Size; first done.
    iFrame "Hinode". iSplit.
    { by iApply "HΦ". }
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
    iSplit; by iApply "HΦ".
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

  (* TODO: move to helper file / upstream *)
  Lemma map_size_insert_overwrite `{Countable K} {A} (m: gmap K A) k x :
    is_Some (m !! k) →
    size (<[k := x]> m) = size m.
  Proof.
    induction m using map_ind; intros [x' Hlookup].
    - apply lookup_empty_Some in Hlookup; contradiction.
    - destruct (decide (k = i)); subst.
      + rewrite insert_insert.
        rewrite lookup_insert in Hlookup; inversion Hlookup; subst.
        rewrite !map_size_insert //.
      + rewrite lookup_insert_ne // in Hlookup.
        rewrite insert_commute //.
        rewrite [size (insert i _ m)]map_size_insert //.
        rewrite [size (insert i _ _)]map_size_insert; last first.
        { rewrite lookup_insert_ne //. }
        rewrite IHm //.
        eauto.
  Qed.

  Theorem wpc_Append {k E2} (Q: iProp Σ) l sz b_s b0 k' (idx: u64) :
    (2 + k < k')%nat →
    nroot.@"readonly" ## N →
    int.nat idx < num_inodes →
    {{{ "#Hdir" ∷ is_dir l sz k' ∗
        "Hb" ∷ is_block b_s 1 b0 ∗
        "Hfupd" ∷ (∀ σ blocks,
                      ⌜σ.(dir.inodes) !! int.nat idx = Some blocks⌝ -∗
                      ▷ P σ ={⊤ ∖ ↑N}=∗ ▷ P (dir.mk $ <[ int.nat idx := blocks ++ [b0] ]> σ.(dir.inodes)) ∗ Q)
    }}}
      Dir__Append #l #idx (slice_val b_s) @ NotStuck; LVL (S (S k)); ⊤; E2
    {{{ (ok: bool), RET #ok; if ok then Q else emp }}}
    {{{ True }}}.
  Proof.
    iIntros (?? Hidx Φ Φc) "Hpre HΦ"; iNamed "Hpre".
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
    wpc_bind (struct.loadF _ _ _). wpc_frame. wp_loadField.
    iIntros "Hthings". iNamed "Hthings".
    (* Now we get to the actual append operation. *)
    iApply (wpc_Inode__Append (n:=k') (k':=k') inodeN allocN);
      [lia|lia|solve_ndisj|solve_ndisj|solve_ndisj|..].
    iFrame "Hinode Hb Halloc".
    iSplit; [ | iSplit; [ | iSplit ] ]; try iModIntro.
    - iApply reserve_fupd_Palloc.
    - iApply free_fupd_Palloc.
    - by iApply "HΦ".
    - iSplit.
      { (* Failure case *) iRight in "HΦ". iApply "HΦ". done. }
      iIntros (σ σ' addr' -> Hwf s Hreserved) "(>HPinode&>HPalloc)".
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
      iMod fupd_intro_mask' as "HcloseM"; last (* adjust mask *)
        iMod ("Hfupd" with "[% //] [$HP]") as "[HP HQ]".
      { solve_ndisj. }
      iMod "HcloseM" as "_".
      simpl. iMod ("Hclose" with "[Hγblocks HP]") as "_".
      { iNext. iExists _. iFrame "HP". rewrite /dir_inv /=. iFrame.
        (* Show that the first 5 inodes are still all allocated. *)
        iPureIntro. intros idx' Hidx'. destruct (decide ((int.nat idx) = idx')) as [->|Hne].
        - rewrite lookup_insert. eauto.
        - rewrite lookup_insert_ne //. apply Hdom. done.
      }
      iModIntro.
      iFrame.
      rewrite /Palloc.
      iSplitR "HΦ HQ".
      { iNext. iExists _. iFrame "Hused".
        (* Show that the domain bookeeping worked out. *)
        iPureIntro. split.
        - rewrite map_size_insert_overwrite //.
          eauto.
        - rewrite alloc_used_insert.
          apply alloc_insert_dom; auto.
      }
      iSplit; by iApply "HΦ".
  Qed.

End goose.
