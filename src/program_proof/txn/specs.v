From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(*
  TODO: allow representing multiple logical disks with Txn,
    one per logical disk from Wal.
  TODO: how to deal with crashes?  the 3 ghost maps exposed
    by Txn must remain latest, so what represents the old state?
*)

From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.Helpers Require Import GenHeap.

From Goose.github_com.mit_pdos.goose_nfsd Require Import buf txn.
From Perennial.program_proof Require Import wal.specs wal.heapspec.

Record addr := {
  addrBlock : u64;
  addrOff : u64;
}.

Definition inode_bytes := Z.to_nat 128.
Definition inode_buf := vec u8 inode_bytes.
Definition inode_to_vals {ext: ext_op} (i:inode_buf) : list val :=
  fmap b2val (vec_to_list i).

Definition inode_bits : u64 := inode_bytes*8.
Definition block_bits : u64 := block_bytes*8.

Inductive updatable_buf (T : Type) :=
| UB : forall (v : T) (modifiedSinceInstallG : gname), updatable_buf T
.

Arguments UB {T} v modifiedSinceInstallG.

Inductive txnObject :=
| txnBit (b : bool)
| txnInode (i : inode_buf)
| txnBlock (b : Block)
.

Global Instance addr_eq_dec : EqDecision addr.
Proof.
  solve_decision.
Defined.

Global Instance addr_finite : Countable addr.
Proof.
  refine (inj_countable'
            (fun a => (a.(addrBlock), a.(addrOff)))
            (fun '(b, o) => Build_addr b o) _);
    by intros [].
Qed.

Section heap.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!gen_heapPreG u64 heap_block Σ}.
Context `{!gen_heapPreG u64 (updatable_buf Block) Σ}.
Context `{!gen_heapPreG u64 (updatable_buf inode_buf) Σ}.
Context `{!gen_heapPreG u64 (updatable_buf bool) Σ}.
Context `{!gen_heapPreG unit
          (gmap u64 (gmap u64 (updatable_buf bool)) *
           gmap u64 (gmap u64 (updatable_buf inode_buf)) *
           gmap u64 (gmap u64 (updatable_buf Block)))
         Σ}.
Context `{!gen_heapPreG addr txnObject Σ}.
Context `{!inG Σ (authR (optionUR (exclR boolO)))}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Definition lockN : namespace := nroot .@ "txnlock".
Definition invN : namespace := nroot .@ "txninv".
Definition walN : namespace := nroot .@ "txnwal".

Definition extract_nth (b : Block) (elemsize : nat) (n : nat) : option (vec u8 elemsize).
  destruct (decide ((S n) * elemsize <= block_bytes)).
  - refine (Some _).

    assert (elemsize ≤ block_bytes - n * elemsize)%nat by abstract lia.
    refine (Vector.take _ H _).

    unfold Block in b.
    assert (block_bytes = n * elemsize + (block_bytes - n * elemsize))%nat by abstract lia.
    rewrite H0 in b.
    refine (snd (Vector.splitat _ b)).
  - exact None.
Defined.

Definition mapsto_txn {T} hG (off : u64) (v : T) : iProp Σ :=
  ∃ γm,
    mapsto (hG := hG) off 1 (UB v γm) ∗
    own γm (◯ (Excl' true)).

Definition txn_inodes_in_block (installed : Block) (bs : list Block) (gm : gmap u64 (updatable_buf inode_buf)) : iProp Σ :=
  (
    [∗ map] off ↦ maybe_inode ∈ gm,
      match maybe_inode with
      | UB v γm =>
        ⌜ extract_nth (latest_update installed bs) inode_bytes (int.nat off) = Some v ⌝ ∗
        ∃ (modifiedSinceInstall : bool),
          own γm (● (Excl' modifiedSinceInstall)) ∗
          if modifiedSinceInstall then emp
          else
            ⌜ ∀ prefix,
              extract_nth (latest_update installed (take prefix bs)) inode_bytes (int.nat off) = Some v ⌝
      end
  )%I.

Definition txn_bits_in_block (installed : Block) (bs : list Block) (gm : gmap u64 (updatable_buf bool)) : iProp Σ :=
  (
    [∗ map] off ↦ maybe_bit ∈ gm,
      match maybe_bit with
      | UB v γm =>
        (* extract bit off from block; it must be equal to v *)
        True
      end
  )%I.

Definition txn_blocks_in_block (installed : Block) (bs : list Block) (gm : gmap u64 (updatable_buf Block)) : iProp Σ :=
  (
    [∗ map] off ↦ maybe_block ∈ gm,
      match maybe_block with
      | UB v γm =>
        ⌜ latest_update installed bs = v ⌝ ∗
        ∃ (modifiedSinceInstall : bool),
          own γm (● (Excl' modifiedSinceInstall)) ∗
          if modifiedSinceInstall then emp
          else
            ⌜ ∀ prefix,
              latest_update installed (take prefix bs) = v ⌝
      end
  )%I.

Global Instance txn_bits_in_block_timeless installed bs gm : Timeless (txn_bits_in_block installed bs gm).
Proof.
  apply big_sepM_timeless; intros.
  destruct x; refine _.
Qed.

Global Instance txn_inodes_in_block_timeless installed bs gm : Timeless (txn_inodes_in_block installed bs gm).
Proof.
  apply big_sepM_timeless; intros.
  destruct x.
  apply sep_timeless; refine _.
  apply exist_timeless.
  destruct x; refine _.
Qed.

Global Instance txn_blocks_in_block_timeless installed bs gm : Timeless (txn_blocks_in_block installed bs gm).
Proof.
  apply big_sepM_timeless; intros.
  destruct x; refine _.
  apply sep_timeless; refine _.
  apply exist_timeless.
  destruct x; refine _.
Qed.

Definition is_txn_always (walHeap : gen_heapG u64 heap_block Σ)
    (gBits   : gmap u64 (gen_heapG u64 (updatable_buf bool) Σ))
    (gInodes : gmap u64 (gen_heapG u64 (updatable_buf inode_buf) Σ))
    (gBlocks : gmap u64 (gen_heapG u64 (updatable_buf Block) Σ))
    γMaps
    : iProp Σ :=
  (
    ∃ (mBits : gmap u64 (gmap u64 (updatable_buf bool)))
      (mInodes : gmap u64 (gmap u64 (updatable_buf inode_buf)))
      (mBlocks : gmap u64 (gmap u64 (updatable_buf Block))),
      ( [∗ map] blkno ↦ gm;gh ∈ mBits;gBits, gen_heap_ctx (hG := gh) gm ) ∗
      ( [∗ map] blkno ↦ gm;gh ∈ mInodes;gInodes, gen_heap_ctx (hG := gh) gm ) ∗
      ( [∗ map] blkno ↦ gm;gh ∈ mBlocks;gBlocks, gen_heap_ctx (hG := gh) gm ) ∗
      mapsto (hG := γMaps) tt (1/2) (mBits, mInodes, mBlocks) ∗
      ( [∗ map] blkno ↦ bitmap ∈ mBits,
          ∃ installed bs,
            mapsto (hG := walHeap) blkno 1 (HB installed bs) ∗
            txn_bits_in_block installed bs bitmap ) ∗
      ( [∗ map] blkno ↦ inodemap ∈ mInodes,
          ∃ installed bs,
            mapsto (hG := walHeap) blkno 1 (HB installed bs) ∗
            txn_inodes_in_block installed bs inodemap ) ∗
      ( [∗ map] blkno ↦ blockmap ∈ mBlocks,
          ∃ installed bs theBlock,
            ⌜ blockmap = {[ (0 : u64) := theBlock ]} ⌝ ∗
            mapsto (hG := walHeap) blkno 1 (HB installed bs) ∗
            txn_blocks_in_block installed bs blockmap )
  )%I.

Definition is_txn_locked γMaps : iProp Σ :=
  (
    ∃ (mBits : gmap u64 (gmap u64 (updatable_buf bool)))
      (mInodes : gmap u64 (gmap u64 (updatable_buf inode_buf)))
      (mBlocks : gmap u64 (gmap u64 (updatable_buf Block))),
      mapsto (hG := γMaps) tt (1/2) (mBits, mInodes, mBlocks)
  )%I.

Definition is_txn (l : loc)
    (gBits   : gmap u64 (gen_heapG u64 (updatable_buf bool) Σ))
    (gInodes : gmap u64 (gen_heapG u64 (updatable_buf inode_buf) Σ))
    (gBlocks : gmap u64 (gen_heapG u64 (updatable_buf Block) Σ))
    : iProp Σ :=
  (
    ∃ γMaps γLock (walHeap : gen_heapG u64 heap_block Σ) (mu : loc) (walptr : loc) q,
      l ↦[Txn.S :: "mu"]{q} #mu ∗
      l ↦[Txn.S :: "log"]{q} #walptr ∗
      is_wal walN (wal_heap_inv walHeap) walptr ∗
      inv invN (is_txn_always walHeap gBits gInodes gBlocks γMaps) ∗
      is_lock lockN γLock #mu (is_txn_locked γMaps)
  )%I.

Theorem wp_txn_Load_block l gBits gInodes gBlocks (blk off : u64)
    (hG : gen_heapG u64 (updatable_buf Block) Σ) v :
  {{{ is_txn l gBits gInodes gBlocks ∗
      ⌜gBlocks !! blk = Some hG⌝ ∗
      mapsto_txn hG off v
  }}}
    Txn__Load #l (#blk, (#off, (#(block_bytes*8), #())))%V
  {{{ (buf : Slice.t) vals, RET (slice_val buf);
      is_slice buf u8T 1%Qp vals ∗
      ⌜vals = Block_to_vals v⌝ ∗
      mapsto_txn hG off v
  }}}.
Proof.
  iIntros (Φ) "(Htxn & % & Hstable) HΦ".
  iDestruct "Htxn" as (γMaps γLock walHeap mu walptr q) "(Hl & Hwalptr & #Hwal & #Hinv & #Hlock)".
  iDestruct "Hstable" as (γm) "[Hstable Hmod]".

  wp_call.
  wp_loadField.
  wp_call.

  wp_apply (wp_Walog__ReadMem _ _ (λ mb,
    mapsto off 1 (UB v γm) ∗
    match mb with
    | Some b => own γm (◯ Excl' true) ∗ ⌜ b = v ⌝
    | None => own γm (◯ Excl' false)
    end ∗ ⌜ off = 0 ⌝)%I with "[$Hwal Hstable Hmod]").
  {
    iApply (wal_heap_readmem walN invN with "[Hstable Hmod]").

    iInv invN as ">Hinv_inner" "Hinv_closer".
    iDestruct "Hinv_inner" as (mBits mInodes mBlocks) "(Hctxbits & Hctxinodes & Hctxblocks & Hbigmap & Hbits & Hinodes & Hblocks)".

    iDestruct (big_sepM2_lookup_2_some with "Hctxblocks") as %Hblk; eauto.
    destruct Hblk.

    iDestruct (big_sepM2_lookup_acc with "Hctxblocks") as "[Hctxblock Hctxblocks]"; eauto.
    iDestruct (gen_heap_valid with "Hctxblock Hstable") as %Hblockoff.
    iDestruct ("Hctxblocks" with "Hctxblock") as "Hctxblocks".

    iDestruct (big_sepM_lookup_acc with "Hblocks") as "[Hblock Hblocks]"; eauto.
    iDestruct "Hblock" as (blk_installed blk_bs theBlock) "(% & Hblk & Hinblk)".

    iExists _, _. iFrame.

    iModIntro.
    iIntros (mb) "Hrmq".
    destruct mb; rewrite /=.

    {
      iDestruct "Hrmq" as "[Hrmq %]".

      iDestruct (big_sepM_lookup_acc with "Hinblk") as "[Hinblk Hinblkother]"; eauto.
      iDestruct "Hinblk" as "(% & Hinblk)".
      iDestruct ("Hinblkother" with "[Hinblk]") as "Hinblk".
      { iFrame. done. }

      iDestruct ("Hinv_closer" with "[-Hmod]") as "Hinv_closer".
      {
        iModIntro.
        iExists _, _, _.
        iFrame.
        iApply "Hblocks".
        iExists _, _. iFrame.
        eauto.
      }

      iMod "Hinv_closer".
      iModIntro.
      intuition; subst.
      iFrame.
      apply lookup_singleton_Some in Hblockoff; intuition subst.
      done.
    }

    {
      subst x.
      rewrite /txn_blocks_in_block.
      rewrite big_sepM_singleton.
      apply lookup_singleton_Some in Hblockoff; intuition subst.
      iDestruct "Hinblk" as "[<- Hinblk]".
      iDestruct "Hinblk" as (modSince) "[Hγm Hinblk]".
      iDestruct (ghost_var_agree with "Hγm Hmod") as %->.
      iMod (ghost_var_update _ false with "Hγm Hmod") as "[Hγm Hmod]".

      iDestruct ("Hinv_closer" with "[-Hmod]") as "Hinv_closer".
      {
        iModIntro.
        iExists _, _, _.
        iFrame.
        iApply "Hblocks".
        iExists _, _, _.
        iSplitR; [ done | ].
        iFrame.
        iApply big_sepM_singleton.
        iSplitR; [ done | ].
        iExists _. iFrame. iPureIntro.
        intros.
        rewrite take_nil. auto.
      }

      iMod "Hinv_closer".
      iModIntro.
      iFrame. done.
    }
  }

  iIntros (ok bl) "Hres".
  destruct ok.
  {
    iDestruct ("Hres") as (b) "(Hisblock & Hlatest & (Hown & ->) & ->)".
    wp_pures.
    (* XXX slice reasoning for MkBufLoad *)
    admit.
  }

  {
    iDestruct ("Hres") as "(Hlatest & Hown & ->)".
    wp_pures.

    wp_apply (wp_Walog__ReadInstalled _ _ (λ b, ⌜ b = v ⌝ ∗ mapsto (hG := hG) 0 1 (UB v γm) ∗ own γm (◯ (Excl' true)))%I with "[$Hwal Hlatest Hown]").
    {
      iApply (wal_heap_readinstalled walN invN with "[Hlatest Hown]").

      iInv invN as ">Hinv_inner" "Hinv_closer".
      iDestruct "Hinv_inner" as (mBits mInodes mBlocks) "(Hctxbits & Hctxinodes & Hctxblocks & Hbigmap & Hbits & Hinodes & Hblocks)".

      iDestruct (big_sepM2_lookup_2_some with "Hctxblocks") as %Hblk; eauto.
      destruct Hblk.

      iDestruct (big_sepM2_lookup_acc with "Hctxblocks") as "[Hctxblock Hctxblocks]"; eauto.
      iDestruct (gen_heap_valid with "Hctxblock Hlatest") as %Hblockoff.
      iDestruct ("Hctxblocks" with "Hctxblock") as "Hctxblocks".

      iDestruct (big_sepM_lookup_acc with "Hblocks") as "[Hblock Hblocks]"; eauto.
      iDestruct "Hblock" as (blk_installed blk_bs theBlock) "(% & Hblk & Hinblk)".

      iExists _, _. iFrame "Hblk".

      iModIntro.
      iIntros (b) "Hriq".
      iDestruct "Hriq" as "[Hriq %]".

      subst x.
      rewrite /txn_blocks_in_block.
      rewrite big_sepM_singleton.
      apply lookup_singleton_Some in Hblockoff; intuition subst.
      iDestruct "Hinblk" as "[<- Hinblk]".
      iDestruct "Hinblk" as (modSince) "[Hγm Hinblk]".
      iDestruct (ghost_var_agree with "Hγm Hown") as %->.
      iMod (ghost_var_update _ true with "Hγm Hown") as "[Hγm Hown]".
      iDestruct "Hinblk" as %Hinblk.
      iFrame.

      iDestruct ("Hinv_closer" with "[-]") as "Hinv_closer".
      {
        iModIntro.
        iExists _, _, _.
        iFrame.
        iApply "Hblocks".
        iExists _, _, _.
        iSplitR; [ done | ].
        iFrame.
        iApply big_sepM_singleton.
        iSplitR; [ done | ].
        iExists _. iFrame.
      }

      iMod "Hinv_closer".
      iModIntro.
      iPureIntro.

      apply elem_of_list_lookup_1 in H2.
      destruct H2 as [prefix H2].
      specialize (Hinblk prefix).
      rewrite <- Hinblk; clear Hinblk.
      erewrite latest_update_take_some; eauto.
    }

    iIntros (bslice) "Hres".
    iDestruct "Hres" as (b) "(Hres & -> & Hlatest & Hmod)".
    wp_pures.
    (* more MkBufLoad *)
    admit.
Admitted.

Theorem wp_txn_Load_bit l gBits gInodes gBlocks (blk off : u64)
    (hG : gen_heapG u64 (updatable_buf bool) Σ) v :
  {{{ is_txn l gBits gInodes gBlocks ∗
      ⌜gBits !! blk = Some hG⌝ ∗
      mapsto_txn hG off v
  }}}
    Txn__Load #l (#blk, #off, #1)
  {{{ (buf : Slice.t) b, RET (slice_val buf);
      is_slice buf u8T 1%Qp [b] ∗
      ⌜b = #0 <-> v = false⌝ ∗
      mapsto_txn hG off v
  }}}.
Proof.
Admitted.

Theorem wp_txn_Load_inode l gBits gInodes gBlocks (blk off : u64)
    (hG : gen_heapG u64 (updatable_buf inode_buf) Σ) v :
  {{{ is_txn l gBits gInodes gBlocks ∗
      ⌜gInodes !! blk = Some hG⌝ ∗
      mapsto_txn hG off v
  }}}
    Txn__Load #l (#blk, #off, #(inode_bytes*8))
  {{{ (buf : Slice.t) vals, RET (slice_val buf);
      is_slice buf u8T 1%Qp vals ∗
      ⌜vals = inode_to_vals v⌝ ∗
      mapsto_txn hG off v
  }}}.
Proof.
Admitted.

Definition commit_pre
    (gBits   : gmap u64 (gen_heapG u64 (updatable_buf bool) Σ))
    (gInodes : gmap u64 (gen_heapG u64 (updatable_buf inode_buf) Σ))
    (gBlocks : gmap u64 (gen_heapG u64 (updatable_buf Block) Σ))
    (b : val) : iProp Σ :=
  (
    ∃ (bloc : loc) (blkno off sz : u64) data data_vals,
      ⌜b = #bloc⌝ ∗
      bloc ↦[struct.t buf.Buf.S] (#blkno, #off, #sz, slice_val data) ∗
      is_slice data u8T 1%Qp data_vals ∗
      (
        ( ∃ (hG : gen_heapG u64 (updatable_buf bool) Σ) v,
          ⌜sz=1⌝ ∗
          ⌜gBits !! blkno = Some hG⌝ ∗
          mapsto_txn hG off v ) ∨
        ( ∃ (hG : gen_heapG u64 (updatable_buf inode_buf) Σ) v,
          ⌜sz=inode_bits⌝ ∗
          ⌜gInodes !! blkno = Some hG⌝ ∗
          mapsto_txn hG off v ) ∨
        ( ∃ (hG : gen_heapG u64 (updatable_buf Block) Σ) v,
          ⌜sz=block_bits⌝ ∗
          ⌜gBlocks !! blkno = Some hG⌝ ∗
          mapsto_txn hG off v )
      )
  )%I.

Definition commit_post
    (gBits   : gmap u64 (gen_heapG u64 (updatable_buf bool) Σ))
    (gInodes : gmap u64 (gen_heapG u64 (updatable_buf inode_buf) Σ))
    (gBlocks : gmap u64 (gen_heapG u64 (updatable_buf Block) Σ))
    (b : val) : iProp Σ :=
  (
    ∃ (bloc : loc) (blkno off sz : u64) data data_vals,
      ⌜b = #bloc⌝ ∗
      bloc ↦[struct.t buf.Buf.S] (#blkno, #off, #sz, slice_val data) ∗
      is_slice data u8T 1%Qp data_vals ∗
      (
        ( ∃ (hG : gen_heapG u64 (updatable_buf bool) Σ) v,
          ⌜sz=1⌝ ∗
          ⌜gBits !! blkno = Some hG⌝ ∗
          mapsto_txn hG off v ∗
          ⌜ v = false ∧ data_vals = (#0 :: nil) ∨
            v = true ∧ ∃ x, data_vals = [x] ∧ x ≠ #0 ⌝
          ) ∨
        ( ∃ (hG : gen_heapG u64 (updatable_buf inode_buf) Σ) v,
          ⌜sz=inode_bits⌝ ∗
          ⌜gInodes !! blkno = Some hG⌝ ∗
          mapsto_txn hG off v ∗
          ⌜ inode_to_vals v = data_vals ⌝ ) ∨
        ( ∃ (hG : gen_heapG u64 (updatable_buf Block) Σ) v,
          ⌜sz=block_bits⌝ ∗
          ⌜gBlocks !! blkno = Some hG⌝ ∗
          mapsto_txn hG off v ∗
          ⌜ Block_to_vals v = data_vals ⌝ )
      )
  )%I.

Theorem wp_txn__installBufs l q gBits gInodes gBlocks bufs buflist :
  {{{ is_txn l gBits gInodes gBlocks ∗
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      ( [∗ list] _ ↦ buf ∈ buflist, commit_pre gBits gInodes gBlocks buf )
  }}}
    Txn__installBufs #l (slice_val bufs)
  {{{ (blks : Slice.t), RET (slice_val blks);
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      ( [∗ list] _ ↦ buf ∈ buflist, commit_pre gBits gInodes gBlocks buf )
  }}}.
Proof.
  iIntros (Φ) "(Htxn & Hbufs & Hbufpre) HΦ".

  wp_call.
  wp_apply wp_new_slice. { rewrite /=. intuition. apply has_zero_slice_T. }
  iIntros (blks) "Hblks".

  wp_apply wp_ref_to; [val_ty|].
  iIntros (blks_l) "Hblks_l".

  wp_pures.
  wp_apply wp_NewMap.
  iIntros (bufsByBlock) "HbufsByBlock".

  wp_apply wp_ref_to; [val_ty|].
  iIntros (bufsByBlock_l) "HbufsByBlock_l".

  wp_pures.
  wp_apply wp_forSlice.
Admitted.

Theorem wp_txn__doCommit l q gBits gInodes gBlocks bufs buflist :
  {{{ is_txn l gBits gInodes gBlocks ∗
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      ( [∗ list] _ ↦ buf ∈ buflist, commit_pre gBits gInodes gBlocks buf )
  }}}
    Txn__doCommit #l (slice_val bufs)
  {{{ (commitpos : u64) (ok : bool), RET (#commitpos, #ok);
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      ( [∗ list] _ ↦ buf ∈ buflist, commit_post gBits gInodes gBlocks buf ) }}}.
Proof.
  iIntros (Φ) "(Htxn & Hbufs & Hbufpre) HΦ".
  iDestruct "Htxn" as (γMaps γLock walHeap mu walptr tq) "(Hl & Hwalptr & #Hwal & #Hinv & #Hlock)".

  wp_call.
  wp_loadField.
  wp_apply acquire_spec; eauto.
  iIntros "[Hlocked Htxnlocked]".

  wp_pures.
  

Admitted.

Theorem wp_txn_CommitWait l q gBits gInodes gBlocks bufs buflist (wait : bool) (id : u64) :
  {{{ is_txn l gBits gInodes gBlocks ∗
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      ( [∗ list] _ ↦ buf ∈ buflist, commit_pre gBits gInodes gBlocks buf )
  }}}
    Txn__CommitWait #l (slice_val bufs) #wait #id
  {{{ (ok : bool), RET #ok;
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      ( [∗ list] _ ↦ buf ∈ buflist, commit_post gBits gInodes gBlocks buf ) }}}.
Proof.
  iIntros (Φ) "(Htxn & Hbufs & Hbufpre) HΦ".

  wp_call.
  wp_apply wp_ref_to; [val_ty|].
  iIntros (commit) "Hcommit".
  wp_pures.
  wp_apply wp_slice_len.
  wp_pures.
  rewrite bool_decide_decide.
  destruct (decide (int.val 0 < int.val bufs.(Slice.sz))).
  - wp_pures.
    wp_apply (wp_txn__doCommit with "[$Htxn $Hbufs $Hbufpre]").
    iIntros (commitpos ok) "[Hq Hbufpost]".

    wp_pures.
    destruct ok.
    + wp_pures.
      destruct wait.
      * wp_pures.
        admit.
      * wp_pures.
        iDestruct (struct_mapsto_singleton with "Hcommit") as "Hcommit"; eauto.
        wp_apply (wp_load with "Hcommit"); iIntros "Hcommit".
        iApply "HΦ".
        iFrame.

    + wp_pures.
      wp_apply util_proof.wp_DPrintf.
      wp_pures.
      iDestruct (struct_mapsto_singleton with "Hcommit") as "Hcommit"; eauto.
      wp_apply (wp_store with "Hcommit"); iIntros "Hcommit".
      wp_pures.
      wp_apply (wp_load with "Hcommit"); iIntros "Hcommit".
      iApply "HΦ".
      iFrame.

  - wp_pures.
    wp_apply util_proof.wp_DPrintf.
    wp_pures.
    iDestruct (struct_mapsto_singleton with "Hcommit") as "Hcommit"; eauto.
    wp_apply (wp_load with "Hcommit"); iIntros "Hcommit".
    iApply "HΦ".
    iFrame.

    (* Slice.sz is 0, so buflist must be nil *)
    admit.
Admitted.

Definition unify_heaps_inner
    (gBits    : gmap u64 (gen_heapG u64 (updatable_buf bool) Σ))
    (gInodes  : gmap u64 (gen_heapG u64 (updatable_buf inode_buf) Σ))
    (gBlocks  : gmap u64 (gen_heapG u64 (updatable_buf Block) Σ))
    (gUnified : gmap addr txnObject)
    : iProp Σ :=
  (
    [∗ map] addr ↦ txnObj ∈ gUnified,
      match txnObj with
      | txnBit v =>
        ∃ hG,
          ⌜gBits !! addr.(addrBlock) = Some hG⌝ ∧
          mapsto_txn hG addr.(addrOff) v
      | txnInode v =>
        ∃ hG,
          ⌜gInodes !! addr.(addrBlock) = Some hG⌝ ∧
          mapsto_txn hG addr.(addrOff) v
      | txnBlock v =>
        ∃ hG,
          ⌜gBlocks !! addr.(addrBlock) = Some hG⌝ ∧
          mapsto_txn hG addr.(addrOff) v
      end
  )%I.

Definition unify_heaps
    (gBits    : gmap u64 (gen_heapG u64 (updatable_buf bool) Σ))
    (gInodes  : gmap u64 (gen_heapG u64 (updatable_buf inode_buf) Σ))
    (gBlocks  : gmap u64 (gen_heapG u64 (updatable_buf Block) Σ))
    (γUnified : gen_heapG addr txnObject Σ)
    : iProp Σ :=
  (
    ∃ gUnified,
      gen_heap_ctx (hG := γUnified) gUnified ∗
      unify_heaps_inner gBits gInodes gBlocks gUnified
  )%I.

End heap.
