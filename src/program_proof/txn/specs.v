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
| Latest : forall (v : T), updatable_buf T
| NotModifiedSinceInstall : forall (v : T), updatable_buf T.

Arguments Latest {T} v.
Arguments NotModifiedSinceInstall {T} v.

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

Definition txn_inodes_in_block (installed : Block) (bs : list Block) (gm : gmap u64 (updatable_buf inode_buf)) : iProp Σ :=
  (
    [∗ map] off ↦ maybe_inode ∈ gm,
      ⌜ match maybe_inode with
        | Latest v =>
          extract_nth (latest_update installed bs) inode_bytes (int.nat off) = Some v
        | NotModifiedSinceInstall v =>
          ∀ prefix,
            extract_nth (latest_update installed (take prefix bs)) inode_bytes (int.nat off) = Some v
        end ⌝
  )%I.

Definition txn_bits_in_block (installed : Block) (bs : list Block) (gm : gmap u64 (updatable_buf bool)) : iProp Σ :=
  (
    [∗ map] off ↦ maybe_bit ∈ gm,
      match maybe_bit with
      | Latest v => True
      | NotModifiedSinceInstall v =>
        (* extract bit off from block; it must be equal to v *)
        True
      end
  )%I.

Definition txn_blocks_in_block (installed : Block) (bs : list Block) (gm : gmap u64 (updatable_buf Block)) : iProp Σ :=
  (
    [∗ map] off ↦ maybe_block ∈ gm,
      ⌜ off = (0 : u64) ⌝ ∗
      ⌜ match maybe_block with
        | Latest v =>
          latest_update installed bs = v
        | NotModifiedSinceInstall v =>
          ∀ prefix,
            latest_update installed (take prefix bs) = v
      end ⌝
  )%I.

Global Instance txn_bits_in_block_timeless installed bs gm : Timeless (txn_bits_in_block installed bs gm).
Proof.
  apply big_sepM_timeless; intros.
  destruct x; refine _.
Qed.

Global Instance txn_inodes_in_block_timeless installed bs gm : Timeless (txn_inodes_in_block installed bs gm).
Proof.
  apply big_sepM_timeless; intros.
  destruct x; refine _.
Qed.

Global Instance txn_blocks_in_block_timeless installed bs gm : Timeless (txn_blocks_in_block installed bs gm).
Proof.
  apply big_sepM_timeless; intros.
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
          ∃ installed bs,
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
      mapsto (hG := hG) off 1 (Latest v)
  }}}
    Txn__Load #l (#blk, (#off, (#(block_bytes*8), #())))%V
  {{{ (buf : Slice.t) vals, RET (slice_val buf);
      is_slice buf u8T 1%Qp vals ∗
      ⌜vals = Block_to_vals v⌝ ∗
      mapsto (hG := hG) off 1 (Latest v)
  }}}.
Proof.
  iIntros (Φ) "(Htxn & % & Hstable) HΦ".
  iDestruct "Htxn" as (γMaps γLock walHeap mu walptr q) "(Hl & Hwalptr & #Hwal & #Hinv & #Hlock)".

  wp_call.
  wp_loadField.
  wp_call.

  wp_apply (wp_Walog__ReadMem _ _ (λ mb, match mb with
    | Some b => mapsto (hG := hG) off 1 (Latest v) ∗ ⌜ b = v ⌝
    | None => mapsto (hG := hG) off 1 (NotModifiedSinceInstall v)
    end ∗ ⌜ off = 0 ⌝)%I with "[$Hwal Hstable]").
  {
    iApply (wal_heap_readmem walN invN with "[Hstable]").

    iInv invN as ">Hinv_inner" "Hinv_closer".
    iDestruct "Hinv_inner" as (mBits mInodes mBlocks) "(Hctxbits & Hctxinodes & Hctxblocks & Hbigmap & Hbits & Hinodes & Hblocks)".

    iDestruct (big_sepM2_lookup_2_some with "Hctxblocks") as %Hblk; eauto.
    destruct Hblk.

    iDestruct (big_sepM2_lookup_acc with "Hctxblocks") as "[Hctxblock Hctxblocks]"; eauto.
    iDestruct (gen_heap_valid with "Hctxblock Hstable") as %Hblockoff.
    iDestruct ("Hctxblocks" with "Hctxblock") as "Hctxblocks".

    iDestruct (big_sepM_lookup_acc with "Hblocks") as "[Hblock Hblocks]"; eauto.
    iDestruct "Hblock" as (blk_installed blk_bs) "[Hblk Hinblk]".

    iExists _, _. iFrame.

    iModIntro.
    iIntros (mb) "Hrmq".
    destruct mb; rewrite /=.

    {
      iDestruct "Hrmq" as "[Hrmq %]".
      iDestruct (big_sepM_lookup with "Hinblk") as %Hinblk; eauto.
      iDestruct ("Hinv_closer" with "[-Hstable]") as "Hinv_closer".
      {
        iModIntro.
        iExists _, _, _.
        iFrame.
        iApply "Hblocks".
        iExists _, _. iFrame.
      }

      iMod "Hinv_closer".
      iModIntro.
      intuition; subst.
      iFrame.
      done.
    }

    {
      admit.
    }
  }

  iIntros (ok bl) "Hres".
  destruct ok.
  {
    iDestruct ("Hres") as (b) "(Hisblock & (Hlatest & ->) & ->)".
    wp_pures.
    admit.
  }

  {
    iDestruct ("Hres") as "(Hnotmod & ->)".
    wp_pures.

    wp_apply (wp_Walog__ReadInstalled _ _ (λ b, ⌜ b = v ⌝)%I with "[$Hwal Hnotmod]").
    {
(*
      iApply (wal_heap_readinstalled with "[$Hres]"). }
      iIntros (ok bl0) "Hres".
      iDestruct "Hres" as (b) "[Hisblock [Hblk ->]]".
      wp_pures.
      admit.
*)

      admit.
    }

    iIntros (bslice) "Hres".
    iDestruct "Hres" as (b) "(Hres & ->)".
    wp_pures.
    admit.
  }
Admitted.

Theorem wp_txn_Load_bit l gBits gInodes gBlocks (blk off : u64)
    (hG : gen_heapG u64 (updatable_buf bool) Σ) v :
  {{{ is_txn l gBits gInodes gBlocks ∗
      ⌜gBits !! blk = Some hG⌝ ∗
      mapsto (hG := hG) off 1 (Latest v)
  }}}
    Txn__Load #l (#blk, #off, #1)
  {{{ (buf : Slice.t) b, RET (slice_val buf);
      is_slice buf u8T 1%Qp [b] ∗
      ⌜b = #0 <-> v = false⌝
  }}}.
Proof.
Admitted.

Theorem wp_txn_Load_inode l gBits gInodes gBlocks (blk off : u64)
    (hG : gen_heapG u64 (updatable_buf inode_buf) Σ) v :
  {{{ is_txn l gBits gInodes gBlocks ∗
      ⌜gInodes !! blk = Some hG⌝ ∗
      mapsto (hG := hG) off 1 (Latest v)
  }}}
    Txn__Load #l (#blk, #off, #(inode_bytes*8))
  {{{ (buf : Slice.t) vals, RET (slice_val buf);
      is_slice buf u8T 1%Qp vals ∗
      ⌜vals = inode_to_vals v⌝ }}}.
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
          mapsto (hG := hG) off 1 (Latest v) ) ∨
        ( ∃ (hG : gen_heapG u64 (updatable_buf inode_buf) Σ) v,
          ⌜sz=inode_bits⌝ ∗
          ⌜gInodes !! blkno = Some hG⌝ ∗
          mapsto (hG := hG) off 1 (Latest v) ) ∨
        ( ∃ (hG : gen_heapG u64 (updatable_buf Block) Σ) v,
          ⌜sz=block_bits⌝ ∗
          ⌜gBlocks !! blkno = Some hG⌝ ∗
          mapsto (hG := hG) off 1 (Latest v) )
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
          mapsto (hG := hG) off 1 (Latest v) ∗
          ⌜ v = false ∧ data_vals = (#0 :: nil) ∨
            v = true ∧ ∃ x, data_vals = [x] ∧ x ≠ #0 ⌝
          ) ∨
        ( ∃ (hG : gen_heapG u64 (updatable_buf inode_buf) Σ) v,
          ⌜sz=inode_bits⌝ ∗
          ⌜gInodes !! blkno = Some hG⌝ ∗
          mapsto (hG := hG) off 1 (Latest v) ∗
          ⌜ inode_to_vals v = data_vals ⌝ ) ∨
        ( ∃ (hG : gen_heapG u64 (updatable_buf Block) Σ) v,
          ⌜sz=block_bits⌝ ∗
          ⌜gBlocks !! blkno = Some hG⌝ ∗
          mapsto (hG := hG) off 1 (Latest v) ∗
          ⌜ Block_to_vals v = data_vals ⌝ )
      )
  )%I.

Theorem wp_txn_CommitWait l q gBits gInodes gBlocks bufs buflist :
  {{{ is_txn l gBits gInodes gBlocks ∗
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      ( [∗ list] _ ↦ buf ∈ buflist, commit_pre gBits gInodes gBlocks buf )
  }}}
    Txn__CommitWait #l (slice_val bufs)
  {{{ RET #();
      is_slice bufs (refT (struct.t buf.Buf.S)) q buflist ∗
      ( [∗ list] _ ↦ buf ∈ buflist, commit_post gBits gInodes gBlocks buf ) }}}.
Proof.
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
          mapsto (hG := hG) addr.(addrOff) 1 (Latest v)
      | txnInode v =>
        ∃ hG,
          ⌜gInodes !! addr.(addrBlock) = Some hG⌝ ∧
          mapsto (hG := hG) addr.(addrOff) 1 (Latest v)
      | txnBlock v =>
        ∃ hG,
          ⌜gBlocks !! addr.(addrBlock) = Some hG⌝ ∧
          mapsto (hG := hG) addr.(addrOff) 1 (Latest v)
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
