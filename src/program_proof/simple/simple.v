From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.algebra Require Import deletable_heap liftable.
From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.

From Goose.github_com.mit_pdos.goose_nfsd Require Import simple.
From Perennial.program_proof Require Import txn.txn_proof buftxn.buftxn_proof marshal_proof addr_proof lockmap_proof addr.addr_proof buf.buf_proof.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.Helpers Require Import NamedProps Map List range_set.
From Perennial.program_logic Require Import spec_assert.
From Perennial.goose_lang.lib Require Import slice.typed_slice into_val.

Module simple.
  Definition ino := list u8.
  Definition t := gmap nat ino.
End simple.

Section heap.
Context `{!crashG Σ}.
Context `{!buftxnG Σ}.
Context `{!invG Σ}.
Implicit Types (stk:stuckness) (E: coPset).

Record simple_names := {
  simple_txn : @txn_names Σ;
  simple_src : gen_heapG nat simple.ino Σ;
  simple_lockmapghs : list (gen_heapG u64 bool Σ);
}.

Definition LogSz : nat := 513.
Definition InodeSz : nat := 128.
Definition NumInodes : nat := 4096 / InodeSz.

Definition encodes_inode (len: u64) (blk: u64) data : Prop :=
  has_encoding data (EncUInt64 len :: EncUInt64 blk :: nil).

Definition inum2addr inum := Build_addr LogSz (inum * InodeSz * 8).
Definition blk2addr blk := Build_addr blk 0.

Definition is_inode_enc γ (inum: nat) (len: u64) (blk: u64) : iProp Σ :=
  ∃ (ibuf : defs.inode_buf),
    ⌜ encodes_inode len blk (vec_to_list ibuf) ⌝ ∗
    mapsto_txn γ.(simple_txn) (inum2addr inum) (existT _ (defs.bufInode ibuf)).

Definition is_inode_data γ (len : u64) (blk: u64) (contents: list u8) : iProp Σ :=
  ∃ (bbuf : Block),
    "%Hdiskdata" ∷ ⌜ firstn (length contents) (vec_to_list bbuf) = contents ⌝ ∗
    "%Hdisklen" ∷ ⌜ len = length contents ⌝ ∗
    "Hdiskblk" ∷ mapsto_txn γ.(simple_txn) (blk2addr blk) (existT _ (defs.bufBlock bbuf)).

Definition is_inode_disk γ (inum: nat) (state: simple.ino) : iProp Σ :=
  ∃ (blk: u64),
    is_inode_enc γ inum (length state) blk ∗
    is_inode_data γ (length state) blk state.

Definition is_inode_mem (l: loc) (inum: nat) (len: u64) (blk: u64) : iProp Σ :=
  "Hinum" ∷ l ↦[Inode.S :: "Inum"] #inum ∗
  "Hisize" ∷ l ↦[Inode.S :: "Size"] #len ∗
  "Hidata" ∷ l ↦[Inode.S :: "Data"] #blk.

Theorem wp_inum2Addr inum :
  {{{ ⌜ inum < NumInodes ⌝ }}}
    inum2Addr #inum
  {{{ RET (addr2val (inum2addr inum)); True }}}.
Proof.
  iIntros (Φ) "% HΦ".
  wp_call.
  wp_call.
  rewrite /addr2val /inum2addr /=.
  rewrite /LogSz /InodeSz.
  replace (word.add (word.divu (word.sub 4096 8) 8) 2)%Z with (U64 513) by reflexivity.
  replace (word.mul (word.mul inum 128) 8)%Z with (U64 (inum * 128 * 8)%nat).
  { iApply "HΦ". done. }

  revert H.
  rewrite /NumInodes /InodeSz.
  replace (4096 `div` 128) with (32) by reflexivity.
  intros.
  word_cleanup.
  admit.
Admitted.

Theorem wp_block2addr bn :
  {{{ True }}}
    block2addr #bn
  {{{ RET (addr2val (blk2addr bn)); True }}}.
Proof.
  iIntros (Φ) "% HΦ".
  wp_call.
  wp_call.
  iApply "HΦ". done.
Qed.

Theorem wp_ReadInode γ inum len blk (btxn : loc) bufm :
  {{{ is_buftxn btxn bufm γ.(simple_txn) ∗
      is_inode_enc γ inum len blk ∗
      ⌜ inum < NumInodes ⌝ }}}
    ReadInode #btxn #inum
  {{{ l, RET #l;
      is_inode_enc γ inum len blk ∗
      is_inode_mem l inum len blk }}}.
Proof.
  iIntros (Φ) "(Hbuftxn & Henc & %) HΦ".

  wp_call.
  wp_apply (wp_inum2Addr); auto.
  replace (#(LitInt (word.mul 128 8))) with (#1024%nat) by reflexivity.
  wp_apply (wp_BufTxn__ReadBuf with "[$Hbuftxn]").

  (* Need the [is_inode_enc] to be actually lifted into the buftxn active transaction.
   * Need to solve two problems to get there:
   * - Current buftxn spec just has a gmap, and
   * - [is_inode_enc] is not parameterized by txn/buftxn.
   *)
Admitted.

Definition is_source γ : iProp Σ :=
  ∃ (src: simple.t),
    (* Really we want to say [source_ctx ∗ source_state src] here,
     * but we have not yet defined the [language] for our simple NFS server.. *)
    gen_heap_ctx (hG := γ.(simple_src)) src.

Definition is_inode_stable γ (inum64: u64) : iProp Σ :=
  ∃ (inum: nat) (state: simple.ino),
    ⌜ inum64 = inum ⌝ ∗
    mapsto (hG := γ.(simple_src)) inum 1%Qp state ∗
    is_inode_disk γ inum state.

Definition covered_inodes : gset u64 :=
  rangeSet 2 (NumInodes-2).

Definition is_fs γ (nfs: loc) : iProp Σ :=
  ∃ (txn lm : loc),
    readonly (nfs ↦[Nfs.S :: "t"] #txn) ∗
    readonly (nfs ↦[Nfs.S :: "l"] #lm) ∗
    is_txn txn γ.(simple_txn) ∗
    is_lockMap lm γ.(simple_lockmapghs) covered_inodes (is_inode_stable γ).

Theorem wp_Inode__Read γ ip inum len blk (btxn : loc) (offset : u64) (bytesToRead : u64) bufm contents :
  {{{ is_buftxn btxn bufm γ.(simple_txn) ∗
      is_inode_mem ip inum len blk ∗
      is_inode_data γ len blk contents }}}
    Inode__Read #ip #btxn #offset #bytesToRead
  {{{ resSlice (eof : bool) (vs : list u8), RET (slice_val resSlice, #eof);
      is_slice resSlice u8T 1 vs ∗
      is_buftxn btxn bufm γ.(simple_txn) ∗
      is_inode_mem ip inum len blk ∗
      is_inode_data γ len blk contents ∗
      ⌜ firstn (length vs) (skipn (int.nat offset) contents) = vs ⌝ ∗
      ⌜ eof = true <-> (int.nat offset + length vs ≥ int.nat len)%nat ⌝ }}}.
Proof.
  iIntros (Φ) "(Hbuftxn & Hmem & Hdata) HΦ".
  wp_call.
  iNamed "Hmem".
  wp_loadField.
  wp_if_destruct.
  { wp_pures.
    replace (slice.nil) with (slice_val (Slice.nil)); auto.
    iApply "HΦ".
    iSplitR.
    { iApply (is_slice_zero (V:=u8)). }
    iFrame.
    iPureIntro; intuition.
    simpl. lia.
  }

  wp_apply wp_ref_to; first by val_ty.
  iIntros (count) "Hcount".
  wp_pures.
  wp_loadField. wp_load.
  wp_if_destruct.
  - wp_loadField. wp_store. wp_pures.
    wp_apply util_proof.wp_DPrintf.
    wp_pures.
    wp_apply (wp_NewSlice (V:=u8)).
    iIntros (dataslice) "Hdataslice".
    wp_apply wp_ref_to; first by val_ty.
    iIntros (datavar) "Hdatavar".
    wp_pures.
    wp_loadField.
    wp_apply wp_block2addr.
    iNamed "Hdata".
    wp_apply (wp_BufTxn__ReadBuf _ _ _ _ _ (existT _ (bufBlock bbuf)) with "[$Hbuftxn]").
    { iPureIntro; intuition.
      (* XXX need to get this out of "Hdiskblk" *)
      admit.
    }

    iIntros (bufptr dirty) "[Hbuf Hbufupd]".
    wp_pures.
    wp_load.
    wp_pures.
    wp_apply wp_ref_to; first by val_ty.
    iIntros (b) "Hb".
    wp_pures.

    replace (replicate (int.nat 0%Z) IntoVal_def) with (@nil u8) by reflexivity.

    wp_apply (wp_forUpto (λ i,
      ∃ dataslice vs,
        "Hdatavar" ∷ datavar ↦[slice.T byteT] (slice_val dataslice) ∗
        "Hdataslice" ∷ is_slice dataslice byteT 1 vs ∗
        "%Hcontent" ∷ ⌜ firstn (length vs) (skipn (int.nat offset) contents) = vs ⌝ ∗
        "Hbuf" ∷ is_buf bufptr (blk2addr blk) {|
           bufKind := projT1 (existT KindBlock (bufBlock bbuf));
           bufData := projT2 (existT KindBlock (bufBlock bbuf));
           bufDirty := dirty |}
      )%I with "[] [$Hb Hdatavar Hdataslice Hbuf]").
    { word. }
    {
      iIntros (b').
      iIntros (Φ') "!>".
      iIntros "(HI & Hb & %Hbound) HΦ'".
      iNamed "HI".
      wp_pures.
      wp_load.
      wp_apply (wp_buf_loadField_data with "Hbuf").
      iIntros (vslice) "[Hbufdata Hbufnodata]".
      wp_apply (wp_SliceGet (V:=u8) with "[$Hbufdata]").
      { admit. }
      iIntros "Hbufdata".
      wp_load.
      wp_apply (wp_SliceAppend (V:=u8) with "Hdataslice").
      iIntros (dataslice') "Hdataslice".
      wp_store.
      iApply "HΦ'".
      iFrame "Hb".
      iExists _, _.
      iFrame "Hdatavar".
      iFrame "Hdataslice".
      iSplitR.
      { rewrite app_length /=.
        admit.
      }
      iApply is_buf_return_data. iFrame.
    }
    {
      iExists _, _.
      iFrame.
      rewrite /= //.
    }

    iIntros "(HI & Hb)".
    iNamed "HI".

    iMod ("Hbufupd" with "[$Hbuf]") as "Hbuftxn".
    { intuition. }

    rewrite insert_id.
    2: { admit. }

    wp_pures.
    wp_apply util_proof.wp_DPrintf.
    wp_pures.
    wp_load.
    wp_pures.
    iApply "HΦ".
    iFrame "Hdataslice Hbuftxn".
    iFrame.
    iSplitL "Hdiskblk".
    { iExists _. iFrame. done. }

    iPureIntro. intuition.
    { admit. }
    { admit. }

  - admit.
Admitted.

End heap.
