From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.algebra Require Import deletable_heap liftable.
From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.

From Goose.github_com.mit_pdos.goose_nfsd Require Import simple super.
From Perennial.program_proof Require Import txn.txn_proof buftxn.buftxn_proof marshal_proof addr_proof lockmap_proof.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.Helpers Require Import NamedProps Map List.
From Perennial.program_logic Require Import spec_assert.

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

Definition is_super_mem (l: loc) : iProp Σ :=
  "#Hsuplog" ∷ readonly (l ↦[FsSuper.S :: "nLog"] #513) ∗
  "#Hsupbb" ∷ readonly (l ↦[FsSuper.S :: "NBlockBitmap"] #0) ∗
  "#Hsupib" ∷ readonly (l ↦[FsSuper.S :: "NInodeBitmap"] #0) ∗
  "#Hsupi" ∷ readonly (l ↦[FsSuper.S :: "nInodeBlk"] #1).

Definition encodes_inode (len: u64) (blk: u64) data : Prop :=
  has_encoding data (EncUInt64 len :: EncUInt64 blk :: nil).

Definition inum2addr inum := Build_addr LogSz (inum * InodeSz * 8).
Definition blk2addr blk := Build_addr blk 0.

Definition is_inode_enc γ (inum: nat) (len: u64) (blk: u64) : iProp Σ :=
  ∃ (ibuf : defs.inode_buf),
    ⌜ encodes_inode len blk (vec_to_list ibuf) ⌝ ∗
    mapsto_txn γ.(simple_txn) (inum2addr inum) (existT _ (defs.bufInode ibuf)).

Definition is_inode_data γ (blk: u64) (contents: list u8) : iProp Σ :=
  ∃ (bbuf : Block),
    ⌜ firstn (length contents) (vec_to_list bbuf) = contents ⌝ ∗
    mapsto_txn γ.(simple_txn) (blk2addr blk) (existT _ (defs.bufBlock bbuf)).

Definition is_inode_disk γ (inum: nat) (state: simple.ino) : iProp Σ :=
  ∃ (blk: u64),
    is_inode_enc γ inum (length state) blk ∗
    is_inode_data γ blk state.

Definition is_inode_mem (l: loc) (inum: nat) (len: u64) (blk: u64) : iProp Σ :=
  l ↦[Inode.S :: "Inum"] #inum ∗
  l ↦[Inode.S :: "Size"] #len ∗
  l ↦[Inode.S :: "Data"] #blk.

Theorem wp_Inum2Addr sup inum :
  {{{ is_super_mem sup ∗
      ⌜ inum < NumInodes ⌝ }}}
    FsSuper__Inum2Addr #sup #inum
  {{{ RET (addr2val (inum2addr inum)); True }}}.
Proof.
  iIntros (Φ) "[Hsup %] HΦ".
  iNamed "Hsup".
  wp_call.

  (* XXX goose bug: [common.INODESZ] *)
Admitted.

Theorem wp_ReadInode γ inum len blk (sup btxn : loc) bufm :
  {{{ is_super_mem sup ∗
      is_buftxn btxn bufm γ.(simple_txn) ∗
      is_inode_enc γ inum len blk ∗
      ⌜ inum < NumInodes ⌝ }}}
    ReadInode #btxn #sup #inum
  {{{ l, RET #l;
      is_inode_enc γ inum len blk ∗
      is_inode_mem l inum len blk }}}.
Proof.
  iIntros (Φ) "(#Hsup & Hbuftxn & Henc & %) HΦ".

  wp_call.
  wp_apply (wp_Inum2Addr with "[$Hsup]"); auto.
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

Definition covered_inodes : gmap u64 unit :=
  ∅. (* Should really be 1..NumInodes maps to tt *)

Definition is_fs γ (nfs: loc) : iProp Σ :=
  ∃ (txn super lm : loc),
    readonly (nfs ↦[Nfs.S :: "t"] #txn) ∗
    readonly (nfs ↦[Nfs.S :: "s"] #super) ∗
    readonly (nfs ↦[Nfs.S :: "l"] #lm) ∗
    is_txn txn γ.(simple_txn) ∗
    is_super_mem super ∗
    is_lockMap lm γ.(simple_lockmapghs) covered_inodes (is_inode_stable γ).

End heap.
