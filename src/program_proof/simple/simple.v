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
From Perennial.algebra Require Import log_heap.
From Perennial.program_logic Require Import spec_assert.
From Perennial.goose_lang.lib Require Import slice.typed_slice into_val.
From Perennial.program_proof Require Import simple.spec.

(* XXX lift somewhere higher up *)
Canonical Structure u64O := leibnizO u64.
Canonical Structure u8O := leibnizO u8.
Canonical Structure asyncO T := leibnizO (async T).

Section heap.
Context `{!crashG Σ}.
Context `{!buftxnG Σ}.
Context `{!inG Σ (ghostR $ gmapO u64O $ asyncO $ list u8)}.
Implicit Types (stk:stuckness) (E: coPset).

Record simple_names := {
  simple_txn : @txn_names Σ;
  simple_state : gname;
  simple_src : gen_heapG u64 (async (list u8)) Σ;
  simple_lockmapghs : list (gen_heapG u64 bool Σ);
}.

Variable P : SimpleNFS.State -> iProp Σ.
Context `{!forall σ, Timeless (P σ)}.

Definition is_source γ : iProp Σ :=
  ∃ (src: SimpleNFS.State),
    own γ.(simple_state) (● Excl' src) ∗
    (* If we were doing a refinement proof, the top-level source_state would
     * own the ◯ of this ghost variable.. *)
    gen_heap_ctx (hG := γ.(simple_src)) src ∗
    P src.

Definition LogSz : nat := 513.
Definition InodeSz : nat := 128.
Definition NumInodes : nat := 4096 / InodeSz.

Definition encodes_inode (len: u64) (blk: u64) data : Prop :=
  has_encoding data (EncUInt64 len :: EncUInt64 blk :: nil).

Definition inum2addr (inum : u64) := Build_addr LogSz (int.nat inum * InodeSz * 8).
Definition blk2addr blk := Build_addr blk 0.

Definition is_inode_enc γ (inum: u64) (len: u64) (blk: u64) : iProp Σ :=
  ∃ (ibuf : defs.inode_buf),
    "%Hinode_encodes" ∷ ⌜ encodes_inode len blk (vec_to_list ibuf) ⌝ ∗
    "Hinode_enc_mapsto" ∷ mapsto_txn γ.(simple_txn) (inum2addr inum) (existT _ (defs.bufInode ibuf)).

Definition is_inode_data γ (len : u64) (blk: u64) (contents: list u8) : iProp Σ :=
  ∃ (bbuf : Block),
    "%Hdiskdata" ∷ ⌜ firstn (length contents) (vec_to_list bbuf) = contents ⌝ ∗
    "%Hdisklen" ∷ ⌜ len = length contents ⌝ ∗
    "Hdiskblk" ∷ mapsto_txn γ.(simple_txn) (blk2addr blk) (existT _ (defs.bufBlock bbuf)).

Definition is_inode_disk γ (inum: u64) (state: list u8) : iProp Σ :=
  ∃ (blk: u64),
    "Hinode_enc" ∷ is_inode_enc γ inum (length state) blk ∗
    "Hinode_data" ∷ is_inode_data γ (length state) blk state.

Definition is_inode_mem (l: loc) (inum: u64) (len: u64) (blk: u64) : iProp Σ :=
  "Hinum" ∷ l ↦[Inode.S :: "Inum"] #inum ∗
  "Hisize" ∷ l ↦[Inode.S :: "Size"] #len ∗
  "Hidata" ∷ l ↦[Inode.S :: "Data"] #blk.

Theorem wp_inum2Addr (inum : u64) :
  {{{ ⌜ int.nat inum < NumInodes ⌝ }}}
    inum2Addr #inum
  {{{ RET (addr2val (inum2addr inum)); True }}}.
Proof.
  iIntros (Φ) "% HΦ".
  wp_call.
  wp_call.
  rewrite /addr2val /inum2addr /=.
  rewrite /LogSz /InodeSz.
  replace (word.add (word.divu (word.sub 4096 8) 8) 2)%Z with (U64 513) by reflexivity.
(*
  replace (word.mul (word.mul inum 128) 8)%Z with (U64 (inum * 128 * 8)%nat).
  { iApply "HΦ". done. }

  revert H.
  rewrite /NumInodes /InodeSz.
  replace (4096 `div` 128) with (32) by reflexivity.
  intros.
  word_cleanup.
  admit.
*)
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

Definition covered_inodes : gset u64 :=
  rangeSet 2 (NumInodes-2).

Theorem wp_ReadInode γ (inum : u64) len blk (btxn : loc) bufm :
  {{{ is_buftxn btxn bufm γ.(simple_txn) ∗
      is_inode_enc γ inum len blk ∗
      ⌜ inum ∈ covered_inodes ⌝ }}}
    ReadInode #btxn #inum
  {{{ l, RET #l;
      is_buftxn btxn bufm γ.(simple_txn) ∗
      is_inode_enc γ inum len blk ∗
      is_inode_mem l inum len blk }}}.
Proof.
  iIntros (Φ) "(Hbuftxn & Henc & %) HΦ".

  wp_call.
  wp_apply (wp_inum2Addr); auto.
(*
  replace (#(LitInt (word.mul 128 8))) with (#1024%nat) by reflexivity.
  wp_apply (wp_BufTxn__ReadBuf with "[$Hbuftxn]").
*)

  (* Need the [is_inode_enc] to be actually lifted into the buftxn active transaction.
   * Need to solve two problems to get there:
   * - Current buftxn spec just has a gmap, and
   * - [is_inode_enc] is not parameterized by txn/buftxn.
   *)
Admitted.

Definition is_inode_stable γ (inum: u64) : iProp Σ :=
  ∃ (state: list u8),
    "Hinode_state" ∷ mapsto (hG := γ.(simple_src)) inum 1%Qp (sync state) ∗
    "Hinode_disk" ∷ is_inode_disk γ inum state.

Definition N := nroot .@ "simplenfs".

Definition is_fs γ (nfs: loc) : iProp Σ :=
  ∃ (txn lm : loc),
    "#Hfs_txn" ∷ readonly (nfs ↦[Nfs.S :: "t"] #txn) ∗
    "#Hfs_lm" ∷ readonly (nfs ↦[Nfs.S :: "l"] #lm) ∗
    "#Histxn" ∷ is_txn txn γ.(simple_txn) ∗
    "#Hislm" ∷ is_lockMap lm γ.(simple_lockmapghs) covered_inodes (is_inode_stable γ) ∗
    "#Hsrc" ∷ inv N (is_source γ).

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

Definition is_fh (s : Slice.t) (fh : u64) : iProp Σ :=
  ∃ vs,
    "#Hfh_slice" ∷ readonly (is_slice_small s u8T 1 vs) ∗
    "%Hfh_enc" ∷ ⌜ has_encoding vs (EncUInt64 fh :: nil) ⌝.

Opaque slice_val.

Theorem wp_fh2ino s i :
  {{{ is_fh s i }}}
    fh2ino (slice_val s, #())%V
  {{{ RET #i; True }}}.
Proof.
  iIntros (Φ) "Hfh HΦ".
  iNamed "Hfh".
  iMod (readonly_load with "Hfh_slice") as (q) "Hslice"; first by solve_ndisj.
  wp_call.
  wp_call.
  wp_apply (wp_new_dec with "Hslice"); first by eauto.
  iIntros (dec) "Hdec".
  wp_apply (wp_Dec__GetInt with "Hdec").
  iIntros "Hdec".
  wp_pures.
  iApply "HΦ".
  done.
Qed.

Theorem wp_validInum (i : u64) :
  {{{ True }}}
    validInum #i
  {{{ (valid : bool), RET #valid; ⌜ valid = true -> i ∈ covered_inodes ⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  wp_if_destruct.
  { iApply "HΦ". done. }
  wp_if_destruct.
  { iApply "HΦ". done. }
  wp_call.
  wp_if_destruct.
  { iApply "HΦ". done. }
  iApply "HΦ".
  iPureIntro. intuition.
  rewrite /covered_inodes /NumInodes /InodeSz.
  replace (4096 `div` 128) with (32) by reflexivity.
  replace (word.divu (U64 4096) (U64 128)) with (U64 32) in Heqb1 by reflexivity.
  apply rangeSet_lookup; try lia.
  split.
  { admit. }
  { word. }
Admitted.

Opaque nfstypes.READ3res.S.

Theorem wp_NFSPROC3_READ γ (nfs : loc) (fh : u64) (fhslice : Slice.t) (offset : u64) (count : u32) (Q : SimpleNFS.res (bool * SimpleNFS.buf) -> iProp Σ) :
  {{{ is_fs γ nfs ∗
      is_fh fhslice fh ∗
      ∀ σ σ' r E,
        ⌜relation.denote (SimpleNFS.wrapper fh (SimpleNFS.read fh offset count)) σ σ' r⌝ -∗
        ( P σ ={E}=∗ P σ' ∗ Q r )
  }}}
    Nfs__NFSPROC3_READ #nfs (slice_val fhslice, #(), (#offset, (#count, #())))%V
(*
      (struct.mk nfstypes.READ3args.S [
        "File" ::= struct.mk nfstypes.Nfs_fh3.S [
          "Data" ::= slice_val fhslice
        ];
        "Offset" ::= #offset;
        "Count" ::= #count
      ])
*)
  {{{ (ok : bool) v,
      RET v;
      if ok then
        ⌜ getField_f nfstypes.READ3res.S "Status" v = #0 ⌝ ∗
        ∃ (eof : bool) (dataslice : Slice.t) r,
          Q r
      else
        ⌜ getField_f nfstypes.READ3res.S "Status" v ≠ #0 ⌝
  }}}.
Proof.
  iIntros (Φ) "(Hfs & #Hfh & Hfupd) HΦ".
  iNamed "Hfs".

  wp_call.
  wp_apply wp_ref_of_zero; first by auto.
  iIntros (reply) "Hreply".
  wp_apply util_proof.wp_DPrintf.
  wp_loadField.
  wp_apply (wp_buftxn_Begin with "Histxn").
  iIntros (buftx) "Hbuftxn".
  wp_apply (wp_fh2ino with "Hfh").
  wp_pures.
  wp_apply (wp_validInum).
  iIntros (valid) "%Hvalid".
  wp_if_destruct.
  { wp_pures.
    wp_apply (wp_storeField_struct with "Hreply"); first by auto.
    iIntros "Hreply".

    wp_load.
    iApply ("HΦ" $! false).
    iPureIntro.
    Transparent nfstypes.READ3res.S.
    simpl.
    Opaque nfstypes.READ3res.S.
    congruence.
  }

  wp_loadField.
  wp_apply (wp_LockMap__Acquire with "[$Hislm]"); first by auto.
  iIntros "[Hstable Hlocked]".
  iNamed "Hstable".
  iNamed "Hinode_disk".
  wp_apply (wp_ReadInode with "[$Hbuftxn $Hinode_enc]"); first by auto.
  iIntros (ip) "(Hbuftxn & Hinode_enc & Hinode_mem)".
  wp_apply (wp_Inode__Read with "[$Hbuftxn $Hinode_mem $Hinode_data]").
  iIntros (resSlice eof vs) "(HresSlice & Hbuftxn & Hinode_mem & Hinode_data & %Hvs & %Heof)".
  wp_apply (wp_BufTxn__CommitWait with "[$Hbuftxn Hfupd Hinode_state]").
  {
    iModIntro.
    iExists _.
    iSplitR.
    { admit. }
    iIntros "Hown".
    iInv "Hsrc" as ">Hopen" "Hclose".
    iDestruct "Hopen" as (src) "(Hsrcown & Hsrcheap & HP)".
    iDestruct (gen_heap_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh".
    iDestruct ("Hfupd" with "[] HP") as "Hfupd".
    {
      iPureIntro.
      simpl.
      monad_simpl.
      simpl.
      rewrite Hsrc_fh.
      simpl.
      econstructor. { econstructor. auto. }
      instantiate (3 := true).
      simpl.
      monad_simpl.
    }
    iMod "Hfupd" as "[HP HQ]".
    iMod ("Hclose" with "[Hsrcown Hsrcheap HP]").
    { iModIntro. iExists _. iFrame. }
    iModIntro.

    (* XXX this might be simpler using Tej's buftxn spec *)
    admit.
  }

  iIntros (ok) "Hok".
  wp_if_destruct.
  2: {
    wp_apply (wp_storeField_struct with "Hreply"); first by auto.
    iIntros "Hreply".

    wp_loadField.
    (* XXX commitWait stole my [Hinode_state]! *)
(*
    wp_apply (wp_LockMap__Release with "[$Hislm $Hlocked Hinode_enc Hinode_data Hinode_state]").
    { iExists _. iFrame.
      iExists _. iFrame. }

    wp_load.
    iApply ("HΦ" $! false).
    iPureIntro.
    Transparent nfstypes.READ3res.S.
    simpl.
    Opaque nfstypes.READ3res.S.
    congruence.
*)
    admit.
  }

  iDestruct (struct_fields_split with "Hreply") as "Hreply".
  iNamed "Hreply".
  wp_storeField.
  (* XXX how to do anything with [struct.fieldRef]? *)
  admit.
Admitted.

End heap.
