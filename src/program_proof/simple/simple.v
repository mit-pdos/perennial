From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.algebra Require Import deletable_heap liftable.
From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.

From Goose.github_com.mit_pdos.goose_nfsd Require Import simple.
From Perennial.program_proof Require Import txn.txn_proof marshal_proof addr_proof lockmap_proof addr.addr_proof buf.buf_proof.
From Perennial.program_proof Require Import buftxn.sep_buftxn_proof.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.Helpers Require Import NamedProps Map List range_set.
From Perennial.algebra Require Import log_heap.
From Perennial.program_logic Require Import spec_assert.
From Perennial.goose_lang.lib Require Import slice.typed_slice into_val.
From Perennial.program_proof Require Import simple.spec.

Section heap.
Context `{!buftxnG Σ}.
Context `{!ghost_varG Σ (gmap u64 (async (list u8)))}.
Implicit Types (stk:stuckness) (E: coPset).

Record simple_names := {
  simple_buftxn : buftxn_names Σ;
  simple_state : gname;
  simple_src : gen_heapG u64 (async (list u8)) Σ;
  simple_lockmapghs : list (gen_heapG u64 bool Σ);
}.

Variable P : SimpleNFS.State -> iProp Σ.
Context `{!forall σ, Timeless (P σ)}.

Definition LogSz : nat := 513.
Definition InodeSz : nat := 128.
Definition NumInodes : nat := 4096 / InodeSz.

Definition covered_inodes : gset u64 :=
  rangeSet 2 (NumInodes-2).

Definition is_source γ : iProp Σ :=
  ∃ (src: SimpleNFS.State),
    ghost_var γ.(simple_state) (1/2) src ∗
    (* If we were doing a refinement proof, the top-level source_state would
     * own the ◯ of this ghost variable.. *)
    gen_heap_ctx (hG := γ.(simple_src)) src ∗
    ⌜dom (gset _) src = covered_inodes⌝ ∗
    P src.

Definition encodes_inode (len: u64) (blk: u64) data : Prop :=
  has_encoding data (EncUInt64 len :: EncUInt64 blk :: nil).

Definition inum2addr (inum : u64) := Build_addr LogSz (int.nat inum * InodeSz * 8).
Definition blk2addr blk := Build_addr blk 0.

Definition is_inode_enc (inum: u64) (len: u64) (blk: u64) (mapsto: addr -> object -> iProp Σ) : iProp Σ :=
  ∃ (ibuf : defs.inode_buf),
    "%Hinode_encodes" ∷ ⌜ encodes_inode len blk (vec_to_list ibuf) ⌝ ∗
    "Hinode_enc_mapsto" ∷ mapsto (inum2addr inum) (existT _ (defs.bufInode ibuf)).

Definition is_inode_data (len : u64) (blk: u64) (contents: list u8) (mapsto: addr -> object -> iProp Σ) : iProp Σ :=
  ∃ (bbuf : Block),
    "%Hdiskdata" ∷ ⌜ firstn (length contents) (vec_to_list bbuf) = contents ⌝ ∗
    "%Hdisklen" ∷ ⌜ int.Z len = length contents ⌝ ∗
    "Hdiskblk" ∷ mapsto (blk2addr blk) (existT _ (defs.bufBlock bbuf)).

Definition is_inode (inum: u64) (state: list u8) (mapsto: addr -> object -> iProp Σ) : iProp Σ :=
  ∃ (blk: u64),
    "Hinode_enc" ∷ is_inode_enc inum (length state) blk mapsto ∗
    "Hinode_data" ∷ is_inode_data (length state) blk state mapsto.

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

Definition Nbuftxn := nroot .@ "buftxn".

Theorem wp_ReadInode γ γtxn (inum : u64) len blk (btxn : loc) dinit P0 :
  {{{ is_buftxn Nbuftxn btxn γ.(simple_buftxn) dinit γtxn P0 ∗
      is_inode_enc inum len blk (buftxn_maps_to γtxn) ∗
      ⌜ inum ∈ covered_inodes ⌝ }}}
    ReadInode #btxn #inum
  {{{ l, RET #l;
      is_buftxn Nbuftxn btxn γ.(simple_buftxn) dinit γtxn P0 ∗
      is_inode_enc inum len blk (buftxn_maps_to γtxn) ∗
      is_inode_mem l inum len blk }}}.
Proof.
  iIntros (Φ) "(Hbuftxn & Henc & %Hcovered) HΦ".
  iNamed "Henc".

  wp_call.
  wp_apply (wp_inum2Addr); auto.
  {
    iPureIntro.
    rewrite /covered_inodes in Hcovered.
    eapply rangeSet_lookup in Hcovered; try lia.
    rewrite /NumInodes /InodeSz. simpl. lia.
  }

  replace (#(LitInt (word.mul 128 8))) with (#1024%nat) by reflexivity.
  wp_apply (wp_BufTxn__ReadBuf with "[$Hbuftxn $Hinode_enc_mapsto]"); eauto.
  iIntros (dirty bufptr) "[Hbuf Hbufdone]".

  wp_pures. wp_call.
  wp_apply wp_allocStruct; eauto.
  iIntros (iptr) "Hi".
  iDestruct (struct_fields_split with "Hi") as "Hi". iNamed "Hi".
  wp_apply (wp_buf_loadField_data with "Hbuf").
  iIntros (bufslice) "[Hbufdata Hbufwithoutdata]".
  rewrite is_buf_data_has_obj. iDestruct "Hbufdata" as (bufdata) "[Hbufslice %]".
  wp_apply (wp_new_dec with "Hbufslice").
  { rewrite /encodes_inode in Hinode_encodes.
    rewrite /data_has_obj /= in H0. subst. eauto. }
  iIntros (dec) "Hdec".
  wp_storeField.
  wp_apply (wp_Dec__GetInt with "Hdec"). iIntros "Hdec".
  wp_storeField.
  wp_apply (wp_Dec__GetInt with "Hdec"). iIntros "Hdec".
  wp_storeField.
  iDestruct (is_dec_to_is_slice_small with "Hdec") as "Hbufslice".
  iMod ("Hbufdone" with "[Hbufslice Hbufwithoutdata] []") as "[Hbuftxn Hbuf]"; eauto.
  {
    iApply is_buf_return_data. iFrame.
    iApply (data_has_obj_to_buf_data with "Hbufslice").
    eauto.
  }
  wp_pures.
  iApply "HΦ".
  iFrame. iExists _. iFrame "∗%".
Qed.

Definition is_inode_stable γ (inum: u64) : iProp Σ :=
  ∃ (state: list u8),
    "Hinode_state" ∷ mapsto (hG := γ.(simple_src)) inum 1%Qp (sync state) ∗
    "Hinode_disk" ∷ is_inode inum state (durable_mapsto γ.(simple_buftxn)).

Definition N := nroot .@ "simplenfs".

Theorem wp_Inode__Read γ γtxn ip inum len blk (btxn : loc) (offset : u64) (bytesToRead : u64) contents P0 dinit :
  {{{ is_buftxn Nbuftxn btxn γ.(simple_buftxn) dinit γtxn P0 ∗
      is_inode_mem ip inum len blk ∗
      is_inode_data len blk contents (buftxn_maps_to γtxn)
  }}}
    Inode__Read #ip #btxn #offset #bytesToRead
  {{{ resSlice (eof : bool) (vs : list u8), RET (slice_val resSlice, #eof);
      is_slice resSlice u8T 1 vs ∗
      is_buftxn Nbuftxn btxn γ.(simple_buftxn) dinit γtxn P0 ∗
      is_inode_mem ip inum len blk ∗
      is_inode_data len blk contents (buftxn_maps_to γtxn) ∗
      ⌜ firstn (length vs) (skipn (int.nat offset) contents) = vs ⌝ ∗
      ⌜ eof = true <-> (int.nat offset + length vs ≥ int.nat len)%nat ⌝
  }}}.
Proof.
  iIntros (Φ) "(Hbuftxn & Hmem & Hdata) HΦ".
  wp_call.
  iNamed "Hmem".
  iNamed "Hdata".
  wp_loadField.
  wp_if_destruct.
  { wp_pures.
    replace (slice.nil) with (slice_val (Slice.nil)); auto.
    iApply "HΦ".
    iSplitR.
    { iApply (is_slice_zero (V:=u8)). }
    iFrame. iSplit.
    { iExists _. iFrame "∗%". }
    iPureIntro; intuition.
    simpl. lia.
  }

  wp_apply wp_ref_to; first by val_ty.
  iIntros (count) "Hcount".
  wp_loadField. wp_load.

  wp_apply (wp_If_join
    (∃ (countval : u64),
      "Hcount" ∷ count ↦[uint64T] #countval ∗
      "Hisize" ∷ ip ↦[Inode.S :: "Size"] #len ∗
      "%Hcountval0" ∷ ⌜(int.Z countval ≤ int.Z bytesToRead)%Z⌝ ∗
      "%Hcountval1" ∷ ⌜(int.Z offset + int.Z countval ≤ int.Z len)%Z⌝
    ) with "[Hcount Hisize]").
  1: iSplit.
  { iIntros "[%Hdec HΦ]". apply bool_decide_eq_true_1 in Hdec.
    wp_loadField. wp_store.
    iApply "HΦ". iFrame.
    iExists _. iFrame. iPureIntro. split.
    { lia. }
    word.
  }
  { iIntros "[%Hdec HΦ]". apply bool_decide_eq_false_1 in Hdec.
    (* XXX how to get rid of the outermost [WP #()]? *)
    admit.
  }
  iIntros "H". iNamed "H".

  wp_apply util_proof.wp_DPrintf.
  wp_pures.
  wp_apply (wp_NewSlice (V:=u8)).
  iIntros (dataslice) "Hdataslice".
  wp_apply wp_ref_to; first by val_ty.
  iIntros (datavar) "Hdatavar".
  wp_pures.
  wp_loadField.
  wp_apply wp_block2addr.
  wp_apply (wp_BufTxn__ReadBuf with "[$Hbuftxn $Hdiskblk]"); first by reflexivity.

  iIntros (dirty bufptr) "[Hbuf Hbufupd]".
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
      "%Hcontent" ∷ ⌜ firstn (int.nat i) (skipn (int.nat offset) contents) = vs ⌝ ∗
      "%Hvslen" ∷ ⌜ length vs = (int.nat i) ⌝ ∗
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
    simpl.
    apply (f_equal length) in Hcontent as Hlens.
    autorewrite with len in Hlens.
(*
    rewrite -> word.unsigned_sub, wrap_small in Hbound by word.
*)
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
    iSplit.
    { iPureIntro. word_cleanup.
      replace (Z.to_nat (int.Z b' + 1)) with (int.nat b' + 1) by word.
      admit.
    }
    iSplit.
    { iPureIntro. rewrite app_length /=. word. }
    iApply is_buf_return_data. iFrame.
  }
  {
    iExists _, _.
    iFrame.
    rewrite /= //.
  }

  iIntros "(HI & Hb)".
  iNamed "HI".

  iMod ("Hbufupd" with "[$Hbuf] []") as "[Hbuftxn Hbuf]".
  { intuition. }

  wp_loadField. wp_load. wp_pures.

  wp_apply util_proof.wp_DPrintf.
  wp_load.
  wp_pures.
  iApply "HΦ".
  iFrame "Hdataslice Hbuftxn".
  iFrame. iSplit.
  { iExists _. iFrame "∗%". }

  iPureIntro. intuition (try congruence).
  {
    apply bool_decide_eq_true_1 in H0.
    rewrite Hvslen. revert H0. word.
  }
  {
    eapply bool_decide_eq_true_2.
    revert H0. rewrite Hvslen. word.
  }
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
  iMod (readonly_load with "Hfh_slice") as (q) "Hslice".
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

Lemma elem_of_covered_inodes (x:u64) :
  x ∈ covered_inodes ↔ (2 ≤ int.Z x < 32)%Z.
Proof.
  rewrite /covered_inodes.
  rewrite rangeSet_lookup //.
Qed.

Theorem wp_validInum (i : u64) :
  {{{ True }}}
    validInum #i
  {{{ (valid : bool), RET #valid; ⌜ valid = true <-> i ∈ covered_inodes ⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  wp_if_destruct.
  { iApply "HΦ". rewrite elem_of_covered_inodes.
    iPureIntro.
    split; [ inversion 1 | intros ].
    move: H0; word. }
  wp_if_destruct.
  { iApply "HΦ". rewrite elem_of_covered_inodes.
    iPureIntro.
    split; [ inversion 1 | intros ].
    move: H0; word. }
  wp_call.
  change (int.Z (word.divu _ _)) with 32%Z.
  wp_if_destruct.
  { iApply "HΦ". rewrite elem_of_covered_inodes.
    iPureIntro.
    split; [ inversion 1 | intros ].
    word. }
  iApply "HΦ".
  iPureIntro. intuition.
  rewrite elem_of_covered_inodes.
  split; [ | word ].
  assert (i ≠ U64 0) as Hnot_0%(not_inj (f:=int.Z)) by congruence.
  assert (i ≠ U64 1) as Hnot_1%(not_inj (f:=int.Z)) by congruence.
  change (int.Z 0%Z) with 0%Z in *.
  change (int.Z 1%Z) with 1%Z in *.
  word.
Qed.

Opaque nfstypes.READ3res.S.

Definition is_fs γ (nfs: loc) dinit : iProp Σ :=
  ∃ (txn lm : loc),
    "#Hfs_txn" ∷ readonly (nfs ↦[Nfs.S :: "t"] #txn) ∗
    "#Hfs_lm" ∷ readonly (nfs ↦[Nfs.S :: "l"] #lm) ∗
    "#Histxn" ∷ is_txn txn γ.(simple_buftxn).(buftxn_txn_names) dinit ∗
    "#Hislm" ∷ is_lockMap lm γ.(simple_lockmapghs) covered_inodes (is_inode_stable γ) ∗
    "#Hsrc" ∷ inv N (is_source γ) ∗
    "#Htxnsys" ∷ is_txn_system Nbuftxn γ.(simple_buftxn).

Global Instance is_fs_persistent γ nfs dinit : Persistent (is_fs γ nfs dinit).
Proof. apply _. Qed.


Lemma nfstypes_read3res_merge reply s ok fail :
  ( reply ↦[nfstypes.READ3res.S :: "Status"] s ∗
    reply ↦[nfstypes.READ3res.S :: "Resok"] ok ∗
    reply ↦[nfstypes.READ3res.S :: "Resfail"] fail ) -∗
  reply ↦[struct.t nfstypes.READ3res.S]{1} (s, (ok, (fail, #()))).
Proof.
  iIntros "(Status & Resok & Resfail)".
  iApply struct_fields_split. iFrame. done.
Qed.

Theorem wp_NFSPROC3_READ γ (nfs : loc) (fh : u64) (fhslice : Slice.t) (offset : u64) (count : u32) (Q : SimpleNFS.res (bool * SimpleNFS.buf) -> iProp Σ) dinit :
  {{{ is_fs γ nfs dinit ∗
      is_fh fhslice fh ∗
      ∀ σ σ' r E,
        ⌜relation.denote (SimpleNFS.wrapper fh (SimpleNFS.read fh offset count)) σ σ' r⌝ -∗
        ( P σ ={E}=∗ P σ' ∗ Q r )
  }}}
    Nfs__NFSPROC3_READ #nfs
      (struct.mk_f nfstypes.READ3args.S [
        "File" ::= struct.mk_f nfstypes.Nfs_fh3.S [
          "Data" ::= slice_val fhslice
        ];
        "Offset" ::= #offset;
        "Count" ::= #count
      ])%V
  {{{ v,
      RET v;
      ( ∃ (eof : bool) (databuf : list u8) (dataslice : Slice.t) resok,
        ⌜ getField_f nfstypes.READ3res.S "Status" v = #(U32 0) ⌝ ∗
        ⌜ getField_f nfstypes.READ3res.S "Resok" v = resok ⌝ ∗
        ⌜ getField_f nfstypes.READ3resok.S "Eof" resok = #eof ⌝ ∗
        ⌜ getField_f nfstypes.READ3resok.S "Data" resok = slice_val dataslice ⌝ ∗
        is_slice dataslice u8T 1%Qp databuf ∗
        Q (SimpleNFS.OK (eof, databuf)) ) ∨
      ( ⌜ getField_f nfstypes.READ3res.S "Status" v ≠ #(U32 0) ⌝ ∗
        Q SimpleNFS.Err )
  }}}.
Proof.
  iIntros (Φ) "(Hfs & #Hfh & Hfupd) HΦ".
  iNamed "Hfs".

  wp_call.
  wp_apply wp_ref_of_zero; first by auto.
  iIntros (reply) "Hreply".
  wp_apply util_proof.wp_DPrintf.
  wp_loadField.
  wp_apply (wp_BufTxn__Begin with "[$Histxn $Htxnsys]").
  iIntros (γtxn buftx) "Hbuftxn".
  wp_apply (wp_fh2ino with "Hfh").
  wp_pures.
  wp_apply (wp_validInum).
  iIntros (valid) "%Hvalid".
  wp_if_destruct.
  { wp_pures.
    wp_apply (wp_storeField_struct with "Hreply"); first by auto.
    iIntros "Hreply".

    (* Simulate to get Q *)
    iApply fupd_wp.
    iInv "Hsrc" as ">Hopen" "Hclose".
    iDestruct "Hopen" as (src) "(Hsrcown & Hsrcheap & %Hdom & HP)".
    iDestruct ("Hfupd" with "[] HP") as "Hfupd".
    {
      iPureIntro.
      simpl.
      monad_simpl.
      simpl.
      destruct (src !! fh) eqn:He.
      { exfalso.
        assert (fh ∈ dom (gset u64) src) as Hin.
        { apply elem_of_dom. rewrite He. eauto. }
        rewrite Hdom in Hin. apply Hvalid in Hin. congruence. }
      rewrite He.
      econstructor. eauto.
    }
    iMod "Hfupd" as "[HP HQ]".
    iMod ("Hclose" with "[Hsrcown Hsrcheap HP]").
    { iModIntro. iExists _. iFrame "∗%". }
    iModIntro.

    wp_load.
    iApply "HΦ".
    iRight.
    iFrame "HQ".
    iPureIntro.
    Transparent nfstypes.READ3res.S.
    simpl.
    Opaque nfstypes.READ3res.S.
    intro He. inversion He. (* XXX why doesn't [congruence] do the right thing? *)
  }

  wp_loadField.
  wp_apply (wp_LockMap__Acquire with "[$Hislm]"); first by intuition eauto.
  iIntros "[Hstable Hlocked]".
  iNamed "Hstable".

  iMod (lift_liftable_into_txn with "Hbuftxn Hinode_disk") as "[Hinode_disk Hbuftxn]".
  { solve_ndisj. }
  iNamed "Hinode_disk".

  wp_apply (wp_ReadInode with "[$Hbuftxn $Hinode_enc]"); first by intuition eauto.
  iIntros (ip) "(Hbuftxn & Hinode_enc & Hinode_mem)".

  wp_apply (wp_Inode__Read with "[$Hbuftxn $Hinode_mem $Hinode_data]").
  iIntros (resSlice eof vs) "(HresSlice & Hbuftxn & Hinode_mem & Hinode_data & %Hvs & %Heof)".
  wp_apply (wp_BufTxn__CommitWait with "[$Hbuftxn Hinode_enc Hinode_data]").
  4: { (* XXX is there a clean version of this? *) generalize (buftxn_maps_to γtxn). intros. iAccu. }
  all: try solve_ndisj.
  { typeclasses eauto. }

  iIntros (ok) "Hcommit".
  iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".
  wp_if_destruct; subst.
  - wp_storeField.

    wp_apply wp_slice_len.
    wp_apply (wp_struct_fieldRef_mapsto with "Resok"); first done.
    iIntros (fl) "[%Hfl Resok]".
    wp_apply (wp_storeField_struct with "Resok").
    { auto. }
    iIntros "Resok".
    rewrite Hfl; clear Hfl fl.

    wp_apply (wp_struct_fieldRef_mapsto with "Resok"); first done.
    iIntros (fl) "[%Hfl Resok]".
    wp_apply (wp_storeField_struct with "Resok").
    { compute. val_ty. }
    iIntros "Resok".
    rewrite Hfl; clear Hfl fl.

    wp_apply (wp_struct_fieldRef_mapsto with "Resok"); first done.
    iIntros (fl) "[%Hfl Resok]".
    wp_apply (wp_storeField_struct with "Resok").
    { compute. val_ty. }
    iIntros "Resok".
    rewrite Hfl; clear Hfl fl.

    (* Simulate to get Q *)
    iApply fupd_wp.
    iInv "Hsrc" as ">Hopen" "Hclose".
    iDestruct "Hopen" as (src) "(Hsrcown & Hsrcheap & %Hdom & HP)".
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
      instantiate (3 := false).
      simpl.
      monad_simpl.
    }
    iMod "Hfupd" as "[HP HQ]".
    iMod ("Hclose" with "[Hsrcown Hsrcheap HP]").
    { iModIntro. iExists _. iFrame "∗%". }
    iModIntro.

    wp_loadField.
    wp_apply (wp_LockMap__Release with "[$Hislm $Hlocked Hinode_state Hcommit]").
    { iExists _. iFrame.
      iDestruct "Hcommit" as "(Hinode_enc & Hinode_data)".
      iExists _. iFrame. }

    wp_apply (wp_LoadAt with "[Status Resok Resfail]").
    { iModIntro. iApply nfstypes_read3res_merge. iFrame. }
    iIntros "Hreply". simpl.
    iApply "HΦ". iLeft.
    iExists _, _, _, _.
Transparent nfstypes.READ3res.S.
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iFrame. iExactEq "HQ".
    f_equal. f_equal. f_equal.
    { destruct eof; (intuition idtac);
        destruct (ge_dec (int.nat offset + int.nat count) (length state)); try reflexivity.
      { (* need [length vs <= count]? *) admit. }
      { symmetry. eapply H3. admit. }
    }
    { rewrite -Hvs. (* again, [length vs] and [count].. *) admit. }

  - wp_storeField.

    (* Simulate to get Q *)
    iApply fupd_wp.
    iInv "Hsrc" as ">Hopen" "Hclose".
    iDestruct "Hopen" as (src) "(Hsrcown & Hsrcheap & %Hdom & HP)".
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
    { iModIntro. iExists _. iFrame "∗%". }
    iModIntro.

    wp_loadField.
    wp_apply (wp_LockMap__Release with "[$Hislm $Hlocked Hinode_state Hcommit]").
    { iExists _. iFrame.
      iDestruct "Hcommit" as "[Hinode_disk _]". iFrame. }

    wp_apply (wp_LoadAt with "[Status Resok Resfail]").
    { iModIntro. iApply nfstypes_read3res_merge. iFrame. }
    iIntros "Hreply".
    iApply "HΦ".
    iRight. iFrame "HQ".
    iPureIntro.
    Transparent nfstypes.READ3res.S.
    simpl.
    Opaque nfstypes.READ3res.S.
    done.
  Admitted.

End heap.
