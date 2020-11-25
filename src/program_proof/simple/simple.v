From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.algebra Require Import deletable_heap liftable auth_map.
From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.

From Goose.github_com.mit_pdos.goose_nfsd Require Import simple.
From Perennial.program_proof Require Import txn.txn_proof marshal_proof addr_proof crash_lockmap_proof addr.addr_proof buf.buf_proof.
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
Context `{!ghost_varG Σ (gmap u64 (list u8))}.
Context `{!mapG Σ u64 (list u8)}.
Implicit Types (stk:stuckness) (E: coPset).

Record simple_names := {
  simple_buftxn : buftxn_names Σ;
  simple_src : gname;
  simple_lockmapghs : list (gen_heapG u64 bool Σ);
}.

Variable P : SimpleNFS.State -> iProp Σ.
Context `{Ptimeless : !forall σ, Timeless (P σ)}.

Definition LogSz : nat := 513.
Definition InodeSz : nat := 128.
Definition NumInodes : nat := 4096 / InodeSz.

Definition covered_inodes : gset u64 :=
  rangeSet 2 (NumInodes-2).

Definition no_overflows (src : SimpleNFS.State) : iProp Σ :=
  ([∗ map] _↦istate ∈ src, ⌜(length istate < 2^64)%Z⌝)%I.

Global Instance no_overflows_Persistent src : Persistent (no_overflows src).
Proof. refine _. Qed.

Definition is_source γ : iProp Σ :=
  ∃ (src: SimpleNFS.State),
    (* If we were doing a refinement proof, the top-level source_state would
     * own 1/2 of this [map_ctx] *)
    "Hsrcheap" ∷ map_ctx γ.(simple_src) 1%Qp src ∗
    "%Hdom" ∷ ⌜dom (gset _) src = covered_inodes⌝ ∗
    "#Hnooverflow" ∷ no_overflows src ∗
    "HP" ∷ P src.

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

  rewrite /NumInodes /InodeSz in H.
  replace (4096 `div` 128) with (32) in H by reflexivity.

  replace (word.add (word.divu (word.sub 4096 8) 8) 2)%Z with (U64 513) by reflexivity.
  replace (word.mul (word.mul inum 128) 8)%Z with (U64 (int.nat inum * 128 * 8)%nat).
  { iApply "HΦ". done. }

  assert (int.Z (word.mul (word.mul inum 128) 8) = int.Z inum * 1024)%Z.
  { rewrite word.unsigned_mul.
    rewrite word.unsigned_mul. word. }

  word.
Qed.

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

Theorem wp_ReadInode γ γtxn (inum : u64) len blk (btxn : loc) dinit γdurable :
  {{{ is_buftxn_mem Nbuftxn btxn γ.(simple_buftxn) dinit γtxn γdurable ∗
      is_inode_enc inum len blk (buftxn_maps_to γtxn) ∗
      ⌜ inum ∈ covered_inodes ⌝ }}}
    ReadInode #btxn #inum
  {{{ l, RET #l;
      is_buftxn_mem Nbuftxn btxn γ.(simple_buftxn) dinit γtxn γdurable ∗
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
    rewrite /data_has_obj /= in H. subst. eauto. }
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
    "Hinode_state" ∷ inum [[γ.(simple_src)]]↦ state ∗
    "Hinode_disk" ∷ is_inode inum state (durable_mapsto_own γ.(simple_buftxn)).

Definition is_inode_crash γ (inum: u64) : iProp Σ :=
  ∃ (state: list u8),
    "Hinode_state" ∷ inum [[γ.(simple_src)]]↦ state ∗
    "Hinode_disk" ∷ is_inode inum state (durable_mapsto γ.(simple_buftxn)).

Definition is_inode_unstable γ (inum: u64) state0 state1 : iProp Σ :=
  "Hinode_state" ∷ inum [[γ.(simple_src)]]↦ state0 ∗
  "Hinode_disk" ∷ is_inode inum state1 (durable_mapsto γ.(simple_buftxn)).

Definition N := nroot .@ "simplenfs".

Theorem wp_Inode__Read γ γtxn ip inum len blk (btxn : loc) (offset : u64) (bytesToRead : u64) contents γdurable dinit :
  {{{ is_buftxn_mem Nbuftxn btxn γ.(simple_buftxn) dinit γtxn γdurable ∗
      is_inode_mem ip inum len blk ∗
      is_inode_data len blk contents (buftxn_maps_to γtxn)
  }}}
    Inode__Read #ip #btxn #offset #bytesToRead
  {{{ resSlice (eof : bool) (vs : list u8), RET (slice_val resSlice, #eof);
      is_slice resSlice u8T 1 vs ∗
      is_buftxn_mem Nbuftxn btxn γ.(simple_buftxn) dinit γtxn γdurable ∗
      is_inode_mem ip inum len blk ∗
      is_inode_data len blk contents (buftxn_maps_to γtxn) ∗
      ⌜ firstn (length vs) (skipn (int.nat offset) contents) = vs ⌝ ∗
      ⌜ length vs ≤ int.nat bytesToRead ⌝ ∗
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
    iPureIntro; intuition; simpl; lia.
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
    iApply "HΦ".
    iExists _. iFrame. iPureIntro. split.
    { lia. }
    word.
  }
  { iIntros "[%Hdec HΦ]". apply bool_decide_eq_false_1 in Hdec.
    wp_pures.
    iApply "HΦ".
    iExists _. iFrame. iPureIntro. split.
    { lia. }
    revert Hdec. word.
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

    destruct (vec_to_list bbuf !! int.nat (word.add offset b')) eqn:He.
    2: {
      exfalso.
      eapply lookup_ge_None_1 in He.
      assert (int.nat (word.add offset b') < length contents).
      { revert Hcountval1. revert Hbound. word. }
      assert (length bbuf ≥ length contents).
      2: { lia. }
      rewrite -Hdiskdata. rewrite take_length. lia.
    }
    wp_apply (wp_SliceGet (V:=u8) with "[$Hbufdata]"); eauto.
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
      replace (Z.to_nat (int.Z b' + 1)) with (S (int.nat b')) by word.
      erewrite take_S_r.
      { rewrite Hcontent. eauto. }
      rewrite lookup_drop. rewrite -Hdiskdata.
      rewrite lookup_take.
      { replace (int.nat (word.add offset b')) with (int.nat offset + int.nat b') in He by word. done. }
      lia.
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
    lia.
  }
  {
    apply bool_decide_eq_true_1 in H.
    rewrite Hvslen. revert H. word.
  }
  {
    eapply bool_decide_eq_true_2.
    revert H. rewrite Hvslen. word.
  }
Qed.

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
    move: H; word. }
  wp_if_destruct.
  { iApply "HΦ". rewrite elem_of_covered_inodes.
    iPureIntro.
    split; [ inversion 1 | intros ].
    move: H; word. }
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
    "#Hislm" ∷ is_crash_lockMap 10 lm γ.(simple_lockmapghs) covered_inodes
                                (is_inode_stable γ) (is_inode_crash γ) ∗
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

Lemma is_inode_crash_ro γ fh state blk :
  fh [[γ.(simple_src)]]↦ state ∗
  ( is_inode fh state (durable_mapsto γ.(simple_buftxn))
    ∨ is_inode_enc fh (length state) blk (durable_mapsto γ.(simple_buftxn))
    ∗ is_inode_data (length state) blk state (durable_mapsto γ.(simple_buftxn)) )
  -∗ is_inode_crash γ fh.
Proof.
  iIntros "[Hfh Hi]".
  iExists _. iFrame.
  iDestruct "Hi" as "[$|[He Hd]]".
  iExists _. iFrame.
Qed.

Lemma is_inode_crash_ro_own γ fh state blk :
  fh [[γ.(simple_src)]]↦ state ∗
  ( is_inode fh state (durable_mapsto_own γ.(simple_buftxn))
    ∨ is_inode_enc fh (length state) blk (durable_mapsto_own γ.(simple_buftxn))
    ∗ is_inode_data (length state) blk state (durable_mapsto_own γ.(simple_buftxn)) )
  -∗ is_inode_crash γ fh.
Proof.
  iIntros "[Hfh H]".
  iDestruct (liftable_mono (Φ := λ m, is_inode fh state m
      ∨ is_inode_enc fh (length state) blk m
        ∗ is_inode_data (length state) blk state m)%I
    _ (durable_mapsto γ.(simple_buftxn)) with "H") as "H".
  { iIntros (??) "[_ $]". }
  iApply is_inode_crash_ro; iFrame.
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
      ( ∃ (stat : Z),
        ⌜ getField_f nfstypes.READ3res.S "Status" v = #(U32 stat) ⌝ ∗
        ⌜ stat ≠ 0 ⌝ ∗
        Q SimpleNFS.Err )
  }}}.
Proof using Ptimeless.
  iIntros (Φ) "(Hfs & #Hfh & Hfupd) HΦ".
  iNamed "Hfs".

  wp_call.
  iFreeze "HΦ".
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
    iNamed "Hopen".
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
    iMod ("Hclose" with "[Hsrcheap HP]").
    { iModIntro. iExists _. iFrame "∗%#". }
    iModIntro.

    wp_load.
    iThaw "HΦ".
    iApply "HΦ".
    iRight. iExists _.
    iFrame "HQ".
    iPureIntro.
    Transparent nfstypes.READ3res.S.
    simpl. intuition eauto.
    Opaque nfstypes.READ3res.S.
    lia.
  }

  wp_loadField.
  wp_apply (wp_LockMap__Acquire with "[$Hislm]"); first by intuition eauto.
  iIntros "Hcrashlocked".

  wp_pures.
  wp_bind (NFSPROC3_READ_internal _ _ _ _).

  iDestruct (use_CrashLocked _ 8 with "Hcrashlocked") as "Hcrashuse"; first by lia.
  iApply (wpc_wp _ _ _ _ _ True).
  iApply "Hcrashuse".
  iSplit.
  { iModIntro. iModIntro. done. }
  iIntros ">Hstable".
  iNamed "Hstable".

  iMod (lift_liftable_into_txn with "Hbuftxn Hinode_disk") as "[Hinode_disk Hbuftxn]";
    [ solve_ndisj .. | ].
  iNamed "Hinode_disk".

  iNamed "Hbuftxn".

  iCache with "Hinode_state Hbuftxn_durable".
  { crash_case.
    iDestruct (is_buftxn_durable_to_old_pred with "Hbuftxn_durable") as "[Hold _]".
    iModIntro.
    iModIntro.
    iSplit; first done.
    iExists _.
    iFrame.
  }

  wpc_call.
  wpc_bind (NFSPROC3_READ_wp _ _ _ _).
  wpc_frame.
  wp_call.

  wp_apply (wp_ReadInode with "[$Hbuftxn_mem $Hinode_enc]"); first by intuition eauto.
  iIntros (ip) "(Hbuftxn_mem & Hinode_enc & Hinode_mem)".

  wp_apply (wp_Inode__Read with "[$Hbuftxn_mem $Hinode_mem $Hinode_data]").
  iIntros (resSlice eof vs) "(HresSlice & Hbuftxn_mem & Hinode_mem & Hinode_data & %Hvs & %Hvslen & %Heof)".

  iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".

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

  iFreeze "Status Resok Resfail".

  iNamed 1.
  wpc_pures.

  iDestruct (is_buftxn_mem_durable with "Hbuftxn_mem Hbuftxn_durable") as "Hbuftxn".

  wpc_apply (wpc_BufTxn__CommitWait with "[$Hbuftxn Hinode_enc Hinode_data]").
  4: { (* XXX is there a clean version of this? *) generalize (buftxn_maps_to γtxn). intros. iAccu. }
  all: try solve_ndisj.
  { typeclasses eauto. }

  iSplit.
  { iModIntro. iModIntro.
    iIntros "[[H _]|[H0 H1]]"; iSplit; try done; iApply is_inode_crash_ro; iFrame "Hinode_state".
    { iLeft; iFrame. }
    { iRight; iFrame. } }

  iModIntro.
  iIntros (ok) "Hcommit".
  destruct ok; subst.
  - (* Simulate to get Q *)
    iApply fupd_wpc.
    iInv "Hsrc" as ">Hopen" "Hclose".
    iNamed "Hopen".
    iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh".
    iDestruct (big_sepM_lookup with "Hnooverflow") as %Hnooverflow; eauto.
    iDestruct ("Hfupd" with "[] HP") as "Hfupd".
    {
      iPureIntro.
      simpl.
      monad_simpl.
      simpl.
      rewrite Hsrc_fh.
      simpl.
      eapply relation.bind_runs with (x:=false). { econstructor. auto. }
      simpl.
      monad_simpl.
      econstructor.
      {
        eapply relation.suchThat_runs with (x:=length vs).
        destruct (decide (length vs = 0)) eqn:He; eauto. right.
        rewrite -Hvs. rewrite take_length.
        rewrite drop_length.
        destruct (decide (int.nat offset ≤ length state)); first by lia.
        exfalso.
        rewrite -> drop_ge in Hvs by lia. rewrite take_nil in Hvs.
        subst. simpl in n. congruence.
      }
      monad_simpl.
    }
    iMod "Hfupd" as "[HP HQ]".
    iMod ("Hclose" with "[Hsrcheap HP]").
    { iModIntro. iExists _. iFrame "∗%#". }
    iModIntro.

    wpc_frame "Hinode_state Hcommit".
    { iModIntro. iModIntro. iSplit; try done.
      iApply is_inode_crash_ro_own. iFrame "Hinode_state". iRight. iFrame. }

    wp_storeField.
    iNamed 1.

    iSplitR "Hinode_state Hcommit".
    2: {
      iModIntro.
      iExists _; iFrame.
      iExists _; iFrame.
    }
    iIntros "Hcrashlocked".
    iSplit.
    { iModIntro. done. }

    wp_loadField.
    wp_apply (wp_LockMap__Release with "Hcrashlocked").

    wp_apply (wp_LoadAt with "[Status Resok Resfail]").
    { iModIntro. iApply nfstypes_read3res_merge. iThaw "Resok Resfail". iFrame. }
    iIntros "Hreply". simpl.
    iThaw "HΦ".
    iApply "HΦ". iLeft.
    iExists _, _, _, _.
Transparent nfstypes.READ3res.S.
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iFrame. iExactEq "HQ".
    assert (length state < 2^64)%Z as Hlenstatebound.
    { eapply Hnooverflow; clear Hnooverflow. }
    clear Hnooverflow.
    assert (int.nat (U64 (Z.of_nat (length state))) = length state) as Hlenstate.
    { word. }
    f_equal. f_equal. f_equal.
    { destruct eof; (intuition idtac);
        destruct (ge_dec (int.nat offset + length vs) (length state)); try reflexivity.
      { lia. }
      { symmetry. eapply H2. lia. }
    }
    { eauto. }

  - (* Simulate to get Q *)
    iApply fupd_wpc.
    iInv "Hsrc" as ">Hopen" "Hclose".
    iNamed "Hopen".
    iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh".
    iDestruct ("Hfupd" with "[] HP") as "Hfupd".
    {
      iPureIntro.
      simpl.
      monad_simpl.
      simpl.
      rewrite Hsrc_fh.
      simpl.
      eapply relation.bind_runs with (x:=true). { econstructor. auto. }
      simpl.
      monad_simpl.
    }
    iMod "Hfupd" as "[HP HQ]".
    iMod ("Hclose" with "[Hsrcheap HP]").
    { iModIntro. iExists _. iFrame "∗%#". }
    iModIntro.

    wpc_frame "Hinode_state Hcommit".
    { iModIntro. iModIntro. iDestruct "Hcommit" as "[H0 H1]".
      iSplit; first by done.
      iApply is_inode_crash_ro_own. iFrame "Hinode_state". iLeft; iFrame. }

    wp_storeField.
    iNamed 1.

    iSplitR "Hinode_state Hcommit".
    2: {
      iDestruct "Hcommit" as "[H _]".
      iModIntro.
      iExists _; iFrame.
    }
    iIntros "Hcrashlocked".
    iSplit.
    { iModIntro. done. }

    wp_loadField.
    wp_apply (wp_LockMap__Release with "Hcrashlocked").

    wp_apply (wp_LoadAt with "[Status Resok Resfail]").
    { iModIntro. iApply nfstypes_read3res_merge. iThaw "Resok Resfail". iFrame. }
    iIntros "Hreply".
    iThaw "HΦ".
    iApply "HΦ".
    iRight. iExists _. iFrame "HQ".
    iPureIntro.
    Transparent nfstypes.READ3res.S.
    simpl. intuition eauto.
    Opaque nfstypes.READ3res.S.
    lia.

Unshelve.
  all: eauto.
Qed.

Opaque nfstypes.GETATTR3res.S.

Theorem wp_Inode__MkFattr ip inum len blk :
  {{{
      is_inode_mem ip inum len blk
  }}}
    Inode__MkFattr #ip
  {{{ fattr3, RET fattr3;
      is_inode_mem ip inum len blk ∗
      ⌜ getField_f nfstypes.Fattr3.S "Size" fattr3 = #len ⌝ ∗
      ⌜ getField_f nfstypes.Fattr3.S "Fileid" fattr3 = #inum ⌝ ∗
      ⌜ val_ty fattr3 (struct.t nfstypes.Fattr3.S) ⌝
  }}}.
Proof.
  iIntros (Φ) "Hmem HΦ".
  wp_call.
  iNamed "Hmem".
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_pures.
  iApply "HΦ".
  iSplit.
  { iFrame. }
  iPureIntro; simpl. eauto.
Qed.

Theorem wp_rootFattr :
  {{{ True
  }}}
    rootFattr #()
  {{{ fattr3, RET fattr3;
      ⌜ getField_f nfstypes.Fattr3.S "Size" fattr3 = #0 ⌝ ∗
      ⌜ val_ty fattr3 (struct.t nfstypes.Fattr3.S) ⌝
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  iApply "HΦ". eauto.
Qed.

Lemma nfstypes_getattr3res_merge reply s ok :
  ( reply ↦[nfstypes.GETATTR3res.S :: "Status"] s ∗
    reply ↦[nfstypes.GETATTR3res.S :: "Resok"] ok ) -∗
  reply ↦[struct.t nfstypes.GETATTR3res.S]{1} (s, (ok, #())).
Proof.
  iIntros "(Status & Resok)".
  iApply struct_fields_split. iFrame. done.
Qed.

Theorem wp_NFSPROC3_GETATTR γ (nfs : loc) (fh : u64) (fhslice : Slice.t) (Q : SimpleNFS.res SimpleNFS.fattr -> iProp Σ) dinit :
  {{{ is_fs γ nfs dinit ∗
      is_fh fhslice fh ∗
      ∀ σ σ' r E,
        ⌜relation.denote (SimpleNFS.full_getattr fh) σ σ' r⌝ -∗
        ( P σ ={E}=∗ P σ' ∗ Q r )
  }}}
    Nfs__NFSPROC3_GETATTR #nfs
      (struct.mk_f nfstypes.GETATTR3args.S [
        "Object" ::= struct.mk_f nfstypes.Nfs_fh3.S [
          "Data" ::= slice_val fhslice
        ]
      ])%V
  {{{ v,
      RET v;
      ( ∃ (sz : u64) resok fattr3,
        ⌜ getField_f nfstypes.GETATTR3res.S "Status" v = #(U32 0) ⌝ ∗
        ⌜ getField_f nfstypes.GETATTR3res.S "Resok" v = resok ⌝ ∗
        ⌜ getField_f nfstypes.GETATTR3resok.S "Obj_attributes" resok = fattr3 ⌝ ∗
        ⌜ getField_f nfstypes.Fattr3.S "Size" fattr3 = #sz ⌝ ∗
        Q (SimpleNFS.OK (SimpleNFS.Build_fattr sz)) ) ∨
      ( ∃ (stat : Z),
        ⌜ getField_f nfstypes.GETATTR3res.S "Status" v = #(U32 stat) ⌝ ∗
        ⌜ stat ≠ 0 ⌝ ∗
        Q SimpleNFS.Err )
  }}}.
Proof using Ptimeless.
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
  wp_if_destruct.
  {
    wp_apply (wp_storeField_struct with "Hreply"); first by auto. iIntros "Hreply".

    (* Simulate to get Q *)
    iApply fupd_wp.
    iInv "Hsrc" as ">Hopen" "Hclose".
    iNamed "Hopen".
    iDestruct ("Hfupd" with "[] HP") as "Hfupd".
    {
      iPureIntro.
      rewrite /SimpleNFS.full_getattr.
      case_decide as cond; try congruence.
      econstructor. { econstructor. eauto. }
      simpl.
      monad_simpl.
    }
    iMod "Hfupd" as "[HP HQ]".
    iMod ("Hclose" with "[Hsrcheap HP]").
    { iModIntro. iExists _. iFrame "∗%#". }
    iModIntro.

    wp_apply wp_rootFattr. iIntros (fattr3) "(%Hlen & %Hfattr3)".

    iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".

    wp_apply (wp_struct_fieldRef_mapsto with "Resok"); first done.
    iIntros (fl) "[%Hfl Resok]".
    wp_apply (wp_storeField_struct with "Resok").
    { eauto. }
    iIntros "Resok".
    rewrite Hfl; clear Hfl fl.

    wp_apply (wp_LoadAt with "[Status Resok]").
    { iModIntro. iApply nfstypes_getattr3res_merge. iFrame. }
    iIntros "Hreply".

    iApply "HΦ". iLeft. iExists _, _, _.
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iFrame.
  }

  wp_apply (wp_validInum).
  iIntros (valid) "%Hvalid".
  wp_if_destruct.
  {
    wp_apply (wp_storeField_struct with "Hreply"); first by auto. iIntros "Hreply".

    (* Simulate to get Q *)
    iApply fupd_wp.
    iInv "Hsrc" as ">Hopen" "Hclose".
    iNamed "Hopen".
    iDestruct ("Hfupd" with "[] HP") as "Hfupd".
    {
      iPureIntro.
      rewrite /SimpleNFS.full_getattr.
      case_decide as cond; try congruence.
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
    iMod ("Hclose" with "[Hsrcheap HP]").
    { iModIntro. iExists _. iFrame "∗%#". }
    iModIntro.

    wp_load.
    iApply "HΦ".
    iRight. iExists _.
    iFrame "HQ".
    iPureIntro.
    Transparent nfstypes.GETATTR3res.S.
    simpl. intuition eauto.
    Opaque nfstypes.GETATTR3res.S.
    lia.
  }

  wp_loadField.
  wp_apply (wp_LockMap__Acquire with "[$Hislm]"); first by intuition eauto.
  iIntros "Hcrashlocked".

  wp_pures.
  wp_bind (NFSPROC3_GETATTR_internal _ _ _ _).

  iDestruct (use_CrashLocked _ 8 with "Hcrashlocked") as "Hcrashuse"; first by lia.
  iApply (wpc_wp _ _ _ _ _ True).
  iApply "Hcrashuse".
  iSplit.
  { iModIntro. iModIntro. done. }
  iIntros ">Hstable".
  iNamed "Hstable".

  iMod (lift_liftable_into_txn with "Hbuftxn Hinode_disk") as "[Hinode_disk Hbuftxn]".
  { solve_ndisj. }
  { solve_ndisj. }
  { solve_ndisj. }
  iNamed "Hinode_disk".

  iNamed "Hbuftxn".

  iCache with "Hinode_state Hbuftxn_durable".
  { crash_case.
    iDestruct (is_buftxn_durable_to_old_pred with "Hbuftxn_durable") as "[Hold _]".
    iModIntro.
    iModIntro.
    iSplit; first done.
    iExists _.
    iFrame.
  }

  wpc_call.
  wpc_bind (NFSPROC3_GETATTR_wp _ _ _ _).
  wpc_frame.
  wp_call.

  wp_apply (wp_ReadInode with "[$Hbuftxn_mem $Hinode_enc]"); first by intuition eauto.
  iIntros (ip) "(Hbuftxn_mem & Hinode_enc & Hinode_mem)".

  wp_apply (wp_Inode__MkFattr with "Hinode_mem").
  iIntros (fattr3) "(Hinode_mem & % & % & %)".

  iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".

  wp_apply (wp_struct_fieldRef_mapsto with "Resok"); first done.
  iIntros (fl) "[%Hfl Resok]".
  wp_apply (wp_storeField_struct with "Resok").
  { eauto. }
  iIntros "Resok".
  rewrite Hfl; clear Hfl fl.

  iNamed 1.
  wpc_pures.

  iDestruct (is_buftxn_mem_durable with "Hbuftxn_mem Hbuftxn_durable") as "Hbuftxn".

  wpc_apply (wpc_BufTxn__CommitWait with "[$Hbuftxn Hinode_enc Hinode_data]").
  4: { (* XXX is there a clean version of this? *) generalize (buftxn_maps_to γtxn). intros. iAccu. }
  all: try solve_ndisj.
  { typeclasses eauto. }

  iSplit.
  { iModIntro. iModIntro.
    iIntros "[[H _]|[H0 H1]]"; iSplit; try done; iApply is_inode_crash_ro; iFrame "Hinode_state".
    { iLeft; iFrame. }
    { iRight; iFrame. } }

  iModIntro.
  iIntros (ok) "Hcommit".
  destruct ok; subst.
  - (* Simulate to get Q *)
    iApply fupd_wpc.
    iInv "Hsrc" as ">Hopen" "Hclose".
    iNamed "Hopen".
    iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh".
    iDestruct (big_sepM_lookup with "Hnooverflow") as %Hnooverflow; eauto.
    iDestruct ("Hfupd" with "[] HP") as "Hfupd".
    {
      iPureIntro.
      rewrite /SimpleNFS.full_getattr.
      case_decide as cond; try congruence.
      simpl.
      monad_simpl.
      rewrite /= Hsrc_fh /=.
      eapply relation.bind_runs with (x:=false). { econstructor. auto. }
      simpl.
      monad_simpl.
    }
    iMod "Hfupd" as "[HP HQ]".
    iMod ("Hclose" with "[Hsrcheap HP]").
    { iModIntro. iExists _. iFrame "∗%#". }
    iModIntro.

    wpc_frame "Hinode_state Hcommit".
    { iModIntro. iModIntro. iSplit; try done.
      iApply is_inode_crash_ro_own. iFrame "Hinode_state". iRight. iFrame. }

    wp_storeField.
    iNamed 1.

    iSplitR "Hinode_state Hcommit".
    2: {
      iModIntro.
      iExists _; iFrame.
      iExists _; iFrame.
    }
    iIntros "Hcrashlocked".
    iSplit.
    { iModIntro. done. }

    wp_loadField.
    wp_apply (wp_LockMap__Release with "Hcrashlocked").

    wp_apply (wp_LoadAt with "[Status Resok]").
    { iModIntro. iApply nfstypes_getattr3res_merge. iFrame. }
    iIntros "Hreply". simpl.
    iApply "HΦ". iLeft.
    iExists _, _, _.
Transparent nfstypes.GETATTR3res.S.
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iFrame.

  - (* Simulate to get Q *)
    iApply fupd_wpc.
    iInv "Hsrc" as ">Hopen" "Hclose".
    iNamed "Hopen".
    iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh".
    iDestruct ("Hfupd" with "[] HP") as "Hfupd".
    {
      iPureIntro.
      rewrite /SimpleNFS.full_getattr.
      case_decide as cond; try congruence.
      simpl.
      monad_simpl.
      simpl.
      rewrite Hsrc_fh.
      simpl.
      eapply relation.bind_runs with (x:=true). { econstructor. auto. }
      econstructor. auto.
    }
    iMod "Hfupd" as "[HP HQ]".
    iMod ("Hclose" with "[Hsrcheap HP]").
    { iModIntro. iExists _. iFrame "∗%#". }
    iModIntro.

    iDestruct "Hcommit" as "[Hcommit _]".
    wpc_frame "Hinode_state Hcommit".
    { iModIntro. iModIntro. iSplit; try done.
      iApply is_inode_crash_ro_own. iFrame "Hinode_state". iLeft. iFrame. }

    wp_storeField.
    iNamed 1.

    iSplitR "Hinode_state Hcommit".
    2: {
      iModIntro.
      iExists _; iFrame.
    }
    iIntros "Hcrashlocked".
    iSplit.
    { iModIntro. done. }

    wp_loadField.
    wp_apply (wp_LockMap__Release with "Hcrashlocked").

    wp_apply (wp_LoadAt with "[Status Resok]").
    { iModIntro. iApply nfstypes_getattr3res_merge. iFrame. }
    iIntros "Hreply".
    iApply "HΦ".
    iRight. iExists _. iFrame "HQ".
    iPureIntro.
    simpl. intuition eauto.
    lia.
Unshelve.
  all: eauto.
Qed.

Opaque nfstypes.WRITE3res.S.

Lemma length_1_singleton {T} (l : list T) :
  length l = 1 -> ∃ v, l = [v].
Proof.
  destruct l; simpl in *; intros; try lia.
  destruct l; simpl in *; intros; try lia.
  eexists; eauto.
Qed.

Theorem wp_Inode__WriteInode γ γtxn (inum : u64) len len' blk (l : loc) (btxn : loc) dinit γdurable :
  {{{ is_buftxn_mem Nbuftxn btxn γ.(simple_buftxn) dinit γtxn γdurable ∗
      is_inode_enc inum len blk (buftxn_maps_to γtxn) ∗
      is_inode_mem l inum len' blk ∗
      ⌜ inum ∈ covered_inodes ⌝
  }}}
    Inode__WriteInode #l #btxn
  {{{ RET #();
      is_buftxn_mem Nbuftxn btxn γ.(simple_buftxn) dinit γtxn γdurable ∗
      is_inode_enc inum len' blk (buftxn_maps_to γtxn) ∗
      is_inode_mem l inum len' blk }}}.
Proof.
  iIntros (Φ) "(Hbuftxn & Henc & Hmem & %Hcovered) HΦ".
  wp_call.
  iNamed "Hmem".
  wp_call.
  wp_apply wp_new_enc. iIntros (enc) "He".
  wp_loadField.
  wp_apply (wp_Enc__PutInt with "He"); first by word. iIntros "He".
  wp_loadField.
  wp_apply (wp_Enc__PutInt with "He"); first by word. iIntros "He".
  wp_apply (wp_Enc__Finish with "He"). iIntros (s data) "(%Hdata & %Hlen & Hs)".
  wp_loadField.
  wp_apply wp_inum2Addr.
  {
    iPureIntro.
    rewrite /covered_inodes in Hcovered.
    eapply rangeSet_lookup in Hcovered; try lia.
    rewrite /NumInodes /InodeSz. simpl. lia.
  }
  iNamed "Henc".
  iDestruct (is_slice_to_small with "Hs") as "Hs".
  wp_apply (wp_BufTxn__OverWrite
    _ _ _ _ _ _ _ _ _ _ _ (existT KindInode (bufInode (list_to_inode_buf data))) with "[$Hbuftxn $Hinode_enc_mapsto $Hs]").
  { eauto. }
  { rewrite /data_has_obj /=. apply list_to_inode_buf_to_list.
    rewrite /inode_bytes. word. }
  { eauto. }
  iIntros "[Hbuftxn Hinode_enc_mapsto]".
  wp_apply util_proof.wp_DPrintf.
  iApply "HΦ". iFrame.
  iExists _. iFrame. iPureIntro.
  rewrite /encodes_inode.
  rewrite list_to_inode_buf_to_list. 2: { rewrite /inode_bytes; word. }
  eapply Hdata.
Qed.

Theorem wp_Inode__Write γ γtxn ip inum len blk (btxn : loc) (offset : u64) (count : u64) dataslice databuf γdurable dinit contents :
  {{{ is_buftxn_mem Nbuftxn btxn γ.(simple_buftxn) dinit γtxn γdurable ∗
      is_inode_mem ip inum len blk ∗
      is_inode_enc inum len blk (buftxn_maps_to γtxn) ∗
      is_inode_data len blk contents (buftxn_maps_to γtxn) ∗
      is_slice_small dataslice u8T 1 databuf ∗
      ⌜ int.nat count = length databuf ⌝ ∗
      ⌜ inum ∈ covered_inodes ⌝
  }}}
    Inode__Write #ip #btxn #offset #count (slice_val dataslice)
  {{{ (wcount: u64) (ok: bool), RET (#wcount, #ok);
      is_buftxn_mem Nbuftxn btxn γ.(simple_buftxn) dinit γtxn γdurable ∗
      ( ( let contents' := ((firstn (int.nat offset) contents) ++
                          (firstn (int.nat count) databuf) ++
                          (skipn (int.nat offset + int.nat count) contents))%list in
        let len' := U64 (Z.max (int.Z len) (int.Z offset + int.Z count)) in
        is_inode_mem ip inum len' blk ∗
        is_inode_enc inum len' blk (buftxn_maps_to γtxn) ∗
        is_inode_data len' blk contents' (buftxn_maps_to γtxn) ∗
        ⌜ wcount = count ∧ ok = true ∧
          (int.Z offset + length databuf < 2^64)%Z ∧
          (int.Z offset ≤ int.Z len)%Z ⌝ ) ∨
      ( is_inode_mem ip inum len blk ∗
        is_inode_enc inum len blk (buftxn_maps_to γtxn) ∗
        is_inode_data len blk contents (buftxn_maps_to γtxn) ∗
        ⌜ int.Z wcount = 0 ∧ ok = false ⌝ ) )
  }}}.
Proof.
  iIntros (Φ) "(Hbuftxn & Hmem & Hienc & Hdata & Hdatabuf & %Hcount & %Hcovered) HΦ".
  wp_call.
  wp_apply util_proof.wp_DPrintf.
  wp_apply wp_slice_len.
  wp_if_destruct.
  { wp_pures. iApply "HΦ". iFrame. iRight. iFrame. done. }
  wp_apply util_proof.wp_SumOverflows.
  iIntros (ok) "%Hok". subst.
  wp_if_destruct.
  { wp_pures. iApply "HΦ". iFrame "Hbuftxn". iRight. iFrame. done. }
  wp_if_destruct.
  { wp_pures. iApply "HΦ". iFrame "Hbuftxn". iRight. iFrame. done. }
  iNamed "Hmem".
  wp_loadField.
  wp_if_destruct.
  { wp_pures. iApply "HΦ". iFrame "Hbuftxn". iRight. iFrame. done. }

  iNamed "Hdata".
  wp_loadField.
  wp_apply wp_block2addr.
  wp_apply (wp_BufTxn__ReadBuf with "[$Hbuftxn $Hdiskblk]"); first by eauto.
  iIntros (dirty bufptr) "[Hbuf Hbufdone]".

  wp_apply wp_ref_to; first by val_ty.
  iIntros (count) "Hcount".

  wp_apply (wp_forUpto (λ i,
    ∃ bbuf',
      "Hdatabuf" ∷ is_slice_small dataslice byteT 1 databuf ∗
      "Hbuf" ∷ is_buf bufptr (blk2addr blk) {|
             bufKind := objKind (existT KindBlock (bufBlock bbuf'));
             bufData := objData (existT KindBlock (bufBlock bbuf'));
             bufDirty := dirty |} ∗
      "%Hbbuf" ∷ ⌜ vec_to_list bbuf' = ((firstn (int.nat offset) (vec_to_list bbuf)) ++
                                       (firstn (int.nat i) databuf) ++
                                       (skipn (int.nat offset + int.nat i) (vec_to_list bbuf)))%list ⌝
    )%I with "[] [$Hcount Hdatabuf Hbuf]").
  { word. }
  {
    iIntros (count').
    iIntros (Φ') "!>".
    iIntros "(HI & Hcount & %Hbound) HΦ'".
    iNamed "HI".
    wp_load.
    destruct (databuf !! int.nat count') eqn:He.
    2: {
      iDestruct (is_slice_small_sz with "Hdatabuf") as "%Hlen".
      eapply lookup_ge_None_1 in He. word.
    }
    wp_apply (wp_SliceGet (V:=u8) with "[$Hdatabuf]"); eauto.
    iIntros "Hdatabuf".
    wp_load.
    wp_apply (wp_buf_loadField_data with "Hbuf").
    iIntros (bufslice) "[Hbufdata Hbufnodata]".
    assert (is_Some (vec_to_list bbuf' !! int.nat (word.add offset count'))).
    { eapply lookup_lt_is_Some_2. rewrite vec_to_list_length /block_bytes.
      revert Heqb0. word. }
    wp_apply (wp_SliceSet (V:=u8) with "[$Hbufdata]"); eauto.
    iIntros "Hbufdata".
    wp_pures.
    iApply "HΦ'". iFrame.

    assert ((int.nat (word.add offset count')) < block_bytes) as fin.
    {
      rewrite /is_Some in H.
      destruct H.
      apply lookup_lt_Some in H.
      rewrite vec_to_list_length /block_bytes in H.
      rewrite /block_bytes; lia.
    }
    iExists (vinsert (nat_to_fin fin) u bbuf'). iSplit.
    { iApply is_buf_return_data. iFrame.
      iExactEq "Hbufdata".
      rewrite /= /Block_to_vals vec_to_list_insert.
      rewrite /is_slice_small. f_equal.
      rewrite /list.untype /to_val /u8_IntoVal /b2val. f_equal. f_equal.
      erewrite fin_to_nat_to_fin. reflexivity.
    }
    iPureIntro.
    rewrite vec_to_list_insert Hbbuf.
    erewrite fin_to_nat_to_fin.
    replace (int.nat (word.add offset count')) with ((int.nat offset)+(int.nat count')).
    2: { word. }
    assert ((int.nat offset) = (length (take (int.nat offset) bbuf))) as Hoff.
    1: {
      rewrite take_length.
      rewrite vec_to_list_length.
      revert fin. word_cleanup.
    }
    rewrite -> Hoff at 1.
    rewrite insert_app_r.
    f_equal.
    replace (int.nat count') with (length (take (int.nat count') databuf) + 0) at 1.
    2: {
      rewrite take_length_le; first by lia. word.
    }
    rewrite insert_app_r.
    replace (int.nat (word.add count' 1%Z)) with (S (int.nat count')) at 1 by word.
    erewrite take_S_r; eauto.
    rewrite -app_assoc. f_equal.
    erewrite <- drop_take_drop.
    1: rewrite insert_app_l.
    1: f_equal.
    3: word.
    2: {
      rewrite drop_length.
      rewrite firstn_length_le.
      2: { rewrite vec_to_list_length. revert fin. word. }
      revert fin. word.
    }
    replace (int.nat (word.add count' 1%Z)) with (int.nat count' + 1) by word.
    rewrite plus_assoc.
    rewrite skipn_firstn_comm.
    replace (int.nat offset + int.nat count' + 1 - (int.nat offset + int.nat count')) with 1 by word.
    edestruct (length_1_singleton (T:=u8) (take 1 (drop (int.nat offset + int.nat count') bbuf))) as [x Hx].
    2: { rewrite Hx. done. }
    rewrite firstn_length_le; eauto.
    rewrite drop_length.
    rewrite vec_to_list_length.
    revert fin. word.
  }
  {
    iExists _. iFrame.
    iPureIntro.
    replace (int.nat (U64 0)) with 0 by reflexivity.
    rewrite take_0. rewrite app_nil_l.
    replace (int.nat offset + 0) with (int.nat offset) by lia.
    rewrite take_drop. done.
  }

  iIntros "(HI & Hcount)".
  iNamed "HI".
  wp_apply (wp_Buf__SetDirty with "Hbuf"). iIntros "Hbuf".

  iMod ("Hbufdone" with "Hbuf []") as "[Hbuftxn Hdiskblk]".
  { iLeft. done. }

  wp_apply util_proof.wp_DPrintf.
  wp_loadField.

  assert (take (int.nat offset) contents =
          take (int.nat offset) bbuf) as Hcontents0.
  { rewrite -Hdiskdata.
    rewrite take_take. f_equal. lia. }

  assert (drop (int.nat offset + int.nat dataslice.(Slice.sz)) contents =
          drop (int.nat offset + int.nat dataslice.(Slice.sz)) (take (length contents) bbuf))
    as Hcontents1.
  { congruence. }

  assert ( (drop (int.nat offset + int.nat dataslice.(Slice.sz)) bbuf) =
           (drop (int.nat offset + int.nat dataslice.(Slice.sz))
                 (take (length contents) bbuf ++ (drop (length contents) bbuf))))
     as Hbuf.
  { rewrite take_drop; done. }

  assert (length contents ≤ length bbuf) as Hlencontents.
  { eapply (f_equal length) in Hdiskdata.
    rewrite take_length in Hdiskdata. lia. }

  wp_if_destruct.
  { wp_storeField.
    wp_apply (wp_Inode__WriteInode with "[$Hbuftxn Hinum Hisize Hidata $Hienc]").
    { iFrame. iFrame "%". }
    iIntros "(Hbuftxn & Hienc & Hmem)".
    wp_pures.
    iApply "HΦ". iFrame "Hbuftxn". iLeft.
    rewrite Z.max_r.
    2: { revert Heqb2. word. }
    iFrame.
    iSplit.
    2: {
      iPureIntro. intuition eauto.
      { rewrite -Hcount; word. }
      lia.
    }
    iExists _. iFrame. iPureIntro.
    rewrite Hbbuf. rewrite Hcontents0 Hcontents1.
    rewrite !app_length.
    rewrite drop_length.
    rewrite take_length_le; last by ( rewrite vec_to_list_length /block_bytes; word ).
    rewrite take_length_le; last by ( rewrite Hcount; lia ).
    rewrite take_length_le; last by ( rewrite vec_to_list_length /block_bytes; word ).
    replace (length contents) with (int.nat len) by word.
    split. 2: { revert Heqb2. word. }
    rewrite app_assoc. rewrite take_app_le.
    2: {
      rewrite !app_length.
      rewrite take_length_le. 2: rewrite vec_to_list_length /block_bytes; word.
      rewrite take_length_le. 2: rewrite Hcount; lia.
      revert Heqb2. word.
    }
    rewrite firstn_all2.
    2: {
      rewrite !app_length.
      rewrite take_length_le. 2: rewrite vec_to_list_length /block_bytes; word.
      rewrite take_length_le. 2: rewrite Hcount; lia.
      revert Heqb2. word.
    }
    f_equal. rewrite drop_ge. 1: rewrite app_nil_r; eauto.
    rewrite take_length_le. 2: rewrite vec_to_list_length /block_bytes; word.
    rewrite Hcount. revert Heqb2. word.
  }
  { wp_pures.
    iApply "HΦ". iFrame "Hbuftxn". iLeft.
    rewrite Z.max_l.
    2: { revert Heqb2. word. }
    replace (U64 (int.Z len)) with (len) by word.
    iFrame.
    iSplit.
    2: {
      iPureIntro. intuition eauto.
      { rewrite -Hcount; word. }
      lia.
    }
    iExists _. iFrame. iPureIntro.
    rewrite Hbbuf. rewrite Hcontents0 Hcontents1 Hbuf.
    rewrite !app_length.
    rewrite drop_length.
    rewrite take_length_le. 2: { rewrite vec_to_list_length /block_bytes. revert Heqb0; word. }
    rewrite take_length_le. 2: { rewrite Hcount; lia. }
    rewrite take_length_le. 2: { lia. }
    replace (length contents) with (int.nat len) by word.
    split. 2: { revert Heqb2. word. }
    rewrite drop_app_le.
    2: {
      rewrite take_length_le. 2: lia.
      revert Heqb2. word.
    }
    rewrite app_assoc. rewrite app_assoc. rewrite take_app_le.
    2: {
      rewrite !app_length.
      rewrite drop_length.
      rewrite take_length_le. 2: lia.
      rewrite take_length_le. 2: rewrite Hcount; lia.
      rewrite take_length_le. 2: lia.
      revert Heqb2. word.
    }
    rewrite firstn_all2.
    1: { rewrite app_assoc; eauto. }

    rewrite !app_length.
    rewrite drop_length.
    rewrite take_length_le. 2: lia.
    rewrite take_length_le. 2: rewrite Hcount; lia.
    rewrite take_length_le. 2: lia.
    revert Heqb2. word.
  }
Qed.

Lemma nfstypes_write3res_merge reply s ok fail :
  ( reply ↦[nfstypes.WRITE3res.S :: "Status"] s ∗
    reply ↦[nfstypes.WRITE3res.S :: "Resok"] ok ∗ 
    reply ↦[nfstypes.WRITE3res.S :: "Resfail"] fail ) -∗
  reply ↦[struct.t nfstypes.WRITE3res.S]{1} (s, (ok, (fail, #()))).
Proof.
  iIntros "(Status & Resok & Resfail)".
  iApply struct_fields_split. iFrame. done.
Qed.

Theorem wp_NFSPROC3_WRITE γ (nfs : loc) (fh : u64) (fhslice : Slice.t) (offset : u64) (dataslice : Slice.t) (databuf : list u8) (Q : SimpleNFS.res u32 -> iProp Σ) (stab : u32) dinit :
  {{{ is_fs γ nfs dinit ∗
      is_fh fhslice fh ∗
      is_slice dataslice u8T 1%Qp databuf ∗
      ⌜ (length databuf < 2^32)%Z ⌝ ∗
      ∀ σ σ' (r : SimpleNFS.res u32) E,
        ⌜relation.denote (SimpleNFS.wrapper fh (SimpleNFS.write fh offset databuf)) σ σ' r⌝ -∗
        ( P σ ={E}=∗ P σ' ∗ Q r )
  }}}
    Nfs__NFSPROC3_WRITE #nfs
      (struct.mk_f nfstypes.WRITE3args.S [
        "File" ::= struct.mk_f nfstypes.Nfs_fh3.S [
          "Data" ::= slice_val fhslice
        ];
        "Offset" ::= #offset;
        "Count" ::= #(U32 (length databuf));
        "Stable" ::= #stab;
        "Data" ::= (slice_val dataslice)
      ])%V
  {{{ v,
      RET v;
      ( ∃ (count : u32) resok,
        ⌜ getField_f nfstypes.WRITE3res.S "Status" v = #(U32 0) ⌝ ∗
        ⌜ getField_f nfstypes.WRITE3res.S "Resok" v = resok ⌝ ∗
        ⌜ getField_f nfstypes.WRITE3resok.S "Count" resok = #count ⌝ ∗
        Q (SimpleNFS.OK count) ) ∨
      ( ∃ (stat : Z),
        ⌜ getField_f nfstypes.WRITE3res.S "Status" v = #(U32 stat) ⌝ ∗
        ⌜ stat ≠ 0 ⌝ ∗
        Q SimpleNFS.Err )
  }}}.
Proof using Ptimeless.
  iIntros (Φ) "(Hfs & #Hfh & Hdata & %Hdatalenbound & Hfupd) HΦ".
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
  wp_apply util_proof.wp_DPrintf.
  wp_apply (wp_validInum).
  iIntros (valid) "%Hvalid".
  wp_if_destruct.
  { wp_apply (wp_storeField_struct with "Hreply"); first by auto.
    iIntros "Hreply".

    (* Simulate to get Q *)
    iApply fupd_wp.
    iInv "Hsrc" as ">Hopen" "Hclose".
    iNamed "Hopen".
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
    iMod ("Hclose" with "[Hsrcheap HP]").
    { iModIntro. iExists _. iFrame "∗%#". }
    iModIntro.

    wp_load.
    iApply "HΦ".
    iRight. iExists _.
    iFrame "HQ".
    iPureIntro.
    simpl. intuition eauto.
    lia.
  }

  wp_loadField.
  wp_apply (wp_LockMap__Acquire with "[$Hislm]"); first by intuition eauto.
  iIntros "Hcrashlocked".

  wp_pures.
  wp_bind (NFSPROC3_WRITE_internal _ _ _ _).

  iDestruct (use_CrashLocked _ 8 with "Hcrashlocked") as "Hcrashuse"; first by lia.
  iApply (wpc_wp _ _ _ _ _ True).
  iApply "Hcrashuse".
  iSplit.
  { iModIntro. iModIntro. done. }
  iIntros ">Hstable".
  iNamed "Hstable".

  iMod (lift_liftable_into_txn with "Hbuftxn Hinode_disk") as "[Hinode_disk Hbuftxn]";
    [ solve_ndisj .. | ].
  iNamed "Hinode_disk".

  iNamed "Hbuftxn".

  iCache with "Hinode_state Hbuftxn_durable".
  { crash_case.
    iDestruct (is_buftxn_durable_to_old_pred with "Hbuftxn_durable") as "[Hold _]".
    iModIntro.
    iModIntro.
    iSplit; first done.
    iExists _.
    iFrame.
  }

  wpc_call.
  wpc_bind (NFSPROC3_WRITE_wp _ _ _ _).
  wpc_frame.
  wp_call.

  wp_apply (wp_ReadInode with "[$Hbuftxn_mem $Hinode_enc]"); first by intuition eauto.
  iIntros (ip) "(Hbuftxn_mem & Hinode_enc & Hinode_mem)".

  wp_apply (wp_Inode__Write with "[$Hbuftxn_mem $Hinode_mem $Hinode_data $Hinode_enc Hdata]").
  { iDestruct (is_slice_to_small with "Hdata") as "$".
    iPureIntro. intuition eauto.
    rewrite /u32_to_u64. word.
  }

  iIntros (wcount ok) "[Hbuftxn_mem [(Hinode_mem & Hinode_enc & Hinode_data & %Hok) | Hok]]"; intuition subst.
  {
    wp_pures.

    iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".

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

    wp_pures.
    iNamed 1.
    wpc_pures.

    iDestruct (is_buftxn_mem_durable with "Hbuftxn_mem Hbuftxn_durable") as "Hbuftxn".

    iApply fupd_wpc.
    iInv "Hsrc" as ">Hopen" "Hclose".
    iNamed "Hopen".
    iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh".
    iDestruct (big_sepM_lookup with "Hnooverflow") as %Hnooverflow; eauto.
    iMod ("Hclose" with "[Hsrcheap HP]").
    { iModIntro. iExists _. iFrame "∗%#". }
    iModIntro. iClear "Hnooverflow".

    replace (int.Z (length state)
              `max` (int.Z offset + int.Z (u32_to_u64 (U32 (length databuf)))))%Z
      with (length (take (int.nat offset) state ++
                    databuf ++ drop (int.nat offset + length databuf) state) : Z).
    2: {
      rewrite /u32_to_u64. word_cleanup.
      destruct (decide (int.Z offset + length databuf ≤ length state)%Z).
      { rewrite Z.max_l; last by lia.
        rewrite !app_length. rewrite drop_length.
        rewrite take_length_le; lia. }
      { rewrite Z.max_r; last by lia.
        rewrite !app_length. rewrite drop_length.
        rewrite take_length_le; try lia.
        revert H3. word. }
    }
    rewrite /u32_to_u64. word_cleanup.
    rewrite (firstn_all2 databuf); last by lia.
    replace (Z.to_nat (length databuf)) with (length databuf) by lia.

  wpc_apply (wpc_strong_mono _ _ _ _ _ _ _ _ _
    (is_inode_crash γ fh ∨
     is_inode_unstable γ fh state (take (int.nat offset) state ++
          databuf ++ drop (int.nat offset + length databuf) state)
    ) with "[-]").
  5: iSplit.
  5: {
    iIntros (v) "HΦ".
    iModIntro. iExact "HΦ".
  }
  5: {
    iModIntro. iIntros ">Hpre C".
    iDestruct "Hpre" as "[Hpre | Hpre]".
    { iModIntro. iFrame. }
    iNamed "Hpre".

    (* XXX how to update [Hinode_state] here? *)
    admit.

    (* To update [Hinode_state], something like this should work: *)

    (*
      iApply fupd_wpc.
      iInv "Hsrc" as ">Hopen" "Hclose".
      iNamed "Hopen".
      iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh2".
      iDestruct ("Hfupd" with "[] HP") as "Hfupd".
      {
        iPureIntro.
        simpl.
        monad_simpl.
        simpl.
        rewrite Hsrc_fh2.
        simpl.
        eapply relation.bind_runs with (x:=false). { econstructor. auto. }
        simpl.
        monad_simpl.
        econstructor. { econstructor. revert H3. word. }
        monad_simpl.
      }
      iMod (map_update with "Hsrcheap Hinode_state") as "[Hsrcheap Hinode_state]".
      iMod "Hfupd" as "[HP HQ]".
      iMod ("Hclose" with "[Hsrcheap HP]").
      { iModIntro. iExists _. iFrame "∗%#". iSplit.
        { iPureIntro. rewrite /= dom_insert_L. set_solver+ Hdom0 H5. }
        iDestruct (big_sepM_delete with "Hnooverflow") as "[H0 H1]"; eauto.
        iApply (big_sepM_insert_delete with "[$H1]").
        iPureIntro.
        rewrite !app_length drop_length.
        rewrite take_length_le.
        2: { revert H3. word. }
        lia.
      }
      iModIntro.
    *)
  }

  4: {
    wpc_apply (wpc_BufTxn__CommitWait with "[$Hbuftxn Hinode_enc Hinode_data]").
    4: { (* XXX is there a clean version of this? *) generalize (buftxn_maps_to γtxn). intros. iAccu. }
    all: try solve_ndisj.
    { typeclasses eauto. }

    iSplit.
    { iModIntro. iModIntro.
      iIntros "[[H _]|[H0 H1]]".
      { iLeft. iApply is_inode_crash_ro. iFrame. }
      { iRight. iFrame. iExists _. iFrame. }
    }

    iModIntro.
    iIntros (ok) "Hcommit".
    destruct ok; subst.
    { (* Simulate to get Q *)
      iApply fupd_wpc.
      iInv "Hsrc" as ">Hopen" "Hclose".
      iNamed "Hopen".
      iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh2".
      iDestruct ("Hfupd" with "[] HP") as "Hfupd".
      {
        iPureIntro.
        simpl.
        monad_simpl.
        simpl.
        rewrite Hsrc_fh2.
        simpl.
        eapply relation.bind_runs with (x:=false). { econstructor. auto. }
        simpl.
        monad_simpl.
        econstructor. { econstructor. revert H3. word. }
        monad_simpl.
      }
      iMod (map_update with "Hsrcheap Hinode_state") as "[Hsrcheap Hinode_state]".
      iMod "Hfupd" as "[HP HQ]".
      iMod ("Hclose" with "[Hsrcheap HP]").
      { iModIntro. iExists _. iFrame "∗%#". iSplit.
        { iPureIntro. rewrite /= dom_insert_L. set_solver+ Hdom0 H5. }
        iDestruct (big_sepM_delete with "Hnooverflow") as "[H0 H1]"; eauto.
        iApply (big_sepM_insert_delete with "[$H1]").
        iPureIntro.
        rewrite !app_length drop_length.
        rewrite take_length_le.
        2: { revert H3. word. }
        lia.
      }
      iModIntro.

      wpc_frame "Hinode_state Hcommit".
      { iModIntro. iModIntro. iLeft.
        iApply is_inode_crash_ro_own. iFrame. }

      wp_storeField.
      iNamed 1.

      iSplitR "Hinode_state Hcommit".
      2: {
        iModIntro.
        iExists _. iFrame "Hinode_state".
        iDestruct "Hcommit" as "(Hinode_enc & Hinode_data)".
        iExists _. iFrame.
      }
      iIntros "Hcrashlocked".
      iSplit.
      { iModIntro. done. }

      wp_loadField.
      wp_apply (wp_LockMap__Release with "Hcrashlocked").

      wp_apply (wp_LoadAt with "[Status Resok Resfail]").
      { iModIntro. iApply nfstypes_write3res_merge. iFrame. }
      iIntros "Hreply". simpl.
      iApply "HΦ". iLeft.
      iExists _, _.
      iSplit; first done.
      iSplit; first done.
      iSplit; first done.
      iExactEq "HQ".
      f_equal. f_equal. rewrite /u32_from_u64 /u32_to_u64. word.
    }

    { (* Simulate to get Q *)
      iApply fupd_wpc.
      iInv "Hsrc" as ">Hopen" "Hclose".
      iNamed "Hopen".
      iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh2".
      iDestruct ("Hfupd" with "[] HP") as "Hfupd".
      {
        iPureIntro.
        simpl.
        monad_simpl.
        simpl.
        rewrite Hsrc_fh2.
        simpl.
        eapply relation.bind_runs with (x:=true). { econstructor. auto. }
        simpl.
        monad_simpl.
      }
      iMod "Hfupd" as "[HP HQ]".
      iMod ("Hclose" with "[Hsrcheap HP]").
      { iModIntro. iExists _. iFrame "∗%#". }
      iModIntro.

      iDestruct "Hcommit" as "[Hcommit _]".
      wpc_frame "Hinode_state Hcommit".
      { iModIntro. iModIntro. iLeft.
        iApply is_inode_crash_ro_own. iFrame. }

      wp_storeField.
      iNamed 1.

      iSplitR "Hinode_state Hcommit".
      2: {
        iModIntro.
        iExists _; iFrame.
      }
      iIntros "Hcrashlocked".
      iSplit.
      { iModIntro. done. }

      wp_loadField.
      wp_apply (wp_LockMap__Release with "Hcrashlocked").

      wp_apply (wp_LoadAt with "[Status Resok Resfail]").
      { iModIntro. iApply nfstypes_write3res_merge. iFrame. }
      iIntros "Hreply". simpl.
      iApply "HΦ". iRight.
      iExists _.
      iSplit; first done.
      iFrame.
      iPureIntro. lia.
    }
  }

  1: eauto.
  2: set_solver.
  1: shelve.
  }

  {
    iDestruct "Hok" as "(Hinode_mem & Hinode_enc & Hinode_data & %Hok)". intuition subst.
    iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".
    wp_storeField.
    iNamed 1.

    iDestruct (is_buftxn_mem_durable with "Hbuftxn_mem Hbuftxn_durable") as "Hbuftxn".

    (* Implicit transaction abort *)
    iDestruct (is_buftxn_to_old_pred with "Hbuftxn") as "[Hold _]".

    (* Simulate to get Q *)
    iApply fupd_wpc.
    iInv "Hsrc" as ">Hopen" "Hclose".
    iNamed "Hopen".
    iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh".
    iDestruct ("Hfupd" with "[] HP") as "Hfupd".
    {
      iPureIntro.
      simpl.
      monad_simpl.
      simpl.
      rewrite Hsrc_fh.
      simpl.
      eapply relation.bind_runs with (x:=true). { econstructor. auto. }
      simpl.
      monad_simpl.
    }
    iMod "Hfupd" as "[HP HQ]".
    iMod ("Hclose" with "[Hsrcheap HP]").
    { iModIntro. iExists _. iFrame "∗%#". }
    iModIntro.

    wpc_pures.
    { iModIntro. iModIntro. iSplit; try done.
      iApply is_inode_crash_ro_own; iFrame "Hinode_state". iLeft; iFrame. }

    iSplitR "Hinode_state Hold".
    2: {
      iModIntro.
      iExists _; iFrame.
    }
    iIntros "Hcrashlocked".
    iSplit.
    { iModIntro. done. }

    wp_loadField.
    wp_apply (wp_LockMap__Release with "Hcrashlocked").

    wp_apply (wp_LoadAt with "[Status Resok Resfail]").
    { iModIntro. iApply nfstypes_write3res_merge. iFrame. }
    iIntros "Hreply". simpl.
    iApply "HΦ". iRight.
    iExists _.
    iSplit; first done.
    iFrame.
    iPureIntro. lia.
  }

Unshelve.
  all: eauto.
  exact tt.
Admitted.

Lemma is_inode_data_shrink: forall state blk (u: u64) M,
   ¬ (int.Z (length state) < int.Z u)%Z ->
  is_inode_data (length state) blk state M -∗
  is_inode_data (length (take (int.nat u) state)) blk (take (int.nat u) state) M.
Proof.
  iIntros (state blk u γtxn) "%H Hinode_data".
  iNamed "Hinode_data".
  rewrite /is_inode_data.
  iExists bbuf.
  iFrame.
  iPureIntro.
  rewrite -> firstn_length_le by lia.
  split; [ | word ].
  rewrite <- Hdiskdata.
  rewrite take_take.
  auto with f_equal lia.
Qed.

Opaque nfstypes.SETATTR3res.S.

Lemma nfstypes_setattr3res_merge reply s ok fail :
  ( reply ↦[nfstypes.SETATTR3res.S :: "Status"] s ∗
    reply ↦[nfstypes.SETATTR3res.S :: "Resok"] ok ∗ 
    reply ↦[nfstypes.SETATTR3res.S :: "Resfail"] fail ) -∗
  reply ↦[struct.t nfstypes.SETATTR3res.S]{1} (s, (ok, (fail, #()))).
Proof.
  iIntros "(Status & Resok & Resfail)".
  iApply struct_fields_split. iFrame. done.
Qed.

Theorem wp_NFSPROC3_SETATTR γ (nfs : loc) (fh : u64) (fhslice : Slice.t) (sattr: SimpleNFS.sattr) (Q : SimpleNFS.res unit -> iProp Σ) dinit :
  {{{ is_fs γ nfs dinit ∗
      is_fh fhslice fh ∗
      ∀ σ σ' (r : SimpleNFS.res unit) E,
        ⌜relation.denote (SimpleNFS.wrapper fh (SimpleNFS.setattr fh sattr)) σ σ' r⌝ -∗
        ( P σ ={E}=∗ P σ' ∗ Q r )
  }}}
    Nfs__NFSPROC3_SETATTR #nfs
      (struct.mk_f nfstypes.SETATTR3args.S [
        "Object" ::= struct.mk_f nfstypes.Nfs_fh3.S [
          "Data" ::= slice_val fhslice
        ];
        "New_attributes" ::= struct.mk_f nfstypes.Sattr3.S [
          "Size" ::= struct.mk_f nfstypes.Set_size3.S [
            "Set_it" ::= match sattr.(SimpleNFS.sattr_size) with | None => #false | Some _ => #true end;
            "Size" ::= match sattr.(SimpleNFS.sattr_size) with | None => #0 | Some s => #s end
          ]
        ]
      ])%V
  {{{ v,
      RET v;
      ( ⌜ getField_f nfstypes.SETATTR3res.S "Status" v = #(U32 0) ⌝ ∗
        Q (SimpleNFS.OK tt) ) ∨
      ( ∃ stat,
        ⌜ getField_f nfstypes.SETATTR3res.S "Status" v = #(U32 stat) ⌝ ∗
        ⌜ stat ≠ 0 ⌝ ∗
        Q SimpleNFS.Err )
  }}}.
Proof using Ptimeless.
  iIntros (Φ) "(Hfs & #Hfh & Hfupd) HΦ".
  iNamed "Hfs".

  wp_call.
  iFreeze "HΦ".
  wp_apply wp_ref_of_zero; first by auto.
  iIntros (reply) "Hreply".
  wp_apply util_proof.wp_DPrintf.
  wp_loadField.
  wp_apply (wp_BufTxn__Begin with "[$Histxn $Htxnsys]").
  iIntros (γtxn buftx) "Hbuftxn".

  wp_apply (wp_fh2ino with "Hfh").
  wp_pures.
  wp_apply util_proof.wp_DPrintf.
  wp_apply (wp_validInum).
  iIntros (valid) "%Hvalid".
  wp_if_destruct.
  { wp_apply (wp_storeField_struct with "Hreply"); first by auto.
    iIntros "Hreply".

    (* Simulate to get Q *)
    iApply fupd_wp.
    iInv "Hsrc" as ">Hopen" "Hclose".
    iNamed "Hopen".
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
    iMod ("Hclose" with "[Hsrcheap HP]").
    { iModIntro. iExists _. iFrame "∗%#". }
    iModIntro.

    wp_load.
    iThaw "HΦ".
    iApply "HΦ".
    iRight. iExists _.
    iFrame "HQ".
    iPureIntro.
    simpl. intuition eauto.
    lia.
  }

  wp_loadField.
  wp_apply (wp_LockMap__Acquire with "[$Hislm]"); first by intuition eauto.
  iIntros "Hcrashlocked".

  wp_pures.
  wp_bind (NFSPROC3_SETATTR_internal _ _ _ _).

  iDestruct (use_CrashLocked _ 8 with "Hcrashlocked") as "Hcrashuse"; first by lia.
  iApply (wpc_wp _ _ _ _ _ True).
  iApply "Hcrashuse".
  iSplit.
  { iModIntro. iModIntro. done. }
  iIntros ">Hstable".
  iNamed "Hstable".

  iMod (lift_liftable_into_txn with "Hbuftxn Hinode_disk") as "[Hinode_disk Hbuftxn]";
    [ solve_ndisj .. | ].
  iNamed "Hinode_disk".

  iNamed "Hbuftxn".

  iCache with "Hinode_state Hbuftxn_durable".
  { crash_case.
    iDestruct (is_buftxn_durable_to_old_pred with "Hbuftxn_durable") as "[Hold _]".
    iModIntro.
    iModIntro.
    iSplit; first done.
    iExists _.
    iFrame.
  }

  wpc_call.
  wpc_bind (NFSPROC3_SETATTR_wp _ _ _ _).
  wpc_frame.
  wp_call.

  wp_apply (wp_ReadInode with "[$Hbuftxn_mem $Hinode_enc]"); first by intuition eauto.
  iIntros (ip) "(Hbuftxn_mem & Hinode_enc & Hinode_mem)".

  wp_apply (typed_mem.wp_AllocAt); eauto.
  iIntros (wpok) "Hwpok".

  wp_pures.
  destruct sattr.
  destruct sattr_size; wp_if.
  {
    wp_pures.
    iNamed "Hinode_mem".
    wp_loadField.
    wp_if_destruct.
    {
      wp_loadField.
      wp_apply (wp_NewSlice (V:=u8)).
      iIntros (zeros) "Hzeros".
      wp_loadField. wp_loadField.

      wp_apply (wp_Inode__Write with "[$Hbuftxn_mem $Hinum $Hisize $Hidata $Hinode_data $Hinode_enc Hzeros]").
      { iDestruct (is_slice_to_small with "Hzeros") as "$".
        iPureIntro. intuition eauto.
        rewrite replicate_length. done.
      }

      iIntros (wcount ok) "[Hbuftxn_mem [(Hinode_mem & Hinode_enc & Hinode_data & %Hok) | Hok]]"; intuition subst.
      {
        iNamed "Hinode_mem".
        wp_loadField.
        wp_pures.

        wp_if_destruct.
        {
          (* XXX should be possible to prove this case is not reachable,
              because if ip.Write() succeeded, it will give us the right
              length.. *)

          iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".
          wp_storeField.

          (* Simulate to get Q after write failed *)
          iApply fupd_wp.
          iInv "Hsrc" as ">Hopen" "Hclose".
          iNamed "Hopen".
          iDestruct ("Hfupd" with "[] HP") as "Hfupd".
          {
            iPureIntro.
            simpl.
            monad_simpl.
            simpl.
            destruct (src !! fh) eqn:He.
            {
              rewrite He.
              eapply relation.bind_runs with (x:=true). { econstructor. auto. }
              simpl.
              monad_simpl.
            }
            rewrite He.
            econstructor. eauto.
          }
          iMod "Hfupd" as "[HP HQ]".
          iMod ("Hclose" with "[Hsrcheap HP]").
          { iModIntro. iExists _. iFrame "∗%#". }
          iModIntro.

          wp_load.

          iNamed 1.
          wpc_pures.

          (* Implicit transaction abort *)
          iDestruct (is_buftxn_mem_durable with "Hbuftxn_mem Hbuftxn_durable") as "Hbuftxn".
          iDestruct (is_buftxn_to_old_pred with "Hbuftxn") as "[Hold _]".

          iSplitR "Hinode_state Hold".
          2: { iModIntro. iExists _. iFrame. }
          iIntros "Hcrashlocked".
          iSplit.
          { iModIntro. done. }

          wp_loadField.
          wp_apply (wp_LockMap__Release with "Hcrashlocked").
          wp_apply (wp_LoadAt with "[Status Resok Resfail]").
          { iModIntro. iApply nfstypes_setattr3res_merge. iFrame. }
          iIntros "Hreply". simpl.
          iThaw "HΦ".
          iApply "HΦ". iRight.
          iExists _.
          iSplit; first done.
          iFrame.
          iPureIntro. lia.
        }

        {
          wp_store.
          wp_load.

          iNamed 1.
          wpc_pures.
          iDestruct (is_buftxn_mem_durable with "Hbuftxn_mem Hbuftxn_durable") as "Hbuftxn".

          (* XXX need joe's help to figure out how to do a [fupd] on [Hinode_state] at crash time *)
(*
          wp_apply (wp_BufTxn__CommitWait with "[$Hbuftxn Hinode_enc Hinode_data]").
          4: { (* XXX is there a clean version of this? *) generalize (buftxn_maps_to γtxn). intros. iAccu. }
          all: try solve_ndisj.
          { typeclasses eauto. }

          iIntros (ok) "Hcommit".
          wp_if_destruct.
          {
            iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".
            wp_storeField.
            wp_pures.

            (* Simulate to get Q, write succeeded *)
            iApply fupd_wp.
            iInv "Hsrc" as ">Hopen" "Hclose".
            iNamed "Hopen".
            iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh".
            iDestruct (big_sepM_lookup with "Hnooverflow") as %Hnooverflow; eauto.
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
            iMod (map_update with "Hsrcheap Hinode_state") as "[Hsrcheap Hinode_state]".
            iMod "Hfupd" as "[HP HQ]".
            iMod ("Hclose" with "[Hsrcheap HP]").
            { iModIntro. iExists _.  iFrame "∗%#". iSplit.
              { iPureIntro. rewrite /= dom_insert_L. set_solver+ Hdom H5. }
              iDestruct (big_sepM_delete with "Hnooverflow") as "[H0 H1]"; eauto.
              iApply (big_sepM_insert_delete with "[$H1]").
              iPureIntro.
              rewrite app_length replicate_length.
              rewrite replicate_length in H0.
              rewrite take_length_ge.
              2: { revert Heqb. word. }
              revert H0.
              word.
            }

            iModIntro.
            wp_loadField.
            wp_apply (wp_LockMap__Release with "[$Hislm $Hlocked Hinode_state Hcommit]").
            { iExists _. iFrame.
              iDestruct "Hcommit" as "(Hinode_enc & Hinode_data)".
              iExists _.

              assert (length state < int.Z u)%Z by (revert Heqb; word).
              rewrite -> Z.max_r in Heqb0 by word.
              rewrite -Heqb0. word_cleanup.
              rewrite -> Z.max_r by word.
              rewrite !app_length !replicate_length take_length_ge.
              2: word.
              replace (length state + (int.Z u - length state))%Z with (int.Z u) by lia.
              replace (length state + (int.Z u - length state))%Z with (int.Z u) by lia.
              replace (length state + (int.nat u - length state)) with (int.nat u) by lia.
              replace (U64 (int.nat u)) with (U64 (int.Z u)) by word. iFrame.
              replace (Z.to_nat (length state)) with (length state) by lia.
              rewrite firstn_all. rewrite (firstn_all2 state); last by lia.
              rewrite drop_ge; last by lia. rewrite app_nil_r.
              rewrite firstn_all2. 2: rewrite replicate_length; lia.
              replace (Z.to_nat (int.Z u - length state)) with (int.nat u - length state) by lia.
              iFrame.
            }

            wp_apply (wp_LoadAt with "[Status Resok Resfail]").

            { iModIntro. iApply nfstypes_setattr3res_merge. iFrame. }
            iIntros "Hreply". simpl.
            iThaw "HΦ".
            iApply "HΦ". iLeft.
            iSplit; first done.
            iExactEq "HQ".
            f_equal.
          }

          {
            iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".
            wp_storeField.

            (* Simulate to get Q *)
            iApply fupd_wp.
            iInv "Hsrc" as ">Hopen" "Hclose".
            iNamed "Hopen".
            iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh".
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
            iMod ("Hclose" with "[Hsrcheap HP]").
            { iModIntro. iExists _. iFrame "∗%#". }
            iModIntro.

            wp_loadField.
            wp_apply (wp_LockMap__Release with "[$Hislm $Hlocked Hinode_state Hcommit]").
            { iExists _. iFrame.
              iDestruct "Hcommit" as "(Hinode & _)". iFrame. }

            wp_apply (wp_LoadAt with "[Status Resok Resfail]").
            { iModIntro. iApply nfstypes_setattr3res_merge. iFrame. }
            iIntros "Hreply". simpl.
            iThaw "HΦ".
            iApply "HΦ". iRight.
            iExists _.
            iSplit; first done.
            iFrame.
            iPureIntro. lia.
          }
*)
          admit.
        }
      }

      {
        iDestruct "Hok" as "(Hinode_mem & Hinode_enc & Hinode_data & %Hok)". intuition subst.
        iNamed "Hinode_mem".
        wp_loadField.
        wp_if_destruct.
        2: lia.

        iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".
        wp_storeField.

        (* Simulate to get Q after write failed *)
        iApply fupd_wp.
        iInv "Hsrc" as ">Hopen" "Hclose".
        iNamed "Hopen".
        iDestruct ("Hfupd" with "[] HP") as "Hfupd".
        {
          iPureIntro.
          simpl.
          monad_simpl.
          simpl.
          destruct (src !! fh) eqn:He.
          {
            rewrite He.
            eapply relation.bind_runs with (x:=true). { econstructor. auto. }
            simpl.
            monad_simpl.
          }
          rewrite He.
          econstructor. eauto.
        }
        iMod "Hfupd" as "[HP HQ]".
        iMod ("Hclose" with "[Hsrcheap HP]").
        { iModIntro. iExists _. iFrame "∗%#". }
        iModIntro.

        wp_load.

        iNamed 1.
        wpc_pures.

        (* Implicit transaction abort *)
        iDestruct (is_buftxn_mem_durable with "Hbuftxn_mem Hbuftxn_durable") as "Hbuftxn".
        iDestruct (is_buftxn_to_old_pred with "Hbuftxn") as "[Hold _]".

        iSplitR "Hinode_state Hold".
        2: { iModIntro. iExists _. iFrame. }
        iIntros "Hcrashlocked".
        iSplit.
        { iModIntro. done. }

        wp_loadField.
        wp_apply (wp_LockMap__Release with "Hcrashlocked").
        wp_apply (wp_LoadAt with "[Status Resok Resfail]").
        { iModIntro. iApply nfstypes_setattr3res_merge. iFrame. }
        iIntros "Hreply". simpl.
        iThaw "HΦ".
        iApply "HΦ". iRight.
        iExists _.
        iSplit; first done.
        iFrame.
        iPureIntro. lia.
      }
    }
    {
      (* shrink inode *)
      wp_storeField.
      wp_apply (wp_Inode__WriteInode with "[$Hbuftxn_mem Hinum Hisize Hidata $Hinode_enc]").
      { iFrame. iPureIntro. apply Hvalid; auto. }
      iIntros "(Hbuftxn_mem & Hinode_enc & Hinode_mem)".
      wp_pures.
      wp_store.
      wp_load.

      iNamed 1.
      wpc_pures.

      admit.
      (* XXX need to [fupd] to make the crash condition work out. *)
(*
      iDestruct (is_buftxn_mem_durable with "Hbuftxn_mem Hbuftxn_durable") as "Hbuftxn".

      wp_apply (wp_BufTxn__CommitWait with "[$Hbuftxn Hinode_enc Hinode_data]").
      4: { (* XXX is there a clean version of this? *) generalize (buftxn_maps_to γtxn). intros. iAccu. }
      { typeclasses eauto. }
      all: try solve_ndisj.

      iIntros (ok) "Hcommit".
      wp_if_destruct.
      {
        iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".
        wp_storeField.
        wp_pures.

        (* Simulate to get Q, commit succeeded *)
        iApply fupd_wp.
        iInv "Hsrc" as ">Hopen" "Hclose".
        iNamed "Hopen".
        iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh".
        iDestruct (big_sepM_lookup with "Hnooverflow") as %Hnooverflow; eauto.
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

        iMod (map_update with "Hsrcheap Hinode_state") as "[Hsrcheap Hinode_state]".
        iMod "Hfupd" as "[HP HQ]".

        assert (int.nat u - length state = 0).
        1: { revert Heqb. word. }
        rewrite H.
        rewrite replicate_0.
        rewrite app_nil_r.
                
        iMod ("Hclose" with "[Hsrcheap HP]").
        { iModIntro. iExists _.  iFrame "∗%#". iSplit.
            { iPureIntro. rewrite /= dom_insert_L. set_solver+ Hdom Hvalid. }
            iDestruct (big_sepM_delete with "Hnooverflow") as "[H0 H1]"; eauto.
            iApply (big_sepM_insert_delete with "[$H1]").
            iPureIntro.
            rewrite firstn_length_le.
            all: word.
          }
          {
            iModIntro.
            wp_loadField.
            wp_apply (wp_LockMap__Release with "[$Hislm $Hlocked Hinode_state Hcommit]").
            { iExists _. iFrame. iDestruct "Hcommit" as "[Hinode_enc Hinode_data]".
              iExists _.
              iDestruct (is_inode_data_shrink with "Hinode_data") as "Hinode_data"; eauto.
              rewrite firstn_length_le. 
              2: word.
              iFrame.
              replace (U64 (Z.of_nat (int.nat u))) with u by word.
              iFrame.
            }
            wp_apply (wp_LoadAt with "[Status Resok Resfail]").

            { iModIntro. iApply nfstypes_setattr3res_merge. iFrame. }
            iIntros "Hreply". simpl.
            iThaw "HΦ".
            iApply "HΦ". iLeft.
            iSplit; first done.
            iExactEq "HQ".
            f_equal.
          }
        }
      {
        iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".
        wp_storeField.

        (* Simulate to get Q, commit failed *)
        iApply fupd_wp.
        iInv "Hsrc" as ">Hopen" "Hclose".
        iNamed "Hopen".
        iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh".
        iDestruct (big_sepM_lookup with "Hnooverflow") as %Hnooverflow; eauto.
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
        iMod ("Hclose" with "[Hsrcheap HP]").
        { iModIntro. iExists _.  iFrame "∗%#". }
        iModIntro.
        wp_loadField.
        wp_apply (wp_LockMap__Release with "[$Hislm $Hlocked Hinode_state Hcommit]").
        { iExists _. iFrame.
          iDestruct "Hcommit" as "(Hinode & _)".
          iFrame.
         }
        wp_apply (wp_LoadAt with "[Status Resok Resfail]").

       { iModIntro. iApply nfstypes_setattr3res_merge. iFrame. }
       iIntros "Hreply". simpl.
       iThaw "HΦ".
       iApply "HΦ". iRight.
       iExists _.
       iSplit; first done.
       iFrame.
       iPureIntro. lia.
      }
*)
    }
  }

  wp_store.
  wp_load.

  iNamed 1.
  wpc_pures.

  iDestruct (is_buftxn_mem_durable with "Hbuftxn_mem Hbuftxn_durable") as "Hbuftxn".

  (* Not changing the length at all. *)
  wpc_apply (wpc_BufTxn__CommitWait with "[$Hbuftxn Hinode_enc Hinode_data]").
  4: { (* XXX is there a clean version of this? *) generalize (buftxn_maps_to γtxn). intros. iAccu. }
  { typeclasses eauto. }
  all: try solve_ndisj.

  iSplit.
  { iModIntro. iModIntro.
    iIntros "[[H _]|[H0 H1]]"; iSplit; try done; iApply is_inode_crash_ro; iFrame "Hinode_state".
    { iLeft; iFrame. }
    { iRight; iFrame. } }

  iModIntro.
  iIntros (ok) "Hcommit".
  destruct ok.
  {
    (* Simulate to get Q *)
    iApply fupd_wpc.
    iInv "Hsrc" as ">Hopen" "Hclose".
    iNamed "Hopen".
    iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh".
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
    iMod ("Hclose" with "[Hsrcheap HP]").
    { iModIntro. iExists _.  iFrame "∗%#". }
    iModIntro.

    wpc_frame "Hinode_state Hcommit".
    { iModIntro; iModIntro; iSplit; try done.
      iApply is_inode_crash_ro_own. iFrame "Hinode_state". iRight. iFrame. }

    iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".
    wp_storeField.

    iNamed 1.
    iSplitR "Hinode_state Hcommit".
    2: {
      iModIntro.
      iExists _; iFrame.
      iExists _; iFrame.
    }
    iIntros "Hcrashlocked".
    iSplit.
    { iModIntro. done. }

    wp_loadField.
    wp_apply (wp_LockMap__Release with "Hcrashlocked").
    wp_apply (wp_LoadAt with "[Status Resok Resfail]").
    { iModIntro. iApply nfstypes_setattr3res_merge. iFrame. }
    iIntros "Hreply". simpl.
    iThaw "HΦ".
    iApply "HΦ". iLeft.
    iSplit; first done.
    iFrame.
  }

  {
    (* Simulate to get Q, commit failed *)
    iApply fupd_wpc.
    iInv "Hsrc" as ">Hopen" "Hclose".
    iNamed "Hopen".
    iDestruct (map_valid with "Hsrcheap Hinode_state") as "%Hsrc_fh".
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
    iMod ("Hclose" with "[Hsrcheap HP]").
    { iModIntro. iExists _.  iFrame "∗%#". }
    iModIntro.

    iDestruct "Hcommit" as "[Hcommit _]". 
    wpc_frame "Hinode_state Hcommit".
    { iModIntro; iModIntro; iSplit; try done.
      iApply is_inode_crash_ro_own. iFrame "Hinode_state". iLeft. iFrame. }

    iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".
    wp_storeField.

    iNamed 1.
    iSplitR "Hinode_state Hcommit".
    2: {
      iModIntro.
      iExists _; iFrame.
    }
    iIntros "Hcrashlocked".
    iSplit.
    { iModIntro. done. }

    wp_loadField.
    wp_apply (wp_LockMap__Release with "Hcrashlocked").
    wp_apply (wp_LoadAt with "[Status Resok Resfail]").
    { iModIntro. iApply nfstypes_setattr3res_merge. iFrame. }
    iIntros "Hreply". simpl.
    iThaw "HΦ".
    iApply "HΦ". iRight. iExists _.
    iSplit; first done.
    iSplit; first done.
    iFrame.
  }
Unshelve.
  all: eauto.
Admitted.

End heap.
