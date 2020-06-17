From RecordUpdate Require Import RecordSet.

From Perennial.goose_lang Require Import crash_modality.

From Goose.github_com.mit_pdos.perennial_examples Require Import indirect_inode.

From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang Require Import lib.into_val.

From Perennial.goose_lang.lib Require Import typed_slice.
From Perennial.Helpers Require Import List.
From Perennial.program_proof Require Import marshal_proof.
From Perennial.program_proof Require Import disk_lib.

Definition maxDirect: Z := 500.
Definition maxIndirect: Z := 10.
Definition indirectNumBlocks: Z := 512.
Definition MaxBlocks: Z := maxDirect + maxIndirect*indirectNumBlocks.

Lemma indirect_blocks_maxBlocks:
  (MaxBlocks - maxDirect) `div` indirectNumBlocks = maxIndirect.
Proof.
  rewrite /MaxBlocks /maxDirect /indirectNumBlocks /maxIndirect.
  change (500 + 10 * 512 - 500) with (10*512).
  rewrite Z.div_mul; auto.
Qed.

Lemma indirect_blocks_upperbound_off sz:
  sz < maxIndirect * indirectNumBlocks ->
  sz `div` indirectNumBlocks < maxIndirect.
Proof.
  intros.
  apply Zdiv_lt_upper_bound; eauto.
  rewrite /indirectNumBlocks //.
Qed.

Lemma indirect_blocks_upperbound sz:
  sz < MaxBlocks ->
  (sz - maxDirect) `div` indirectNumBlocks < maxIndirect.
Proof.
  rewrite /MaxBlocks.
  intros.
  eapply indirect_blocks_upperbound_off. lia.
Qed.

Module inode.
  Record t :=
    mk { addr: u64;
         blocks: list Block; }.
  Global Instance _eta: Settable _ := settable! mk <addr; blocks>.
  Global Instance _witness: Inhabited t := populate!.

  Definition wf σ := length σ.(blocks) ≤ MaxBlocks.
  Definition size σ := length σ.(blocks).
End inode.

Hint Unfold inode.wf MaxBlocks : word.

Section goose.
Context `{!heapG Σ}.
Context `{!lockG Σ}.

Let inodeN := nroot.@"inode".

Implicit Types (σ: inode.t).
Implicit Types (l:loc) (γ:gname) (P: inode.t → iProp Σ).

Definition is_indirect (a: u64) (indBlkAddrs: list u64)
           (indBlock : Block) (specBlocks : list Block) (padding : list u64): iProp Σ :=
  "diskAddr" ∷ int.val a d↦ indBlock ∗
  "%Hencoded" ∷ ⌜Block_to_vals indBlock = b2val <$> encode ((EncUInt64 <$> indBlkAddrs) ++ (EncUInt64 <$> padding))⌝ ∗
  "%Hlen" ∷ ⌜length(indBlkAddrs) = length(specBlocks)⌝ ∗
  "Hdata" ∷ ([∗ list] a;b ∈ indBlkAddrs;specBlocks, int.val a d↦ b)
.

Definition ind_blocks_at_index σ index : list Block :=
  let begin := int.nat (int.nat maxDirect + (index * (int.nat indirectNumBlocks))) in
  List.subslice begin (begin + (int.nat indirectNumBlocks)) σ.(inode.blocks).

Definition is_inode_durable_with σ
            (dirAddrs indAddrs: list u64) (sz: u64) (numInd: u64)
            (indBlocks : list Block) (hdr: Block)
  : iProp Σ  :=
    "%Hwf" ∷ ⌜inode.wf σ⌝ ∗
    "%Hencoded" ∷ ⌜Block_to_vals hdr = b2val <$> encode ([EncUInt64 sz] ++ (EncUInt64 <$> dirAddrs) ++ (EncUInt64 <$> indAddrs) ++ [EncUInt64 numInd])⌝ ∗
    "%Hlen" ∷ (⌜
      length(dirAddrs) = int.nat maxDirect ∧
      length(indAddrs) = int.nat maxIndirect ∧
      int.val sz = length (σ.(inode.blocks)) ∧
      int.val sz < MaxBlocks ∧
      (int.val sz > maxDirect -> int.val numInd = Z.add ((int.val sz - maxDirect) `div` indirectNumBlocks) 1) ∧
      (int.val sz <= maxDirect -> int.val numInd = 0) ∧
      length indBlocks = int.nat numInd
    ⌝) ∗
    "Hhdr" ∷ (int.val σ.(inode.addr) d↦ hdr) ∗
    (* Double check: we can only state ptsto facts about inode blocks that exist? *)
    "HdataDirect" ∷ (let len := Nat.min (int.nat maxDirect) (length σ.(inode.blocks)) in
                     [∗ list] a;b ∈ take len dirAddrs;take len σ.(inode.blocks), int.val a d↦ b) ∗
    "HdataIndirect" ∷ [∗ list] index↦a;indBlock ∈ take (int.nat numInd) indAddrs;indBlocks,
    ∃ indBlkAddrs padding, is_indirect a indBlkAddrs indBlock (ind_blocks_at_index σ index) padding
.

Definition is_inode_durable σ : iProp Σ  :=
  ∃ (dirAddrs indAddrs: list u64) (sz: u64) (numInd: u64) (indBlocks : list Block) (hdr: Block),
    is_inode_durable_with σ dirAddrs indAddrs sz numInd indBlocks hdr
.

Definition inode_linv (l:loc) σ : iProp Σ :=
  ∃ (direct_s indirect_s: Slice.t) (dirAddrs indAddrs: list u64)
    (sz: u64) (numInd: u64) (indBlocks: list Block) (hdr: Block),
    "Hdurable" ∷ is_inode_durable_with σ dirAddrs indAddrs sz numInd indBlocks hdr ∗
    "addr" ∷ l ↦[Inode.S :: "addr"] #σ.(inode.addr) ∗
    "size" ∷ l ↦[Inode.S :: "size"] #sz ∗
    "direct" ∷ l ↦[Inode.S :: "direct"] (slice_val direct_s) ∗
    "indirect" ∷ l ↦[Inode.S :: "indirect"] (slice_val indirect_s) ∗
    "Hdirect" ∷ is_slice direct_s uint64T 1 (take (int.nat sz) dirAddrs) ∗
    "Hindirect" ∷ is_slice indirect_s uint64T 1 (take (int.nat numInd) indAddrs).

Definition is_inode l γ P : iProp Σ :=
  ∃ (d lref: loc),
    "#d" ∷ readonly (l ↦[Inode.S :: "d"] #d) ∗
    "#m" ∷ readonly (l ↦[Inode.S :: "m"] #lref) ∗
    "#Hlock" ∷ is_lock inodeN γ #lref (∃ σ, "Hlockinv" ∷ inode_linv l σ ∗ "HP" ∷ P σ).

Definition pre_inode l γ P σ : iProp Σ :=
  ∃ (d lref: loc), "#d" ∷ readonly (l ↦[Inode.S :: "d"] #d) ∗
                         "#m" ∷ readonly (l ↦[Inode.S :: "m"] #lref) ∗
                         "Hlock" ∷ is_free_lock γ lref ∗
                         "Hlockinv" ∷ inode_linv l σ ∗
                         "HP" ∷ P σ.

Theorem pre_inode_init {E} l γ P σ :
  pre_inode l γ P σ ={E}=∗ is_inode l γ P.
Proof.
  iNamed 1.
  iExists _, _; iFrame "#".
  iMod (alloc_lock inodeN _ _ _
                   (∃ σ, "Hlockinv" ∷ inode_linv l σ ∗ "HP" ∷ P σ)%I
          with "[$Hlock] [Hlockinv HP]") as "$".
  { iExists _; iFrame. }
  auto.
Qed.

Global Instance is_inode_Persistent l γ P:
  Persistent (is_inode l γ P).
Proof. apply _. Qed.

Global Instance is_inode_crash l σ :
  IntoCrash (inode_linv l σ) (λ _, is_inode_durable σ).
Proof.
  hnf; iIntros "Hinv".
  iNamed "Hinv".
  iNamed "Hdurable".
  iExists dirAddrs, indAddrs, sz, numInd, indBlocks, hdr.
  iFrame "% ∗".
  auto.
Qed.

(* TODO: these are copied from the circ proof *)
Definition block0: Block :=
  list_to_vec (replicate (Z.to_nat 4096) (U8 0)).

Lemma replicate_zero_to_block0 :
  replicate (int.nat 4096) (zero_val byteT) =
  Block_to_vals block0.
Proof.
  change (zero_val byteT) with #(U8 0).
  change (int.nat 4096) with (Z.to_nat 4096).
  rewrite /Block_to_vals /block0.
  reflexivity.
Qed.

Theorem init_inode addr :
  int.val addr d↦ block0 -∗ is_inode_durable (inode.mk addr []).
Proof.
  iIntros "Hhdr".
  iExists (replicate (Z.to_nat maxDirect) (U64 0)), (replicate (Z.to_nat maxIndirect) (U64 0)), (U64 0), (U64 0), [], block0.
  unfold is_inode_durable_with.
  iFrame "Hhdr".
  repeat iSplit; auto.
Qed.

Theorem wp_Open {d:loc} {addr σ P} :
  addr = σ.(inode.addr) ->
  {{{ is_inode_durable σ ∗ P σ }}}
    indirect_inode.Open #d #addr
  {{{ l γ, RET #l; is_inode l γ P }}}.
Proof.
  intros ->.
  iIntros (Φ) "(Hinode&HP) HΦ"; iNamed "Hinode".
  iDestruct (big_sepL2_length with "HdataDirect") as %Hblocklen.
  destruct Hlen as [HdirLen [HindirLen [HszEqLen [HszMax [HnumInd1 [HnumInd2 HindBlksLen]]]]]].

  wp_call.
  wp_apply (wp_Read with "Hhdr").
  iIntros (s) "(Hhdr&Hs)".
  wp_pures.
  iDestruct (slice.is_slice_to_small with "Hs") as "Hs".
  rewrite Hencoded.

  assert (encode ([EncUInt64 sz] ++ (EncUInt64 <$> dirAddrs) ++ (EncUInt64 <$> indAddrs)++ [EncUInt64 numInd] ) =
          encode ([EncUInt64 sz] ++ (EncUInt64 <$> dirAddrs) ++ (EncUInt64 <$> indAddrs)++ [EncUInt64 numInd] ) ++ [])
  as HappNil.
  { rewrite app_nil_r; auto. }
  rewrite HappNil.
  wp_apply (wp_NewDec _ _ s ([EncUInt64 sz] ++ (EncUInt64 <$> dirAddrs)++ (EncUInt64 <$> indAddrs) ++ [EncUInt64 numInd] ) []
                      with "Hs").
  iIntros (dec) "[Hdec %Hsz]".

  wp_apply (wp_Dec__GetInt with "Hdec"); iIntros "Hdec".
  wp_pures.
  wp_apply (wp_Dec__GetInts _ _ _ dirAddrs _ ((EncUInt64 <$> indAddrs) ++ [EncUInt64 numInd]) with "[Hdec]").
  { iFrame.
    iPureIntro.
    unfold maxDirect in *.
    word.
  }
  iIntros (diraddr_s) "[Hdec Hdiraddrs]".
  wp_pures.

  wp_apply (wp_Dec__GetInts _ _ _ indAddrs _ [EncUInt64 numInd] with "[Hdec]").
  { iFrame.
    iPureIntro.
    unfold maxIndirect in *.
    word.
  }
  iIntros (indaddr_s) "[Hdec Hindaddrs]".
  wp_pures.

  wp_apply (wp_Dec__GetInt with "Hdec"); iIntros "Hdec".
  wp_pures.

  wp_call.
  iDestruct "Hdiraddrs" as "[[HdirPtsto %Hdirs_len'] Hdirs_cap]".
  iDestruct "Hindaddrs" as "[[HindPtsto %Hinds_len'] Hinds_cap]".
  assert (length dirAddrs = int.nat diraddr_s.(Slice.sz) ∧
         length indAddrs = int.nat indaddr_s.(Slice.sz)) as [Hdirs_len Hinds_len].
  {
    split; [rewrite -Hdirs_len' | rewrite -Hinds_len']; rewrite fmap_length; auto.
  }
  iAssert (slice.is_slice diraddr_s uint64T 1 (u64val <$> dirAddrs)) with "[HdirPtsto Hdirs_cap]" as "Hdiraddrs".
  {
    unfold is_slice, slice.is_slice. iFrame.
    iPureIntro; auto.
  }
  iAssert (slice.is_slice indaddr_s uint64T 1 (u64val <$> indAddrs)) with "[HindPtsto Hinds_cap]" as "Hindaddrs".
  {
    unfold is_slice, slice.is_slice. iFrame.
    iPureIntro; auto.
  }

  destruct (bool_decide (int.val sz <= maxDirect)) eqn:HnumDir; unfold maxDirect in HnumDir; rewrite HnumDir; wp_pures.
  all: rewrite -wp_fupd; wp_apply wp_new_free_lock.
  all: iIntros (γ lref) "Hlock".
  {
    assert (int.val sz <= int.val maxDirect) as HszBound.
    {
      case_bool_decide.
      - auto.
      - discriminate.
    }
    wp_apply (wp_SliceTake uint64T sz).
    {
      rewrite HdirLen in Hdirs_len.
      assert (int.val maxDirect = int.val (diraddr_s.(Slice.sz))).
      { unfold maxDirect in *. word. }
      rewrite -H; auto.
    }
    pose (HnumInd2 HszBound) as HnumInd.
    wp_apply (wp_SliceTake uint64T numInd).
    {
      rewrite HindirLen in Hinds_len.
      word.
    }
    wp_apply wp_allocStruct; auto.
    iIntros (l) "Hinode".
    iDestruct (struct_fields_split with "Hinode") as "(d&m&addr&sz&direct&indirect&_)".
    iMod (readonly_alloc_1 with "d") as "#d".
    iMod (readonly_alloc_1 with "m") as "#m".
    iMod (alloc_lock inodeN ⊤ _ _
                    (∃ σ, "Hlockinv" ∷ inode_linv l σ ∗ "HP" ∷ P σ)%I
            with "[$Hlock] [-HΦ]") as "#Hlock".
    { iExists _; iFrame.
      iExists (slice_take diraddr_s uint64T sz), (slice_take indaddr_s uint64T numInd),
      dirAddrs, indAddrs, sz, numInd, indBlocks, hdr.
      iFrame.
      iSplit; iFrame.
      - iFrame "∗ %".
        iPureIntro. repeat (split; auto).
      - iSplitL "Hdiraddrs"; unfold is_slice; rewrite /list.untype fmap_take//.
        {
          iApply (is_slice_take_cap with "Hdiraddrs").
          rewrite Hdirs_len' -Hdirs_len.
          rewrite HdirLen; auto.
        }
        {
          iApply (is_slice_take_cap with "Hindaddrs").
          rewrite Hinds_len' -Hinds_len.
          rewrite /maxIndirect in HindirLen.
          rewrite HindirLen /maxIndirect; auto.
          word.
        }
    }
    iModIntro.
    iApply "HΦ".
    iExists _, _; iFrame "#".
  }
  {
    assert (int.val sz > int.val maxDirect) as HszBound.
    {
      case_bool_decide.
      - discriminate.
      - rewrite /maxDirect; word.
    }
    pose proof (HnumInd1 HszBound) as HnumInd.
    wp_apply (wp_SliceTake uint64T maxDirect).
    {
      rewrite HdirLen in Hdirs_len.
      assert (maxDirect = int.val (diraddr_s.(Slice.sz))).
      {
        unfold maxDirect in Hdirs_len. unfold maxDirect. by word.
      }
      rewrite -H; word.
    }
    wp_apply (wp_SliceTake uint64T numInd).
    {
      rewrite HindirLen in Hinds_len.
      rewrite HnumInd.
      assert ((int.val sz - maxDirect) `div` indirectNumBlocks + 1 < maxIndirect + 1) as HmaxCmp. {
        rewrite Z.lt_add_lt_sub_r.
        change (maxIndirect + 1 - 1) with (maxIndirect).
        apply indirect_blocks_upperbound. auto.
      }
      unfold maxIndirect in *.
      word.
    }
    wp_apply wp_allocStruct; auto.
    iIntros (l) "Hinode".
    iDestruct (struct_fields_split with "Hinode") as "(d&m&addr&sz&direct&indirect&_)".
    iMod (readonly_alloc_1 with "d") as "#d".
    iMod (readonly_alloc_1 with "m") as "#m".
    iMod (alloc_lock inodeN ⊤ _ _
                    (∃ σ, "Hlockinv" ∷ inode_linv l σ ∗ "HP" ∷ P σ)%I
            with "[$Hlock] [-HΦ]") as "#Hlock".
    { iExists _; iFrame.
      iExists (slice_take diraddr_s uint64T 500), (slice_take indaddr_s uint64T numInd),
      dirAddrs, indAddrs, sz, numInd, indBlocks, hdr.
      iFrame.
      iSplit; iFrame.
      - iFrame "∗ %".
        iPureIntro. repeat (split; auto).
      - iSplitL "Hdiraddrs"; unfold is_slice; rewrite /list.untype fmap_take//.
        {
          change (to_val <$> dirAddrs) with (u64val<$> dirAddrs).
          rewrite take_ge; last by len.
          iEval (rewrite -(firstn_all (u64val <$> dirAddrs)) fmap_length HdirLen /maxDirect).
          iApply (is_slice_take_cap with "Hdiraddrs").
          rewrite Hdirs_len' -Hdirs_len HdirLen /maxDirect. word.
        }
        {
          iApply (is_slice_take_cap with "Hindaddrs").
          pose (indirect_blocks_upperbound (int.val sz)) as Hbound.
          rewrite Hinds_len' -Hinds_len.
          rewrite /maxIndirect HindirLen /maxIndirect HnumInd.
          unfold maxIndirect in Hbound.
          word.
        }
    }
    iModIntro.
    iApply "HΦ".
    iExists _, _; iFrame "#".
  }
Qed.

Theorem wp_indNum {off: u64} :
  {{{
       ⌜int.val off >= maxDirect⌝
  }}}
    indNum #off
  {{{(v: u64), RET #v;
      ⌜int.val v = (int.val off - maxDirect) `div` indirectNumBlocks⌝
  }}}.
Proof.
  iIntros (ϕ) "%H Hϕ".
  wp_call.
  iApply "Hϕ".
  iPureIntro.
  unfold indirectNumBlocks. unfold maxDirect in *.
  word_cleanup.
  word.
Qed.

Theorem wp_indOff {off: u64} :
  {{{
       ⌜int.val off >= maxDirect⌝
  }}}
    indOff #off
  {{{(v: u64), RET #v;
     ⌜int.val v = (int.val off - maxDirect) `mod` indirectNumBlocks⌝
  }}}.
Proof.
  iIntros (ϕ) "%H Hϕ".
  wp_call.
  iApply "Hϕ".
  iPureIntro.
  unfold indirectNumBlocks. unfold maxDirect in *.
  word_cleanup.
  word.
Qed.

Theorem wp_readIndirect {l σ}
        indirect_s (numInd: u64) (indAddrs : list u64)
        (indBlocks : list Block) (indBlk: Block) (indBlkAddrs : list u64)
        (index: nat) (d : loc) (a : u64) (padding: list u64):
  {{{
    "%Hwf" ∷ ⌜inode.wf σ⌝ ∗
    "%Hlen" ∷ ⌜length(indAddrs) = int.nat maxIndirect ∧ int.val numInd <= maxIndirect⌝ ∗
    "#d" ∷ readonly (l ↦[Inode.S :: "d"] #d) ∗
    "%Haddr" ∷ ⌜Some a = (take (int.nat numInd) indAddrs) !! index⌝ ∗
    "%HindBlk" ∷ ⌜Some indBlk = indBlocks!! index⌝ ∗
    "indirect" ∷ l ↦[Inode.S :: "indirect"] (slice_val indirect_s) ∗
    "Hindirect" ∷ is_slice indirect_s uint64T 1 (take (int.nat numInd) indAddrs) ∗
    "HindBlkAddrs" ∷ is_indirect a indBlkAddrs indBlk (ind_blocks_at_index σ index) padding
  }}}
     readIndirect #d #a
  {{{ indBlkAddrs_s, RET slice_val indBlkAddrs_s;
    ∃ padding, "HindBlkIndirect" ∷ is_indirect a indBlkAddrs indBlk (ind_blocks_at_index σ index) padding ∗
    "HindBlkAddrs" ∷ is_slice indBlkAddrs_s uint64T 1 (indBlkAddrs++padding) ∗
    "indirect" ∷ l ↦[Inode.S :: "indirect"] (slice_val indirect_s) ∗
    "Hindirect" ∷ is_slice indirect_s uint64T 1 (take (int.nat numInd) indAddrs)
  }}}.
Proof.
  iIntros (ϕ) "H Hϕ". iNamed "H". iNamed "HindBlkAddrs".
  destruct Hlen as [HindAddrsMax HnumIndBound].
  wp_call.

  wp_apply ((wp_Read a 1 indBlk) with "[diskAddr]"); auto.
  iIntros (s) "[diskAddr Hs]".
  wp_let.
  unfold is_block_full.
  iDestruct (slice.is_slice_to_small with "Hs") as "Hs".
  rewrite Hencoded.

  assert (encode ((EncUInt64 <$> indBlkAddrs) ++ (EncUInt64 <$> padding))
                 = (encode ((EncUInt64 <$> indBlkAddrs) ++ (EncUInt64 <$> padding)) ++ []))
    as HappNil.
  { rewrite app_nil_r. auto. }
  rewrite HappNil.

  wp_apply (wp_NewDec _ _ s ((EncUInt64 <$> indBlkAddrs) ++ (EncUInt64 <$> padding)) [] with "Hs").
  iIntros (dec) "[Hdec %Hdec_s]".
  wp_pures.

  rewrite -fmap_app.
  assert (length indBlkAddrs + length padding = indirectNumBlocks). {
    rewrite /maxIndirect /maxDirect /indirectNumBlocks.
    rewrite /maxIndirect /maxDirect /indirectNumBlocks in Hlen0.
    assert (length (Block_to_vals indBlk) = length (b2val <$> encode ((EncUInt64 <$> indBlkAddrs) ++ (EncUInt64 <$> padding)))).
    {
      rewrite Hencoded. auto.
    }
    rewrite fmap_length in H.
    rewrite length_Block_to_vals in H.
    unfold block_bytes in H.
    rewrite encode_app_length in H.

    rewrite (length_encode_fmap_uniform 8 EncUInt64 indBlkAddrs) in H;
        [| intros; by rewrite -encode_singleton encode_singleton_length].
    rewrite (length_encode_fmap_uniform 8 EncUInt64 padding) in H;
      [| intros; by rewrite -encode_singleton encode_singleton_length].
    word.
  }
  wp_apply (wp_Dec__GetInts _ _ _ (indBlkAddrs++padding) _ [] with "[Hdec]").
  {
    rewrite app_nil_r.
    iFrame.
    iPureIntro.
    rewrite app_length.
    unfold indirectNumBlocks in H.
    word.
  }
  iIntros (indBlkAddrsPadding_s) "[_ HindBlks]".

  iApply "Hϕ"; iFrame.
  iExists padding.
  iSplitR "HindBlks"; auto.
Qed.

Theorem wp_Inode__Read {l γ P} {off: u64} Q :
  {{{ is_inode l γ P ∗
      (∀ σ σ' mb,
        ⌜σ' = σ ∧ mb = σ.(inode.blocks) !! int.nat off⌝ ∗
        P σ ={⊤}=∗ P σ' ∗ Q mb)
  }}}
    Inode__Read #l #off
  {{{ s mb, RET slice_val s;
      (match mb with
       | Some b => ∃ s, is_block s 1 b
       | None => ⌜s = Slice.nil⌝
       end) ∗ Q mb }}}.
Proof.
  iIntros (Φ) "(Hinode&Hfupd) HΦ"; iNamed "Hinode".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "(His_locked&Hlk)"; iNamed "Hlk".
  iNamed "Hlockinv".
  iNamed "Hdurable".
  destruct Hlen as [HdirLen [HindirLen [HszEqLen [HszMax [HnumInd1 [HnumInd2 HindBlksLen]]]]]].
  wp_loadField.
  wp_op.
  wp_if_destruct.
  - wp_loadField.
    iMod ("Hfupd" $! σ σ with "[$HP]") as "[HP HQ]".
    { iPureIntro.
      eauto. }
    wp_apply (release_spec with "[$Hlock $His_locked HP Hhdr addr
             size direct indirect Hdirect Hindirect HdataDirect HdataIndirect]").
    { iExists _; iFrame.
      iExists direct_s, indirect_s, dirAddrs, indAddrs, sz, numInd, indBlocks, hdr. iFrame "∗ %".
      iPureIntro. repeat (split; auto).
    }
    wp_pures.
    change slice.nil with (slice_val Slice.nil).
    iApply "HΦ"; iFrame.
    rewrite lookup_ge_None_2 //.
    rewrite HszEqLen in Heqb.
    word.
  - wp_op.
    assert (int.val off < int.val sz) as Hszoff by lia.
    unfold maxDirect in *.

    wp_if_destruct.

    (* Is direct block *)
    {
      wp_loadField.
      destruct (list_lookup_lt _ dirAddrs (int.nat off)) as [addr Hlookup].
      { unfold maxDirect. rewrite HdirLen. unfold maxDirect. word. }
      iDestruct (is_slice_split with "Hdirect") as "[Hdirect_small Hdirect]".
      wp_apply (wp_SliceGet _ _ _ _ _ (take (int.nat sz) dirAddrs) _ addr with "[Hdirect_small]").
      { iSplit; auto.
        unfold maxDirect in *.
        iPureIntro.
        rewrite lookup_take; auto.
        word.
      }
      iIntros "Hdirect_small".
      wp_pures.
      iDestruct (big_sepL2_lookup_1_some _ _ _ (int.nat off) addr with "HdataDirect") as "%Hblock_lookup"; eauto.
      { rewrite lookup_take; [auto | word]. }
      destruct Hblock_lookup as [b0 Hlookup2].
      iDestruct (is_slice_split with "[$Hdirect_small $Hdirect]") as "Hdirect".
      iDestruct (big_sepL2_lookup_acc _ _ _ _ addr with "HdataDirect") as "[Hb HdataDirect]"; eauto.
      { rewrite lookup_take; [auto | word]. }
      wp_apply (wp_Read with "Hb"); iIntros (s) "[Hb Hs]".
      iSpecialize ("HdataDirect" with "Hb").
      wp_loadField.
      iMod ("Hfupd" $! σ σ with "[$HP]") as "[HP HQ]".
      { iPureIntro; eauto. }
      wp_apply (release_spec with "[$Hlock $His_locked HP Hhdr addr
             size direct indirect Hdirect Hindirect HdataDirect HdataIndirect]").
      { iExists _; iFrame.
        iExists direct_s, indirect_s, dirAddrs, indAddrs, sz, numInd, indBlocks, hdr. iFrame "∗ %".
        iPureIntro; repeat (split; auto).
      }
      wp_pures.
      iApply "HΦ"; iFrame.
      rewrite lookup_take in Hlookup2; [ | word ].
      rewrite Hlookup2.
      iDestruct (is_slice_split with "Hs") as "[Hs _]".
      iExists _; iFrame.
    }


    (* Is indirect block *)
    {
      wp_apply wp_indNum.
      { iPureIntro. auto. }

      iIntros (v) "%Hv".

      (* Here are a bunch of facts *)
      assert (int.val off >= int.val 500) as Hoff500 by word.
      assert (int.val sz > 500) as Hsz by word.
      assert (int.val numInd <= maxIndirect) as HnumIndMax.
      {
         unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
         assert (((int.val sz - 500) `div` 512) < 10) as H.
          {
            apply (Zdiv_lt_upper_bound (int.val sz - 500) 512 10); lia.
          }
          rewrite (HnumInd1 Hsz).
          lia.
      }
      assert (((int.val off - 500) `div` 512) <= ((int.val sz - 500) `div` 512)) as Hoff. {
        apply Z_div_le; lia.
      }

      assert (int.val v < int.val numInd) as HvMax. {
        unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *. word.
      }
      destruct (list_lookup_lt _ (take (int.nat numInd) indAddrs) (int.nat v)) as [addr Hlookup].
      {
        unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
        rewrite firstn_length Hv HindirLen.
        rewrite Min.min_l; word.
      }
      destruct (list_lookup_lt _ indBlocks (int.nat v)) as [indBlk HlookupBlk].
      {
        unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
        rewrite HindBlksLen. word.
      }
      assert (int.nat sz = length(σ.(inode.blocks))) as HszeqNat by word.

      (* Now we actually step through the program *)
      wp_loadField.
      iDestruct (is_slice_split with "Hindirect") as "[Hindirect_small Hindirect]".
      wp_apply (wp_SliceGet _ _ _ _ 1 (take (int.nat numInd) indAddrs) _ addr with "[Hindirect_small]"); iFrame; auto.

      iIntros "Hindirect_small".
      iDestruct (is_slice_split with "[$Hindirect_small $Hindirect]") as "Hindirect".
      iDestruct (big_sepL2_lookup_acc _ (take (int.nat numInd) indAddrs) _ (int.nat v) addr with "HdataIndirect") as "[Hb HdataIndirect]"; eauto.

      wp_loadField.
      iDestruct "Hb" as (indBlkAddrs padding) "HaddrIndirect".
      wp_apply (wp_readIndirect indirect_s numInd indAddrs indBlocks indBlk
                                indBlkAddrs (int.nat v) d addr padding
                  with "[indirect Hindirect HaddrIndirect]").
      {
        iFrame. iSplit; eauto.
      }
      iIntros (indBlkAddrs_s) "H". iNamed "H". iNamed "HindBlkIndirect".

      wp_let.
      wp_apply wp_indOff.
      { iPureIntro; auto. }
      iIntros (offset) "%Hoffset".

      (* More facts about offset *)
      assert (int.val offset < length indBlkAddrs) as HoffsetInBounds.
      {
        unfold ind_blocks_at_index in Hlen.
        unfold maxDirect, indirectNumBlocks in *.
        rewrite Hlen.

        destruct (dec_ge (length σ.(inode.blocks)) ((500 + int.nat v * 512) + 512)) as [HlenGe | HlenNotGe].
        (* Subslice fully contained in blocks *)
        {
          rewrite subslice_length.
          - rewrite minus_plus. rewrite Hoffset.
            apply Z_mod_lt; word.
          - word.
        }
        (* Subslice goes to end of blocks *)
        {
          rewrite Hv in HlenNotGe.
          pose (not_ge _ _ HlenNotGe) as HlenLt.
          rewrite subslice_to_end.
          - rewrite Hoffset.
            rewrite skipn_length.
            assert (int.val v < 10). {
              unfold maxIndirect in *.
              apply (Z.lt_le_trans (int.val v) (int.val numInd) 10); auto.
            }
            rewrite Hv.
            rewrite -HszeqNat.
            word_cleanup.
            admit.
          - rewrite -HszeqNat Hv.
            admit.
        }
      }
      destruct (list_lookup_lt _ (ind_blocks_at_index σ (int.nat v)) (int.nat offset)) as [inodeblkaddr HlookupInodeBlk].
      { rewrite -Hlen. word. }
      destruct (list_lookup_lt _ (indBlkAddrs) (int.nat offset)) as [blkaddr HlookupBlkInd]; try word.
      assert ((σ.(inode.blocks)) !! (int.nat off) = Some inodeblkaddr) as HlookupInodeBlk'.
      {
        admit.
      }

      (* Continue through the program *)
      iDestruct (is_slice_split with "HindBlkAddrs") as "[HindBlkAddrs_small HindBlkAddrs]".

      assert ((indBlkAddrs ++ padding0) !! int.nat offset = Some blkaddr) as HlookupBlkIndPadded. {
        rewrite -(lookup_app_l indBlkAddrs padding0) in HlookupBlkInd; auto; try word.
      }
      wp_apply (wp_SliceGet _ _ _ _ 1 (indBlkAddrs++padding0) _ blkaddr with "[HindBlkAddrs_small]"); iFrame; auto.

      iIntros "HindBlkAddrs_small".
      iDestruct (is_slice_split with "[$HindBlkAddrs_small $HindBlkAddrs]") as "HindBlkAddrs".
      iDestruct (big_sepL2_lookup_acc _ _ _ _ _ with "Hdata") as "[Hb' Hdata]"; eauto.

      wp_apply (wp_Read with "Hb'"); iIntros (s) "[Hb' Hs]".
      wp_let.

      iSpecialize ("Hdata" with "Hb'").
      iAssert (∃ indBlkAddrs padding, is_indirect addr indBlkAddrs indBlk (ind_blocks_at_index σ (int.nat v)) padding)%I
        with "[diskAddr HindBlkAddrs Hdata]" as "HaddrIndirect".
      {
        iExists indBlkAddrs, padding0.
        unfold is_indirect.
        iFrame. iSplit; auto.
      }
      iSpecialize ("HdataIndirect" with "HaddrIndirect").

      wp_loadField.
      iMod ("Hfupd" $! σ σ with "[$HP]") as "[HP HQ]".
      { iPureIntro; eauto. }
      wp_apply (release_spec with "[$Hlock $His_locked HP Hhdr addr
             size direct indirect Hdirect Hindirect HdataDirect HdataIndirect]").
      { iExists _; iFrame.
        iExists direct_s, indirect_s, dirAddrs, indAddrs, sz, numInd, indBlocks, hdr. iFrame "∗ %".
        iPureIntro; repeat (split; auto).
      }
      wp_pures.
      iApply "HΦ"; iFrame.

      rewrite HlookupInodeBlk'.
      iExists _; iDestruct (is_slice_split with "Hs") as "[Hs_small Hs]"; eauto.
    }
Admitted.

Theorem wp_Inode__Size {l γ P} (Q: u64 -> iProp Σ) :
  {{{ is_inode l γ P ∗
      (∀ σ σ' sz,
          ⌜σ' = σ ∧ int.nat sz = inode.size σ⌝ ∗
          P σ ={⊤}=∗ P σ' ∗ Q sz)
  }}}
    Inode__Size #l
  {{{ sz, RET #sz; Q sz }}}.
Proof.
  iIntros (Φ) "(Hinv & Hfupd) HΦ"; iNamed "Hinv".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "(Hlocked & Hinner)". iNamed "Hinner".
  iNamed "Hlockinv". iNamed "Hdurable".
  wp_loadField.
  wp_let.
  wp_loadField.
  iMod ("Hfupd" $! σ σ sz with "[$HP]") as "[HP HQ]".
  { iPureIntro.
    split; auto.
    rewrite /inode.size.
    word.
  }
  wp_apply (release_spec with "[-HQ HΦ $Hlock]").
  { iFrame "Hlocked".
    iExists σ; iFrame.
    iExists direct_s, indirect_s, dirAddrs, indAddrs, sz, numInd, indBlocks, hdr. iFrame "∗ %".
  }
  wp_pures.
  iApply ("HΦ" with "[$]").
Qed.

Theorem wp_padInts enc (n: u64) (encoded : list encodable) (off: Z):
  {{{
    ⌜ int.val 0 ≤ int.val n ∧ off >= 8*(int.val n) ⌝ ∗
    is_enc enc encoded off
  }}}
    padInts (EncM.to_val enc) #n
  {{{ RET #();
    is_enc enc (encoded ++ (EncUInt64 <$> replicate (int.nat n) (U64 0))) (int.val off-(8*int.val n))
  }}}.
Proof.
  iIntros (ϕ) "[%Hi Henc] Hϕ".
  wp_call.
  wp_call.
  change (#0) with (zero_val (baseT uint64BT)).
  wp_apply wp_ref_of_zero; auto.
  iIntros (i) "Hi".
  wp_let.

  wp_apply (wp_forUpto (λ i, "%Hiupper_bound" ∷ ⌜int.val i <= int.val n⌝ ∗
                       "Henc" ∷ is_enc enc (encoded ++ (EncUInt64 <$> (replicate (int.nat i) (U64 0))))
                       (off - (8 * int.nat i)))%I _ _
                    0 n
            with "[] [Henc Hi] [-]").
  {
    word.
  }
  {
    iIntros. iModIntro. iIntros (ϕ0) "H Hϕ0".
    iDestruct "H" as "[H [Hi %Hibound]]"
.
    iNamed "H".
    wp_pures.
    wp_apply (wp_Enc__PutInt with "Henc").
    {
      admit.
    }
    iIntros "Henc".
    wp_pures.
    iApply "Hϕ0".
    iFrame.
    iSplitR "Henc".
    - iPureIntro. (*Need to show doesn't overflow*) admit.
    - (*Need to show that replicate can turn into append*)admit.
  }
  {
    iSplitL "Henc"; iFrame; auto.
    iSplitR "Henc".
    - iPureIntro. admit.
    - admit. (*need to show 0 replicate and 0 addition*)
  }

  iModIntro.
  iIntros "[H Hi]".
  iNamed "H".
  iApply "Hϕ"; iFrame.
Admitted.

Theorem wp_Inode__mkHdr l (sz numInd : u64) allocedDirAddrs allocedIndAddrs direct_s indirect_s:
  (length(allocedDirAddrs) <= int.nat maxDirect ∧
  length(allocedIndAddrs) = int.nat numInd ∧
  int.val sz < MaxBlocks ∧
  (int.val sz > maxDirect -> int.val numInd = Z.add ((int.val sz - maxDirect) `div` indirectNumBlocks) 1) ∧
  (int.val sz <= maxDirect -> int.val numInd = 0)) ->
  {{{
    "direct" ∷ l ↦[Inode.S :: "direct"] (slice_val direct_s) ∗
    "indirect" ∷ l ↦[Inode.S :: "indirect"] (slice_val indirect_s) ∗
    "size" ∷ l ↦[Inode.S :: "size"] #sz ∗
    "Hdirect" ∷ is_slice direct_s uint64T 1 allocedDirAddrs ∗
    "Hindirect" ∷ is_slice indirect_s uint64T 1 allocedIndAddrs
  }}}
    Inode__mkHdr #l
  {{{ s hdr, RET (slice_val s);
    is_block s 1 hdr ∗
    "%Hencoded" ∷ ⌜Block_to_vals hdr =
    b2val <$> encode ([EncUInt64 sz] ++ (EncUInt64 <$> allocedDirAddrs) ++ (EncUInt64 <$> (replicate (int.nat (maxDirect - length allocedDirAddrs)) (U64 0)))
                                     ++ (EncUInt64 <$> allocedIndAddrs) ++ (EncUInt64 <$> (replicate (int.nat (maxIndirect - length allocedIndAddrs)) (U64 0)))
                                     ++ [EncUInt64 numInd])⌝ ∗
    "direct" ∷ l ↦[Inode.S :: "direct"] (slice_val direct_s) ∗
    "indirect" ∷ l ↦[Inode.S :: "indirect"] (slice_val indirect_s) ∗
    "size" ∷ l ↦[Inode.S :: "size"] #sz ∗
    "Hdirect" ∷ is_slice direct_s uint64T 1 allocedDirAddrs ∗
    "Hindirect" ∷ is_slice indirect_s uint64T 1 allocedIndAddrs
  }}}.
Proof.
  iIntros (Hbound Φ) "Hpre HΦ"; iNamed "Hpre".
  wp_call.
  wp_apply wp_new_enc; iIntros (enc) "[Henc %]".
  wp_pures.
  wp_loadField.
  iDestruct (is_slice_sz with "Hdirect") as %HDirlen.
  iDestruct (is_slice_sz with "Hindirect") as %HIndlen.
  autorewrite with len in HDirlen.
  autorewrite with len in HIndlen.
  destruct Hbound as [HallocedDirAddrsLen [HallocedIndAddrsLen [Hszmax [HnumInd1 HnumInd2]]]].

  assert (int.val numInd <= maxIndirect) as HnumInd.
  {
    destruct (bool_decide (int.val sz > maxDirect)) eqn:Heqsz.
    - apply bool_decide_eq_true in Heqsz.
      rewrite (HnumInd1 Heqsz).
      pose (indirect_blocks_upperbound (int.val sz) Hszmax).
      word.
    - apply bool_decide_eq_false in Heqsz.
      rewrite (HnumInd2 Heqsz).
      rewrite /maxIndirect; word.
  }

  wp_apply (wp_Enc__PutInt with "Henc").
  { word. }
  iIntros "Henc".
  rewrite app_nil_l.
  wp_loadField.

  iDestruct (is_slice_split with "Hdirect") as "[Hdirect Hcap]".
  wp_apply (wp_Enc__PutInts with "[$Henc $Hdirect]").
  {
    rewrite /maxDirect in HallocedDirAddrsLen.
    word.
  }

  iIntros "[Henc Hdirect]".
  wp_loadField.
  wp_apply wp_slice_len; wp_pures.

  wp_apply (wp_padInts enc (U64 (500 - int.val (direct_s.(Slice.sz))))
                       ([EncUInt64 sz] ++ (EncUInt64 <$> allocedDirAddrs))
                       (int.val 4096 - 8 - 8 * length allocedDirAddrs) with "[Henc]").
  {
    iSplitR "Henc"; auto.
    iPureIntro.
    split.
    - rewrite HDirlen /maxDirect in HallocedDirAddrsLen. word.
    - rewrite HDirlen. rewrite HDirlen /maxDirect in HallocedDirAddrsLen.
      word.
  }

  iIntros "Henc".
  replace (int.val (int.val 4096 - 8 - 8 * length allocedDirAddrs) -
           8 * int.val (500 - int.val direct_s.(Slice.sz))) with 88.
  2: rewrite HDirlen; rewrite HDirlen /maxDirect in HallocedDirAddrsLen; word.

  wp_pures.
  wp_loadField.

  iDestruct (is_slice_split with "Hindirect") as "[Hindirect Hcapind]".
  wp_apply (wp_Enc__PutInts with "[$Henc $Hindirect]").
  { rewrite HallocedIndAddrsLen. rewrite /maxIndirect in HnumInd. word. }

  iIntros "[Henc Hindirect]".
  wp_loadField.
  wp_apply wp_slice_len; wp_pures.

  wp_apply (wp_padInts enc (U64 (10 - int.val (indirect_s.(Slice.sz))))
               ((([EncUInt64 sz] ++ (EncUInt64 <$> allocedDirAddrs) ++
               (EncUInt64 <$> replicate (int.nat (500 - int.val direct_s.(Slice.sz))) (U64 0))) ++
               (EncUInt64 <$> allocedIndAddrs)))
               (88 - 8 * length allocedIndAddrs) with "[Henc]").
  {
    iSplitR "Henc"; auto.
    iPureIntro.
    split; rewrite HIndlen /maxIndirect in HallocedIndAddrsLen HnumInd; word.
  }
  iIntros "Henc".
  rewrite /maxIndirect in HnumInd.
  replace (int.val (88 - 8 * length allocedIndAddrs) -
           8 * int.nat (10 - int.val indirect_s.(Slice.sz))) with 8 by word.

  wp_pures.
  wp_loadField.
  wp_apply wp_slice_len; wp_pures.
  wp_apply (wp_Enc__PutInt with "Henc").
  { word. }
  iIntros "Henc".
  wp_pures.

  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (s) "[Hs %]".
  wp_pures.
  iApply "HΦ".
  iFrame.
  autorewrite with len in H0.
  iSplitL "Hs".
  - rewrite -list_to_block_to_vals; len.
    + iFrame.
    + rewrite H0.
      rewrite H; reflexivity.
  - iPureIntro.
    rewrite list_to_block_to_vals; len.
    +
      repeat (f_equal; try word).
      rewrite HIndlen in HallocedIndAddrsLen.
      rewrite /maxDirect /maxIndirect HDirlen HIndlen HallocedIndAddrsLen.
      replace (Z.to_nat (int.val (88 - 8 * int.nat numInd) - 8 * int.val (10 - int.val indirect_s.(Slice.sz)) - 8))
        with (int.nat 0) by (rewrite -HallocedIndAddrsLen; word).
      rewrite replicate_0 app_nil_r.
      rewrite -HallocedIndAddrsLen.
      assert (indirect_s.(Slice.sz) = numInd) as foo by word; rewrite foo.
      repeat (rewrite -app_assoc).
      word_cleanup. reflexivity.
    + rewrite H0.
      rewrite H; reflexivity.
Qed.

Inductive AppendStatus :=
| AppendOk
| AppendFull
| AppendAgain.

Instance AppendStatus_witness : Inhabited AppendStatus := populate!.

Instance AppendStatus_eq_dec : EqDecision AppendStatus.
Proof. solve_decision. Qed.

Instance AppendStatus_val : IntoVal AppendStatus.
Proof.
  refine {| to_val := λ v, match v with
                           | AppendOk => #(U8 0)
                           | AppendAgain => #(U8 1)
                           | AppendFull => #(U8 2)
                           end;
            IntoVal_def := AppendOk;
         |}.
  abstract (intros [] []; auto; inversion 1).
Defined.

Theorem wp_Inode__Append {l γ P} (Q: AppendStatus -> iProp Σ) (a: u64) (b0: Block) :
  {{{ is_inode l γ P ∗ int.val a d↦ b0 ∗
      (∀ σ σ' (status: AppendStatus),
          ⌜(match status with
            | AppendOk => σ' = set inode.blocks (λ bs, bs ++ [b0]) σ
            (* TODO: if status is AppendAgain, still need to take ownership of a
               even if blocks don't change *)
            | _ => σ' = σ
            end) ∧
          (status = AppendFull ↔ 1 + inode.size σ > MaxBlocks)⌝ -∗
        ⌜inode.wf σ⌝ -∗
         P σ ={⊤}=∗ P σ' ∗ Q status)
  }}}
    Inode__Append #l #a
  {{{ (status: AppendStatus), RET (to_val status); Q status ∗ if bool_decide (status = AppendOk) then emp else int.val a d↦ b0 }}}.
Proof.
  iIntros (Φ) "(Hinode&Ha&Hfupd) HΦ"; iNamed "Hinode".
  wp_call.
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "(His_locked&Hlk)"; iNamed "Hlk".
  iNamed "Hlockinv".
  iNamed "Hdurable".
  iDestruct (is_slice_sz with "Hdirect") as %Hlen1.
  iDestruct (big_sepL2_length with "HdataDirect") as %Hlen2.
  autorewrite with len in Hlen1.
  destruct Hlen as [HdirLen [HindirLen [HszEqLen [HszMax [HnumInd1 [HnumInd2 HindBlksLen]]]]]].

  wp_loadField.
  change (word.add 500 (word.mul 10 512)) with (U64 5620).

  wp_pures.
  destruct (bool_decide (int.val 5620 <= int.val sz)) eqn:Hsz; wp_pures.
  {
    change (500 + 10 * 512) with (int.val 5620).
    apply bool_decide_eq_true in Hsz.
    wp_loadField.
    iMod ("Hfupd" $! σ σ AppendFull with "[%] [%] HP") as "[HP HQ]"; auto.
    { split; auto.
      split; auto.
      intros.
      rewrite -HszEqLen /inode.size /MaxBlocks /maxDirect /maxIndirect /indirectNumBlocks.
      word.
    }

    wp_apply (release_spec with "[$Hlock $His_locked HP Hhdr addr size direct indirect Hdirect Hindirect HdataDirect HdataIndirect]").
    {
      iExists σ; iFrame.
      iExists direct_s, indirect_s, dirAddrs, indAddrs, sz, numInd, indBlocks, hdr. iFrame "∗ %".
      iPureIntro; repeat (split; auto).
    }
    wp_pures.
    iApply ("HΦ" $! AppendFull).
    iSplitR "Ha"; auto.
    rewrite bool_decide_eq_false_2; auto.
  }

  wp_loadField.
  wp_if_destruct.
  - wp_loadField.
    wp_apply (wp_SliceAppend (V:=u64) with "[$Hdirect]").
    { iPureIntro.
      word. }
    iIntros (direct_s') "Hdirect".
    Transparent slice.T.
    wp_storeField.
    wp_loadField.
    wp_storeField.
    wp_apply (wp_Inode__mkHdr _ _ numInd ((take (int.nat sz) dirAddrs) ++ [a]) _ _ _ with "[$direct $indirect $size $Hdirect $Hindirect]").
    {
      autorewrite with len; simpl.
      assert (int.val (word.add sz 1) <= int.val 500) by word.
      repeat split.
      - rewrite /maxDirect. word.
      - assert (int.val sz <= maxDirect) as Hszle.
        { rewrite /maxDirect. word. }
        rewrite (HnumInd2 Hszle).
        word.
      - rewrite /MaxBlocks /maxDirect /maxIndirect /indirectNumBlocks; word.
      - intros. rewrite /maxDirect in H. contradiction.
      - intros.
        assert (int.val sz <= maxDirect) as Hszle.
        { rewrite /maxDirect. word. }
        rewrite (HnumInd2 Hszle).
        word.
    }

    iIntros (s b) "(Hb & %Hencded & ? & ? & ? & ? & ?)"; iNamed.
    wp_loadField.
    wp_apply (wp_Write_fupd ⊤
                            ("HP" ∷ P (set inode.blocks (λ bs, bs ++ [b0]) σ) ∗

                "Hhdr" ∷ int.val σ.(inode.addr) d↦ b ∗
                            "HQ" ∷ Q AppendOk) with "[$Hb Hhdr Hfupd HP]").
    { iMod ("Hfupd" $! σ _ AppendOk with "[%] [%] HP") as "[HP HQ]"; auto.
      { split; eauto.
        split; try congruence.
        rewrite /inode.size.
        rewrite -HszEqLen. word.
      }
      iExists hdr; iFrame.
      iModIntro. iNext.
      by iIntros "$". }
    iIntros "(Hs&Hpost)"; iNamed "Hpost".
    wp_loadField.
    wp_apply (release_spec with "[$Hlock $His_locked HP Hhdr addr size direct indirect Hdirect Hindirect HdataDirect HdataIndirect]").
    {
      iExists σ; iFrame.
Admitted.
(*      iExists direct_s, indirect_s, dirAddrs, indAddrs, sz, numInd, indBlocks, hdr. iFrame "∗ %".
      iPureIntro; repeat (split; auto).
    }

    wp_apply (release_spec with "[$Hlock $His_locked addr addrs Haddrs HP Hhdr Hdata Ha]").
    { iExists _; iFrame.
      iExists _, _, _, _; iFrame "∗ %".
      iSplitR.
      - iPureIntro.
        rewrite /inode.wf /=.
        autorewrite with len; simpl.
        rewrite -Hlen2 Hlen1; word.
      - simpl.
        iApply (big_sepL2_app with "[$Hdata] [Ha]").
        simpl; iFrame. }
    wp_pures.
    change #(U8 0) with (to_val AppendOk).
    iApply "HΦ"; iFrame.
    rewrite bool_decide_eq_true_2; auto.
Qed.
*)
End goose.
