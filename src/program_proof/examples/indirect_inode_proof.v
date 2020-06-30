From RecordUpdate Require Import RecordSet.
From Perennial.goose_lang Require Import crash_modality.

From Goose.github_com.mit_pdos.perennial_examples Require Import indirect_inode.

From Perennial.program_proof.examples Require Import alloc_crash_proof.
From Perennial.goose_lang.lib Require Import lock.crash_lock.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import typed_slice.
From Perennial.Helpers Require Import List.
From Perennial.program_proof Require Import marshal_proof disk_lib.

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
    mk { (* addresses consumed by this inode *)
         addrs: gset u64;
         blocks: list Block; }.
  Global Instance _eta: Settable _ := settable! mk <addrs; blocks>.
  Global Instance _witness: Inhabited t := populate!.

  Definition wf σ := length σ.(blocks) ≤ MaxBlocks.
  Definition size σ := length σ.(blocks).
End inode.
(*Module inode.
  Record t :=
    mk { (* addresses consumed by this inode *)
         addr: u64;
         direct_addrs: gset u64;
         indirect_addrs: gmap u64 (gset u64);
         blocks: list Block;
         blocks_indirect: list Block; }.
  Global Instance _eta: Settable _ := settable! mk <addr; direct_addrs; indirect_addrs; blocks; blocks_indirect>.
  Global Instance _witness: Inhabited t := populate!.

  Definition wf σ := length σ.(blocks) ≤ MaxBlocks.
  Definition size σ := length σ.(blocks).
End inode.*)

Hint Unfold inode.wf MaxBlocks indirectNumBlocks maxDirect maxIndirect: word.

Section goose.
Context `{!heapG Σ}.
Context `{!crashG Σ}.
Context `{!stagedG Σ}.
Context `{!allocG Σ}.

Context (inodeN allocN: namespace).

Implicit Types (σ: inode.t).
Implicit Types (l:loc) (γ:gname) (P: inode.t → iProp Σ).

Definition is_indirect (a: u64) (indBlkAddrs: list u64) (indBlock : Block)
           (specBlocks : list Block) (padding : list u64): iProp Σ :=
  "diskAddr" ∷ int.val a d↦ indBlock ∗
  "%Hencoded" ∷ ⌜Block_to_vals indBlock = b2val <$> encode ((EncUInt64 <$> indBlkAddrs) ++ (EncUInt64 <$> padding))⌝ ∗
  "%Hlen" ∷ ⌜length(indBlkAddrs) = length(specBlocks)⌝ ∗
  "Hdata" ∷ ([∗ list] a;b ∈ indBlkAddrs;specBlocks, int.val a d↦ b)
.

Definition ind_blocks_at_index σ index : list Block :=
  let begin := int.nat (int.nat maxDirect + (index * (int.nat indirectNumBlocks))) in
  List.subslice begin (begin + (int.nat indirectNumBlocks)) σ.(inode.blocks).

Definition is_inode_durable_with σ (addr: u64) (hdr: Block)
           (numInd : nat) (dirAddrs indAddrs: list u64) (indBlkAddrsList : list (list u64))
           (indBlocks : list Block)
  : iProp Σ  :=
    "%Hwf" ∷ ⌜inode.wf σ⌝ ∗
    "%Haddrs_set" ∷ ⌜list_to_set (take (length σ.(inode.blocks)) dirAddrs
                                       ++ (take numInd indAddrs)
                                       ++ (foldl (λ acc ls, acc ++ ls) [] indBlkAddrsList))
    = σ.(inode.addrs)⌝ ∗
    "%Hencoded" ∷ ⌜Block_to_vals hdr = b2val <$> encode ([EncUInt64 (length σ.(inode.blocks))]
                                                           ++ (EncUInt64 <$> (take (length σ.(inode.blocks)) dirAddrs))
                                                           ++ (EncUInt64 <$> (replicate (int.nat (maxDirect) - (min (length σ.(inode.blocks)) (int.nat maxDirect))) (U64 0)))
                                                           ++ (EncUInt64 <$> (take (numInd)) indAddrs)
                                                           ++ (EncUInt64 <$> (replicate (int.nat (maxIndirect) - numInd) (U64 0)))
                                                           ++ [EncUInt64 numInd])⌝ ∗
    "%Hlen" ∷ (⌜
      maxDirect = length(dirAddrs) ∧
      maxIndirect = length(indAddrs) ∧
      (Z.of_nat (length σ.(inode.blocks))) < MaxBlocks ∧
      ((Z.of_nat (length σ.(inode.blocks))) > maxDirect ->
       (Z.of_nat (numInd) = (Z.add (((length σ.(inode.blocks)) - maxDirect) `div` indirectNumBlocks) 1))) ∧
      ((length σ.(inode.blocks)) <= maxDirect -> (numInd = 0%nat)) ∧
      numInd = length(indBlocks)⌝) ∗
    "Hhdr" ∷ (int.val addr d↦ hdr) ∗
    (* direct addresses correspond to data blocks in inode spec *)
    "HdataDirect" ∷ (let len := Nat.min (int.nat maxDirect) (length σ.(inode.blocks)) in
                     [∗ list] a;b ∈ take len dirAddrs;take len σ.(inode.blocks), int.val a d↦ b) ∗
    (* indirect addresses correspond to a block's worth of data blocks in inode spec *)
    "HdataIndirect" ∷
    ([∗ list] index↦a;indBlock ∈ take (numInd) indAddrs;indBlocks,
    ∃ indBlkAddrs padding, ⌜indBlkAddrsList !! index = Some indBlkAddrs⌝ ∗
                            is_indirect a indBlkAddrs indBlock (ind_blocks_at_index σ index) padding)
.

Definition is_inode_durable σ addr : iProp Σ  :=
  ∃ (hdr: Block) (numInd: nat ) (dirAddrs indAddrs: list u64) indBlkAddrsList (indBlocks : list Block),
    is_inode_durable_with σ addr hdr numInd dirAddrs indAddrs indBlkAddrsList indBlocks
.

Definition inode_linv (l:loc) σ addr : iProp Σ :=
  ∃ (hdr: Block) (direct_s indirect_s: Slice.t) (numInd: nat) (dirAddrs indAddrs: list u64) indBlkAddrsList indBlocks,
    "Hdurable" ∷ is_inode_durable_with σ addr hdr numInd dirAddrs indAddrs indBlkAddrsList indBlocks∗
    "addr" ∷ l ↦[Inode.S :: "addr"] #addr ∗
    "size" ∷ l ↦[Inode.S :: "size"] #(length σ.(inode.blocks)) ∗
    "direct" ∷ l ↦[Inode.S :: "direct"] (slice_val direct_s) ∗
    "indirect" ∷ l ↦[Inode.S :: "indirect"] (slice_val indirect_s) ∗
    "Hdirect" ∷ is_slice direct_s uint64T 1 (take (length σ.(inode.blocks)) dirAddrs) ∗
    "Hindirect" ∷ is_slice indirect_s uint64T 1 (take (numInd) indAddrs).

Definition inode_cinv σ addr: iProp Σ :=
  is_inode_durable σ addr.

Definition inode_state l (d_ref: loc) (lref: loc) : iProp Σ :=
  "#d" ∷ readonly (l ↦[Inode.S :: "d"] #d_ref) ∗
  "#m" ∷ readonly (l ↦[Inode.S :: "m"] #lref).

Definition is_inode l k P addr : iProp Σ :=
  ∃ (d lref: loc),
    "Hro_state" ∷ inode_state l d lref ∗
    "#Hlock" ∷ is_crash_lock inodeN inodeN k #lref (∃ σ, "Hlockinv" ∷ inode_linv l σ addr ∗ "HP" ∷ P σ) True.

Definition pre_inode l P σ addr: iProp Σ :=
  ∃ (d lref: loc),
    "Hro_state" ∷ inode_state l d lref ∗
    "Hfree_lock" ∷ is_free_lock lref ∗
    "Hlockinv" ∷ inode_linv l σ addr.

Global Instance is_inode_Persistent l k P addr:
  Persistent (is_inode l k P addr).
Proof. apply _. Qed.

Global Instance is_inode_crash l σ addr:
  IntoCrash (inode_linv l σ addr) (λ _, is_inode_durable σ addr)%I.
Proof.
  hnf; iIntros "Hinv".
  iNamed "Hinv".
  iNamed "Hdurable".
  iExists hdr, numInd, dirAddrs, indAddrs, indBlkAddrsList, indBlocks.
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
  int.val addr d↦ block0 -∗ inode_cinv (inode.mk ∅ []) addr.
Proof.
  iIntros "Hhdr".
  iExists block0, 0%nat, (replicate (Z.to_nat maxDirect) (U64 0)), (replicate (Z.to_nat maxIndirect) (U64 0)), [], [].
  unfold is_inode_durable_with.
  repeat iSplit; auto.
Qed.

Theorem wp_Open k {d:loc} {addr σ P} :
  {{{ inode_cinv σ addr ∗ P σ }}}
    indirect_inode.Open #d #addr
  {{{ l, RET #l; is_inode l k P addr}}}.
Proof.
  iIntros (Φ) "(Hinode&HP) HΦ"; unfold inode_cinv; iNamed "Hinode".
  iDestruct (big_sepL2_length with "HdataDirect") as %Hblocklen.
  destruct Hlen as [HdirLen [HindirLen [HszMax [HnumInd1 [HnumInd2 HnumIndBlocks]]]]].

  wp_call.
  wp_apply (wp_Read with "Hhdr").
  iIntros (s) "(Hhdr&Hs)".
  wp_pures.
  iDestruct (slice.is_slice_to_small with "Hs") as "Hs".
  rewrite Hencoded.

  assert (encode ([EncUInt64 (length σ.(inode.blocks))] ++ (EncUInt64 <$> dirAddrs) ++ (EncUInt64 <$> indAddrs)++ [EncUInt64 (numInd)] ) =
          encode ([EncUInt64 (length σ.(inode.blocks))] ++ (EncUInt64 <$> dirAddrs) ++ (EncUInt64 <$> indAddrs)++ [EncUInt64 (numInd)] ) ++ [])
  as HappNil.
  { rewrite app_nil_r; auto. }
  rewrite HappNil.
  wp_apply (wp_NewDec _ _ s ([EncUInt64 (U64 (length σ.(inode.blocks)))] ++ (EncUInt64 <$> dirAddrs)++ (EncUInt64 <$> indAddrs) ++ [EncUInt64 (numInd)] ) []
                      with "Hs").
  iIntros (dec) "[Hdec %Hsz]".

  wp_apply (wp_Dec__GetInt with "Hdec"); iIntros "Hdec".
  wp_pures.
  wp_apply (wp_Dec__GetInts _ _ _ dirAddrs _ ((EncUInt64 <$> indAddrs) ++ [EncUInt64 (numInd)]) with "[Hdec]").
  { iFrame.
    iPureIntro.
    unfold maxDirect in *.
    word.
  }
  iIntros (diraddr_s) "[Hdec Hdiraddrs]".
  wp_pures.

  wp_apply (wp_Dec__GetInts _ _ _ indAddrs _ [EncUInt64 (numInd)] with "[Hdec]").
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

  destruct (bool_decide (int.val (length σ.(inode.blocks)) <= maxDirect)) eqn:HnumDir; unfold maxDirect in HnumDir; rewrite HnumDir; wp_pures.
  all: rewrite -wp_fupd; wp_apply wp_new_free_lock.
  all: iIntros (lref) "Hlock".
  {
    assert (length σ.(inode.blocks) <= maxDirect) as HszBound.
    {
      case_bool_decide; rewrite /maxDirect; rewrite /maxDirect in H; rewrite /MaxBlocks /maxDirect /maxIndirect /indirectNumBlocks in HszMax;
        [ | discriminate ].
      replace (int.val (U64 (Z.of_nat (length σ.(inode.blocks))))) with (Z.of_nat (length σ.(inode.blocks))) in H; word.
    }
    wp_apply (wp_SliceTake uint64T (length σ.(inode.blocks))).
    {
      assert (int.val maxDirect = int.val (diraddr_s.(Slice.sz))).
      { unfold maxDirect in *. word. }
      replace (int.val (U64 (Z.of_nat (length σ.(inode.blocks))))) with (Z.of_nat (length σ.(inode.blocks))) in H; word.
    }
    pose (HnumInd2 HszBound) as HnumInd.
    wp_apply (wp_SliceTake uint64T (numInd)).
    {
      rewrite HnumInd.
      word.
    }
    wp_apply wp_allocStruct; auto.
    iIntros (l) "Hinode".
    iDestruct (struct_fields_split with "Hinode") as "(d&m&addr&sz&direct&indirect&_)".
    iMod (readonly_alloc_1 with "d") as "#d".
    iMod (readonly_alloc_1 with "m") as "#m".
    (*TODO needs to be crash lock*)
    iMod (alloc_lock inodeN ⊤ _
                    (∃ σ addr, "Hlockinv" ∷ inode_linv l σ addr ∗ "HP" ∷ P σ)%I
            with "[$Hlock] [-HΦ]") as "#Hlock".
    { iExists _, _; iFrame.
      iExists hdr, (slice_take diraddr_s uint64T (U64 (length σ.(inode.blocks)))), (slice_take indaddr_s uint64T (numInd)),
      numInd, dirAddrs, indAddrs, indBlkAddrsList, indBlocks.
      iFrame.
      iSplit; iFrame.
      - iFrame "∗ %".
        iPureIntro. repeat (split; auto).
      - iSplitL "Hdiraddrs"; unfold is_slice; rewrite /list.untype fmap_take//.
        {
          unfold maxDirect in *.
          change (into_val.to_val <$> dirAddrs) with (u64val <$> dirAddrs).
          iPoseProof (is_slice_take_cap _ _ (u64val <$> dirAddrs) (U64 (Z.of_nat (length σ.(inode.blocks)))) with "Hdiraddrs") as "H".
          { word. }
          replace (int.nat (U64 (Z.of_nat (length σ.(inode.blocks))))) with (length σ.(inode.blocks)); auto.
          word.
        }
        {
          rewrite HnumInd.
          iApply (is_slice_take_cap indaddr_s uint64T (u64val <$> indAddrs) (0) with "Hindaddrs").
          { word. }
        }
    }
    iAssert (is_crash_lock inodeN inodeN k #lref (∃ σ, inode_linv l σ addr ∗ P σ) True) as "#Hcrash_lock".
    { admit. }
    iModIntro.
    iApply "HΦ".
    iExists _, _; iFrame "#".
  }
  {
    assert (length σ.(inode.blocks) > maxDirect) as HszBound.
    {
      case_bool_decide.
      - discriminate.
      - unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
        replace (int.val (U64 (Z.of_nat (length σ.(inode.blocks))))) with (Z.of_nat (length σ.(inode.blocks))) in H; word.
    }
    pose proof (HnumInd1 HszBound) as HnumInd.
    wp_apply (wp_SliceTake uint64T maxDirect).
    {
      assert (maxDirect = int.val (diraddr_s.(Slice.sz))).
      {
        unfold maxDirect in Hdirs_len, HdirLen. unfold maxDirect. by word.
      }
      rewrite -H; word.
    }
    wp_apply (wp_SliceTake uint64T (numInd)).
    {
      rewrite HnumInd.
      assert (((Z.of_nat (length σ.(inode.blocks))) - maxDirect) `div` indirectNumBlocks + 1 < maxIndirect + 1) as HmaxCmp. {
        rewrite Z.lt_add_lt_sub_r.
        change (maxIndirect + 1 - 1) with (maxIndirect).
        apply indirect_blocks_upperbound. auto.
      }
      unfold maxIndirect in *.
      replace (int.val indaddr_s.(Slice.sz)) with 10 by word.
      word.
    }
    wp_apply wp_allocStruct; auto.
    iIntros (l) "Hinode".
    iDestruct (struct_fields_split with "Hinode") as "(d&m&addr&sz&direct&indirect&_)".
    iMod (readonly_alloc_1 with "d") as "#d".
    iMod (readonly_alloc_1 with "m") as "#m".
    iMod (alloc_lock inodeN ⊤ _
                    (∃ σ addr, "Hlockinv" ∷ inode_linv l σ addr∗ "HP" ∷ P σ)%I
            with "[$Hlock] [-HΦ]") as "#Hlock".
    { iExists _, _; iFrame.
      iExists hdr, (slice_take diraddr_s uint64T 500), (slice_take indaddr_s uint64T (numInd)),
      numInd, dirAddrs, indAddrs, indBlkAddrsList, indBlocks.
      iFrame.
      iSplit; iFrame.
      - iFrame "∗ %".
        iPureIntro. repeat (split; auto).
      - iSplitL "Hdiraddrs"; unfold is_slice; rewrite /list.untype fmap_take//.
        {
          change (to_val <$> dirAddrs) with (u64val<$> dirAddrs).
          unfold maxDirect in HdirLen, HszBound.
          rewrite take_ge; last by len.
          iEval (rewrite -(firstn_all (u64val <$> dirAddrs)) fmap_length HdirLen /maxDirect).
          replace (length dirAddrs) with 500%nat by word.
          iApply (is_slice_take_cap with "Hdiraddrs").
          rewrite fmap_length; word.
        }
        {
          pose (indirect_blocks_upperbound (length σ.(inode.blocks))) as Hbound.
          iPoseProof (is_slice_take_cap indaddr_s uint64T (u64val <$> indAddrs) (numInd) with "Hindaddrs") as "H".
          { rewrite fmap_length -HindirLen /maxIndirect HnumInd; unfold maxIndirect in Hbound; word. }
          by replace (int.nat (U64 (Z.of_nat (numInd)))) with (numInd) by word.
        }
    }
    iAssert (is_crash_lock inodeN inodeN k #lref (∃ σ, inode_linv l σ addr ∗ P σ) True) as "#Hcrash_lock".
    { admit. }
    iModIntro.
    iApply "HΦ".
    iExists _, _; iFrame "#".
  }
Admitted.

Theorem is_inode_durable_size σ addr (dirAddrs : list u64) (indBlkAddrsList: list (list u64)):
  is_inode_durable σ addr -∗ ⌜((length dirAddrs) + (foldl (λ n x, n + (length x)) 0 indBlkAddrsList)
                         = length σ.(inode.blocks))%nat⌝.
Proof.
  iNamed 1.
  iDestruct (big_sepL2_length with "HdataDirect") as "%H1".
  iDestruct (big_sepL2_length with "HdataIndirect") as "%H2".
Admitted.

Definition slice_subslice A n m s := slice_skip (slice_take s A m) A n.

Definition is_alloced_blocks_slice σ s (direct_s indirect_s indblks_s : Slice.t)
           numInd (dirAddrs indAddrs : list u64) (indBlkAddrsList: list (list u64)) : iProp Σ :=
      is_slice direct_s uint64T 1 (take (length σ.(inode.blocks)) dirAddrs) ∗
      is_slice indirect_s uint64T 1 (take (numInd) indAddrs) ∗
      is_slice indblks_s uint64T 1 (foldl (λ acc ls, acc ++ ls) [] indBlkAddrsList) ∗
      ⌜slice_subslice uint64T 0 (direct_s.(Slice.sz)) s = direct_s ∧
      slice_subslice uint64T (direct_s.(Slice.sz)) ((int.nat direct_s.(Slice.sz)) + (int.nat indirect_s.(Slice.sz)))%nat s = indirect_s ∧
      slice_subslice uint64T ((int.nat direct_s.(Slice.sz)) + (int.nat indirect_s.(Slice.sz)))%nat s.(Slice.sz) s = indblks_s⌝.

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
        indirect_s (numInd: nat) (indAddrs : list u64)
        (indBlk: Block) (indBlkAddrs : list u64) (indBlocks: list Block)
        (index: nat) (d : loc) (a : u64) (padding: list u64):
  {{{
    "%Hwf" ∷ ⌜inode.wf σ⌝ ∗
    "%Hlen" ∷ ⌜Z.of_nat (length(indAddrs)) = int.val maxIndirect ∧ numInd <= maxIndirect⌝ ∗
    "#d" ∷ readonly (l ↦[Inode.S :: "d"] #d) ∗
    "%Haddr" ∷ ⌜Some a = (take (numInd) indAddrs) !! index⌝ ∗
    "%HindBlk" ∷ ⌜Some indBlk = indBlocks !! index⌝ ∗
    "indirect" ∷ l ↦[Inode.S :: "indirect"] (slice_val indirect_s) ∗
    "Hindirect" ∷ is_slice indirect_s uint64T 1 (take (numInd) indAddrs) ∗
    "HindBlkAddrs" ∷ is_indirect a indBlkAddrs indBlk (ind_blocks_at_index σ index) padding
  }}}
     readIndirect #d #a
  {{{ indBlkAddrs_s, RET slice_val indBlkAddrs_s;
    ∃ padding, "HindBlkIndirect" ∷ is_indirect a indBlkAddrs indBlk (ind_blocks_at_index σ index) padding ∗
    "HindBlkAddrs" ∷ is_slice indBlkAddrs_s uint64T 1 (indBlkAddrs++padding) ∗
    "indirect" ∷ l ↦[Inode.S :: "indirect"] (slice_val indirect_s) ∗
    "Hindirect" ∷ is_slice indirect_s uint64T 1 (take (numInd) indAddrs)
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

Theorem wp_Inode__UsedBlocks {l γ P addr σ} :
  {{{ pre_inode l P σ addr }}}
    Inode__UsedBlocks #l
    {{{ (s direct_s indirect_s indblks_s:Slice.t)
          numInd (dirAddrs indAddrs: list u64) (indBlkAddrsList: list (list u64)) (indBlocks: list Block),
        RET (slice_val s);
        ⌜list_to_set (take (length σ.(inode.blocks)) dirAddrs
                   ++ (take numInd indAddrs)
                   ++ (foldl (λ acc ls, acc ++ ls) [] indBlkAddrsList))
        = σ.(inode.addrs)⌝ ∗
      is_alloced_blocks_slice σ s direct_s indirect_s indblks_s numInd dirAddrs indAddrs indBlkAddrsList ∗
      (is_alloced_blocks_slice σ s direct_s indirect_s indblks_s numInd dirAddrs indAddrs indBlkAddrsList
                               -∗ pre_inode l P σ addr) }}}.
Proof.
  iIntros (Φ) "Hinode HΦ"; iNamed "Hinode".
  wp_call.
  iNamed "Hlockinv".
  wp_apply wp_ref_of_zero; auto.
  iIntros (l0) "Hl0".
  wp_let.
  wp_apply (wp_NewSlice _ _ (uint64T)).
  iIntros (s) "Hs".
  wp_store.
  wp_loadField; wp_let.
  wp_loadField; wp_let.

  iDestruct (is_slice_split with "Hdirect") as "[Hdirect_small Hdirect]".
  iDestruct (is_slice_split with "Hindirect") as "[Hindirect_small Hindirect]".
  iNamed "Hdurable".
  destruct Hlen as [HdirLen [HindirLen [HszMax [HnumInd1 [HnumInd2 HnumIndBlocks]]]]].

  wp_apply (wp_forSlicePrefix
              (fun done todo =>
               ∃ s usedBlksList,
                 "%" ∷ ⌜ done ++ todo = (take (length σ.(inode.blocks)) dirAddrs) ⌝ ∗
                 "%" ∷ ⌜ done = usedBlksList ⌝ ∗
                 "Hl0" ∷ (l0 ↦[slice.T uint64T] (slice_val s)) ∗
                 "HusedSlice" ∷ is_slice s uint64T 1 usedBlksList
      )%I
  with "[] [Hl0 Hdirect_small Hs]").
  { iIntros (i a done todo).
    iModIntro.
    iIntros (lϕ) "Hinv HΦ"; iNamed "Hinv".
    wp_pures.
    wp_load.
    wp_apply (wp_SliceAppend (V:=u64) with "[HusedSlice]").
    {
      iDestruct (is_slice_sz with "HusedSlice") as %HlenUsed.
      iSplit; eauto. iPureIntro.
      unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
      rewrite /list.untype fmap_length in HlenUsed.
      assert (length (usedBlksList ++ a :: todo) = length (take (length σ.(inode.blocks)) dirAddrs)).
      {
        rewrite -H0 H; auto.
      }
      rewrite take_length app_length in H1.
      word.
    }

    iIntros (direct_s') "Hdirect".
    wp_store.
    iApply "HΦ".
    iExists direct_s', (usedBlksList ++ [a]).
    repeat iSplit; auto.
    - iPureIntro.
      replace ((done ++ [a]) ++ todo) with (done ++ a :: todo); auto.
      rewrite cons_middle -app_assoc; auto.
    - iPureIntro; rewrite H0; auto.
    - iFrame.
  }
  {
    iFrame.
    iExists s, [].
    iFrame.
    repeat iSplit; auto.
  }

  iIntros "[Hdirect_small HdirLoop]". iNamed "HdirLoop".
  wp_pures.
  wp_apply (wp_forSlicePrefix
              (fun done todo =>
               ∃ s usedIndBlks,
                 "%" ∷ ⌜ done ++ todo = (take (numInd) indAddrs) ⌝ ∗
                 "%" ∷ ⌜ done = usedIndBlks ⌝ ∗
                 "Hl0" ∷ (l0 ↦[slice.T uint64T] (slice_val s)) ∗
                 "HusedSlice" ∷ is_slice s uint64T 1 (usedBlksList ++ usedIndBlks)
      )%I
  with "[] [Hl0 Hindirect_small indirect HusedSlice]").
  { iIntros (i a done todo).
    iModIntro.
    iIntros (lϕ) "Hinv HΦ"; iNamed "Hinv".
    wp_pures.
    wp_load.

    wp_apply (wp_SliceAppend (V:=u64) with "[HusedSlice]").
    {
      iDestruct (is_slice_sz with "HusedSlice") as %HlenUsed.
      iSplit; eauto. iPureIntro.
      unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
      rewrite /list.untype fmap_length in HlenUsed.
      assert (length (done ++ a :: todo) = length (take (numInd) indAddrs)).
      {
        rewrite -H1; auto.
      }
      rewrite take_length app_length H2 in H3.
      rewrite app_length -H0 take_length in HlenUsed.
      word.
    }

    iIntros (indirect_s') "Hindirect".
    wp_store.
    iApply "HΦ".
    iExists indirect_s', (usedIndBlks ++ [a]).
    repeat iSplit; auto.
    - iPureIntro.
      replace ((done ++ [a]) ++ todo) with (done ++ a :: todo); auto.
      rewrite cons_middle -app_assoc; auto.
    - iPureIntro. rewrite H2; auto.
    - iFrame. rewrite app_assoc; auto.
  }
  {
    iFrame.
    iExists s0, [].
    rewrite app_nil_l app_nil_r.
    iFrame.
    repeat iSplit; auto.
  }
  iIntros "[Hindirect_small HindLoop]". iNamed "HindLoop".
  wp_pures.

  (*TODO facts about readIndirect*)
  iNamed "Hro_state".
  wp_apply (wp_forSlicePrefix
              (fun done todo =>
               ∃ s indBlkAddrsList,
                 "%" ∷ ⌜ done ++ todo = (take (numInd) indAddrs) ⌝ ∗
                 "Hl0" ∷ (l0 ↦[slice.T uint64T] (slice_val s)) ∗
                 "HusedSlice" ∷ is_slice s uint64T 1 (usedBlksList ++ done ++ (foldl (λ acc x, acc ++ x) [] indBlkAddrsList)) ∗
                 "HindBlks" ∷ [∗ list] i↦a ∈ done,
                                            (∃ indBlkAddrs,
                                                ⌜ indBlkAddrsList !! i = Some indBlkAddrs ⌝ ∗
                                                ∃ indBlk padding, is_indirect a indBlkAddrs indBlk (ind_blocks_at_index σ i) padding)
      )%I
  with "[] [Hl0 Hindirect_small HusedSlice Hindirect]").
  { iIntros (i a done todo).
    iModIntro.
    iIntros (lϕ) "Hinv HΦ"; iNamed "Hinv".
    wp_pures.
    wp_loadField.
    wp_apply wp_readIndirect.
    {
      admit.
    }
    admit.
  }
Admitted.

Theorem wp_Inode__Read {l P k addr} {off: u64} Q :
  {{{ "Hinode" ∷ is_inode l k P addr ∗
      "Hfupd" ∷ (∀ σ σ' mb,
        ⌜σ' = σ ∧ mb = σ.(inode.blocks) !! int.nat off⌝ ∗
        ▷ P σ ={⊤}=∗ ▷ P σ' ∗ Q mb)
  }}}
    Inode__Read #l #off
  {{{ s mb, RET slice_val s;
      (match mb with
       | Some b => is_block s 1 b
       | None => ⌜s = Slice.nil⌝
       end) ∗ Q mb }}}.
Proof.
  iIntros (Φ) "Hpre HΦ"; iNamed "Hpre".
  iNamed "Hinode". iNamed "Hro_state".
  wp_call.
  wp_loadField.
  wp_apply (crash_lock.acquire_spec with "Hlock"); auto.
  iIntros "His_locked".
  wp_pures.

  iAssert ((∃ σ , inode_linv l σ addr ∗ P σ)%I) as (σ) "(-#Hlockinv & -#HP)". { admit. }
  iNamed "Hlockinv".
  iNamed "Hdurable".
  destruct Hlen as [HdirLen [HindirLen [HszMax [HnumInd1 [HnumInd2 HnumIndBlocks]]]]].
  wp_loadField.
  wp_op.
  wp_if_destruct;
    replace (int.val (U64 (Z.of_nat (length σ.(inode.blocks))))) with (Z.of_nat (length σ.(inode.blocks))) in Heqb
    by (unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *; word).
  - iMod ("Hfupd" $! σ σ None with "[$HP]") as "[HP HQ]".
    { iPureIntro.
      rewrite lookup_ge_None_2 //.
      word.
    }
    wp_loadField.
    wp_apply (crash_lock.release_spec with "His_locked"); auto.
    (*{ iExists _; iFrame.
      iExists addrs.
      iExists direct_s, indirect_s, dirAddrs, indAddrs, sz, numInd, hdr. iFrame "∗ %".
      iPureIntro. repeat (split; auto).
    }*)
    wp_pures.
    change slice.nil with (slice_val Slice.nil).
    iApply "HΦ"; iFrame; auto.
  - wp_op.
    assert (int.val off < length σ.(inode.blocks)) as Hszoff by lia.
    unfold maxDirect in *.
    wp_if_destruct.

    (* Is direct block *)
    {
      wp_loadField.
      destruct (list_lookup_lt _ dirAddrs (int.nat off)) as [a Hlookup].
      { rewrite /maxDirect. word. }
      iDestruct (is_slice_split with "Hdirect") as "[Hdirect_small Hdirect]".
      wp_apply (wp_SliceGet _ _ _ _ _ (take (length (σ.(inode.blocks))) dirAddrs) _ a with "[Hdirect_small]").
      { iSplit; auto.
        unfold maxDirect in *.
        iPureIntro.
        rewrite lookup_take; auto.
        word.
      }
      iIntros "Hdirect_small".
      wp_pures.
      iDestruct (big_sepL2_lookup_1_some _ _ _ (int.nat off) a with "HdataDirect") as "%Hblock_lookup"; eauto.
      { rewrite lookup_take; [auto | word]. }
      destruct Hblock_lookup as [b0 Hlookup2].
      iDestruct (is_slice_split with "[$Hdirect_small $Hdirect]") as "Hdirect".
      iDestruct (big_sepL2_lookup_acc _ _ _ _ a with "HdataDirect") as "[Hb HdataDirect]"; eauto.
      { rewrite lookup_take; [auto | word]. }
      wp_apply (wp_Read with "Hb"); iIntros (s) "[Hb Hs]".
      iSpecialize ("HdataDirect" with "Hb").
      wp_loadField.
      iMod ("Hfupd" $! σ σ with "[$HP]") as "[HP HQ]".
      { iPureIntro; eauto. }
      wp_apply (crash_lock.release_spec with "His_locked"); auto.
      (*wp_apply (release_spec with "[$Hlock $His_locked HP Hhdr addr
             size direct indirect Hdirect Hindirect HdataDirect HdataIndirect]").
      { iExists _; iFrame.
        iExists addrs.
        iExists direct_s, indirect_s, dirAddrs, indAddrs, sz, numInd, hdr. iFrame "∗ %".
        iPureIntro; repeat (split; auto).
      }*)
      wp_pures.
      iApply "HΦ"; iFrame.
      rewrite lookup_take in Hlookup2; [ | word ].
      rewrite Hlookup2.
      iDestruct (is_slice_split with "Hs") as "[Hs _]".
      iFrame.
    }

    (* Is indirect block *)
    {
      wp_apply wp_indNum.
      { iPureIntro. auto. }

      iIntros (index) "%Hindex".

      (* Here are a bunch of facts *)
      assert (int.val off >= int.val 500) as Hoff500 by word.
      assert (length σ.(inode.blocks) > 500) as Hsz by word.
      assert (numInd <= maxIndirect) as HnumIndMax.
      {
         unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
         assert (((length σ.(inode.blocks) - 500) `div` 512) < 10) as H.
          {
            apply (Zdiv_lt_upper_bound (length σ.(inode.blocks) - 500) 512 10); lia.
          }
          rewrite (HnumInd1 Hsz).
          lia.
      }
      assert (((int.val off - 500) `div` 512) <= ((length σ.(inode.blocks) - 500) `div` 512)) as Hoff. {
        apply Z_div_le; lia.
      }

      assert (int.val index < numInd) as HindexMax. {
        unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *. word.
      }
      destruct (list_lookup_lt _ (take (numInd) indAddrs) (int.nat index)) as [a Hlookup].
      {
        unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
        rewrite firstn_length Hindex.
        rewrite Min.min_l; word.
      }
      destruct (list_lookup_lt _ indBlocks (int.nat index)) as [indBlk HlookupBlk].
      {
        unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
        word.
      }

      (* Now we actually step through the program *)
      wp_loadField.
      iDestruct (is_slice_split with "Hindirect") as "[Hindirect_small Hindirect]".
      wp_apply (wp_SliceGet _ _ _ _ 1 (take (numInd) indAddrs) _ a with "[Hindirect_small]"); iFrame; auto.

      iIntros "Hindirect_small".
      iDestruct (is_slice_split with "[$Hindirect_small $Hindirect]") as "Hindirect".
      iDestruct (big_sepL2_lookup_acc _ (take (numInd) indAddrs) _ (int.nat index) a with "HdataIndirect") as "[Hb HdataIndirect]"; eauto.

      wp_loadField.
      iDestruct "Hb" as (indBlkAddrs padding) "[%HaddrLookup HaddrIndirect]".
      wp_apply (wp_readIndirect indirect_s numInd indAddrs indBlk
                                indBlkAddrs indBlocks (int.nat index) d a padding
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
      assert ((int.val off - 500) `div` 512 * 512 = (512 * (int.val off - 500) `div` 512)) as HMulComm.
      { replace ((int.val off - 500) `div` 512 * 512) with (512 * ((int.val off - 500) `div` 512)); word. }

      assert ((int.val off - 500) `div` 512 * 512  <= ((512 * (int.val off - 500)) `div` 512)) as HdivMulLe.
      { rewrite HMulComm. apply Z.div_mul_le; word. }

      assert (int.val index * indirectNumBlocks <= int.val off -maxDirect ∧
              int.val off -maxDirect < (int.val index * indirectNumBlocks) + indirectNumBlocks)
        as [HoffLBound HoffUBound].
      {
        split; unfold maxDirect, indirectNumBlocks in *; rewrite Hindex; auto.
        + rewrite HMulComm.
          apply Z.mul_div_le; word.
        + rewrite HMulComm.
          replace (int.val off - 500 < 512 * (int.val off - 500) `div` 512 + 512) with
              (512 * (int.val off - 500) `div` 512 + (int.val off - 500) `mod` 512 < 512 * (int.val off - 500) `div` 512 + 512)
            by (rewrite -(Z.div_mod (int.val off - 500) 512); auto).
          rewrite -Z.add_lt_mono_l.
          apply (Z_mod_lt (int.val off - 500) 512).
          word.
      }

      assert (int.val offset < length indBlkAddrs) as HoffsetInBounds.
      {
        unfold ind_blocks_at_index in Hlen.
        rewrite Hlen.
        rewrite Hoffset.
        unfold maxDirect, indirectNumBlocks in *.

        destruct (dec_ge (length σ.(inode.blocks)) ((500 + int.nat index * 512) + 512)) as [HlenGe | HlenNotGe].
        (* Subslice fully contained in blocks *)
        {
          rewrite subslice_length.
          - rewrite minus_plus.
            apply Z_mod_lt; word.
          - unfold maxIndirect in *. word.
        }
        (* Subslice goes to end of blocks *)
        {
          pose (not_ge _ _ HlenNotGe) as HlenUBound.
          rewrite subslice_to_end; [ | word ].
          rewrite skipn_length.
          word_cleanup.
          assert (int.val index * 512 < length σ.(inode.blocks) -500) as HlenLBound.
          {
            apply (Z.le_lt_trans (int.val index * 512) (int.val off - 500) (length σ.(inode.blocks) - 500));
            word.
          }
          replace (Z.of_nat (length σ.(inode.blocks) - Z.to_nat (500 + int.val index * 512))) with ((Z.of_nat (length σ.(inode.blocks)) - 500 - (int.val index * 512))) by word.
          rewrite Hindex.
          rewrite -Z.lt_add_lt_sub_l.
          rewrite HMulComm.
          rewrite -Z.div_mod; word.
        }
      }
      destruct (list_lookup_lt _ (ind_blocks_at_index σ (int.nat index)) (int.nat offset)) as [inodeblkaddr HlookupInodeBlk].
      { rewrite -Hlen. word. }
      destruct (list_lookup_lt _ (indBlkAddrs) (int.nat offset)) as [blkaddr HlookupBlkInd]; try word.
      assert ((σ.(inode.blocks)) !! (int.nat off) = Some inodeblkaddr) as HlookupInodeBlk'.
      {
        rewrite /ind_blocks_at_index Hoffset in HlookupInodeBlk.
        unfold subslice in *.
        rewrite lookup_drop in HlookupInodeBlk.
        unfold maxDirect, indirectNumBlocks in *.
        rewrite Hindex in HlookupInodeBlk.
        replace
          (int.nat
             (U64
             (Z.of_nat (int.nat (U64 500)) +
             Z.of_nat (Z.to_nat ((int.val off - 500) `div` 512)) * Z.of_nat (int.nat (U64 512)))) +
             Z.to_nat ((int.val off - 500) `mod` 512))%nat
          with
            (Z.to_nat (500 + (512 * (int.val off - 500) `div` 512) + (int.val off - 500) `mod` 512))
          in HlookupInodeBlk
          by word.
        rewrite -Z.add_assoc -(Z.div_mod (int.val off - 500) 512) in HlookupInodeBlk; [ | word ].
        replace (500 + (int.val off - 500)) with (int.val off) in HlookupInodeBlk by word.
        rewrite lookup_take in HlookupInodeBlk; auto.
        word.
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
      iAssert (∃ indBlkAddrs padding,
                  ⌜indBlkAddrsList !! int.nat index = Some indBlkAddrs⌝ ∗
                  is_indirect a indBlkAddrs indBlk (ind_blocks_at_index σ (int.nat index)) padding)%I
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

      wp_apply (crash_lock.release_spec with "His_locked"); auto.
      (*wp_apply (release_spec with "[$Hlock $His_locked HP Hhdr addr
             size direct indirect Hdirect Hindirect HdataDirect HdataIndirect]").
      { iExists _; iFrame.
        iExists addrs.
        iExists direct_s, indirect_s, dirAddrs, indAddrs, sz, numInd, hdr. iFrame "∗ %".
        iPureIntro; repeat (split; auto).
      }*)
      wp_pures.
      iApply "HΦ"; iFrame.

      rewrite HlookupInodeBlk'.
      iDestruct (is_slice_split with "Hs") as "[Hs_small Hs]"; eauto.
    }
Admitted.

Theorem wp_Inode__Size {l k' P addr} (Q: u64 -> iProp Σ) :
  {{{ "Hinode" ∷ is_inode l (LVL k') P addr ∗
      "Hfupd" ∷ (∀ σ σ' sz,
          ⌜σ' = σ ∧ int.nat sz = inode.size σ⌝ ∗
          ▷ P σ ={⊤}=∗ ▷ P σ' ∗ Q sz)
  }}}
    Inode__Size #l
  {{{ sz, RET #sz; Q sz }}}.
Proof.
  iIntros (Φ) "Hpre HΦ"; iNamed "Hpre".
  iNamed "Hinode"; iNamed "Hro_state".
  wp_call.
  wp_loadField.
  wp_apply (crash_lock.acquire_spec with "Hlock"); auto.
  iIntros "His_locked".
  wp_pures.

  iAssert ((∃ σ, inode_linv l σ addr ∗ P σ)%I) as (σ) "(-#Hlockinv & -#HP)". { admit. }
  iNamed "Hlockinv".
  iNamed "Hdurable".
  wp_loadField.
  wp_let.
  wp_loadField.
  iMod ("Hfupd" $! σ σ (length σ.(inode.blocks)) with "[$HP]") as "[HP HQ]".
  { iPureIntro.
    split; auto.
    unfold inode.size. word.
  }
  wp_apply (crash_lock.release_spec with "His_locked"); auto.
  (*wp_apply (crash_lock.release_spec with "[-HQ HΦ $Hlock]").
  { iFrame "Hlocked".
    iExists σ; iFrame.
    iExists addrs.
    iExists direct_s, indirect_s, dirAddrs, indAddrs, sz, numInd, hdr. iFrame "∗ %".
  }*)
  wp_pures.
  iApply ("HΦ" with "[$]").
Admitted.

Theorem wp_padInts {Stk E} enc (n: u64) (encoded : list encodable) (off: Z):
  {{{
    ⌜ int.val 0 ≤ int.val n ∧ off >= 8*(int.val n) ⌝ ∗
    is_enc enc encoded off
  }}}
    padInts (EncM.to_val enc) #n @Stk ; E
  {{{ RET #()
;
    is_enc enc (encoded ++ (EncUInt64 <$> replicate (int.nat n) (U64 0))) (off-(8*int.val n))
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
                       (off - (8 * int.val i)))%I _ _
                    0 n
            with "[] [Henc Hi] [-]").
  {
    word.
  }
  {
    iIntros. iModIntro. iIntros (ϕ0) "H Hϕ0".
    iDestruct "H" as "[H [Hi %Hibound]]"; destruct Hi as [Hn Hoff].
    iNamed "H".
    wp_pures.
    wp_apply (wp_Enc__PutInt with "Henc"); [ word | ].

    iIntros "Henc".
    wp_pures.
    iApply "Hϕ0".
    iFrame.
    iSplitR "Henc".
    - iPureIntro. word.
    - replace (int.nat (word.add i0 1)) with (S (int.nat i0)) by word.
      rewrite replicate_S_end.
      rewrite fmap_app; simpl.
      rewrite app_assoc.
      replace (off - 8 * int.val (word.add i0 (U64 1))) with (off - 8 * int.val i0 - 8); auto.
      word.
  }
  {
    iSplitL "Henc"; iFrame; auto.
    iSplitR "Henc".
    - iPureIntro. word.
    - rewrite replicate_0 fmap_nil app_nil_r. rewrite Z.mul_0_r Z.sub_0_r. auto.
  }

  iModIntro.
  iIntros "[H Hi]".
  destruct Hi as [Hn Hoff].
  iNamed "H".
  iApply "Hϕ"; iFrame.
Qed.

Theorem wp_Inode__mkHdr {Stk E} l (sz numInd : Z) allocedDirAddrs allocedIndAddrs direct_s indirect_s:
  (length(allocedDirAddrs) <= int.nat maxDirect ∧
   (Z.of_nat (length(allocedIndAddrs))) = numInd ∧
    sz < MaxBlocks ∧
    (sz > maxDirect -> numInd = Z.add ((sz - maxDirect) `div` indirectNumBlocks) 1) ∧
    (sz <= maxDirect -> numInd = 0)) ->
  {{{
    "direct" ∷ l ↦[Inode.S :: "direct"] (slice_val direct_s) ∗
    "indirect" ∷ l ↦[Inode.S :: "indirect"] (slice_val indirect_s) ∗
    "size" ∷ l ↦[Inode.S :: "size"] #sz ∗
    "Hdirect" ∷ is_slice direct_s uint64T 1 allocedDirAddrs ∗
    "Hindirect" ∷ is_slice indirect_s uint64T 1 allocedIndAddrs
  }}}
    Inode__mkHdr #l @ Stk; E
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

  assert (numInd <= maxIndirect) as HnumInd.
  {
    destruct (bool_decide (sz > maxDirect)) eqn:Heqsz.
    - apply bool_decide_eq_true in Heqsz.
      rewrite (HnumInd1 Heqsz).
      pose (indirect_blocks_upperbound (sz) Hszmax).
      unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
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
  replace  (int.val (U64 4096) - 8 - 8 * Z.of_nat (length allocedDirAddrs) -
              8 * int.val (U64 (500 - int.val direct_s.(Slice.sz)))) with 88.
  2: rewrite HDirlen; rewrite HDirlen /maxDirect in HallocedDirAddrsLen; word.

  wp_pures.
  wp_loadField.

  iDestruct (is_slice_split with "Hindirect") as "[Hindirect Hcapind]".
  wp_apply (wp_Enc__PutInts with "[$Henc $Hindirect]").
  { rewrite HallocedIndAddrsLen. rewrite /maxIndirect in HnumInd.
    word.
  }
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
      replace (Z.to_nat (88 - 8 * numInd - 8 * int.val (U64 (10 - int.val indirect_s.(Slice.sz))) - 8))
        with (int.nat 0) by (rewrite -HallocedIndAddrsLen; word).
      rewrite replicate_0 app_nil_r.
      rewrite -HallocedIndAddrsLen.
      assert (indirect_s.(Slice.sz) = numInd) as foo by word; rewrite foo.
      repeat (rewrite -app_assoc).
      word_cleanup. reflexivity.
    + rewrite H0.
      rewrite H; reflexivity.
Qed.
End goose.
