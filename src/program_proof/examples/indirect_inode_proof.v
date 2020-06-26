From RecordUpdate Require Import RecordSet.

From Perennial.goose_lang Require Import crash_modality.

From Goose.github_com.mit_pdos.perennial_examples Require Import indirect_inode.

From Perennial.program_proof.examples Require Import alloc_crash_proof.
(*From Perennial.program_proof.examples Require Import alloc_proof.*)
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
         addr: u64;
         direct_addrs: gset u64;
         indirect_addrs: gmap u64 (gset u64);
         blocks: list Block;
         blocks_indirect: list Block; }.
  Global Instance _eta: Settable _ := settable! mk <addr; direct_addrs; indirect_addrs; blocks; blocks_indirect>.
  Global Instance _witness: Inhabited t := populate!.

  Definition wf σ := length σ.(blocks) ≤ MaxBlocks.
  Definition size σ := length σ.(blocks).
End inode.

Hint Unfold inode.wf MaxBlocks : word.

Section goose.
Context `{!heapG Σ}.
Context `{!crashG Σ}.
Context `{!stagedG Σ}.
Context `{!allocG Σ}.

Let inodeN := nroot.@"inode".

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

Definition num_ind σ : nat := length (σ.(inode.blocks_indirect)).

Definition is_inode_durable_with σ (dirAddrs indAddrs: list u64) (indBlkAddrsList : list (list u64)) (hdr: Block)
  : iProp Σ  :=
    "%Hwf" ∷ ⌜inode.wf σ⌝ ∗
    "%HdirAddrs_set" ∷ (⌜list_to_set (take (Nat.min (int.nat maxDirect) (length σ.(inode.blocks))) dirAddrs) = σ.(inode.direct_addrs)⌝) ∗
    "%HindAddrs_set" ∷ (⌜Forall_idx u64 (λ (index : nat) (a: u64),
                        ∃ indBlkAddrs, indBlkAddrsList !! index = Some indBlkAddrs ∧
                                       σ.(inode.indirect_addrs) !! a = Some (list_to_set indBlkAddrs))
                         0 (take (num_ind σ) indAddrs)⌝) ∗
    "%Hencoded" ∷ ⌜Block_to_vals hdr = b2val <$> encode ([EncUInt64 (length σ.(inode.blocks))] ++ (EncUInt64 <$> dirAddrs) ++ (EncUInt64 <$> indAddrs) ++ [EncUInt64 (num_ind σ)])⌝ ∗
    "%Hlen" ∷ (⌜
      maxDirect = length(dirAddrs) ∧
      maxIndirect = length(indAddrs) ∧
      (Z.of_nat (length σ.(inode.blocks))) < MaxBlocks ∧
      ((Z.of_nat (length σ.(inode.blocks))) > maxDirect ->
       (Z.of_nat (num_ind σ) = (Z.add (((length σ.(inode.blocks)) - maxDirect) `div` indirectNumBlocks) 1))) ∧
      ((length σ.(inode.blocks)) <= maxDirect -> (num_ind σ = 0%nat))⌝) ∗
    "Hhdr" ∷ (int.val σ.(inode.addr) d↦ hdr) ∗
    (* direct addresses correspond to data blocks in inode spec *)
    "HdataDirect" ∷ (let len := Nat.min (int.nat maxDirect) (length σ.(inode.blocks)) in
                     [∗ list] a;b ∈ take len dirAddrs;take len σ.(inode.blocks), int.val a d↦ b) ∗
    (* indirect addresses correspond to a block's worth of data blocks in inode spec *)
    "HdataIndirect" ∷
    ([∗ list] index↦a;indBlock ∈ take (num_ind σ) indAddrs;σ.(inode.blocks_indirect),
    ∃ indBlkAddrs padding, ⌜indBlkAddrsList !! index = Some indBlkAddrs⌝ ∗
                            is_indirect a indBlkAddrs indBlock (ind_blocks_at_index σ index) padding)
.

Definition is_inode_durable σ : iProp Σ  :=
  ∃ (dirAddrs indAddrs: list u64) indBlkAddrsList (hdr: Block),
    is_inode_durable_with σ dirAddrs indAddrs indBlkAddrsList hdr
.

Definition inode_linv (l:loc) σ : iProp Σ :=
  ∃ (direct_s indirect_s: Slice.t) (dirAddrs indAddrs: list u64) indBlkAddrsList (hdr: Block),
    "Hdurable" ∷ is_inode_durable_with σ dirAddrs indAddrs indBlkAddrsList hdr ∗
    "addr" ∷ l ↦[Inode.S :: "addr"] #σ.(inode.addr) ∗
    "size" ∷ l ↦[Inode.S :: "size"] #(length σ.(inode.blocks)) ∗
    "direct" ∷ l ↦[Inode.S :: "direct"] (slice_val direct_s) ∗
    "indirect" ∷ l ↦[Inode.S :: "indirect"] (slice_val indirect_s) ∗
    "Hdirect" ∷ is_slice direct_s uint64T 1 (take (length σ.(inode.blocks)) dirAddrs) ∗
    "Hindirect" ∷ is_slice indirect_s uint64T 1 (take (num_ind σ) indAddrs).

Definition inode_cinv σ: iProp Σ :=
  is_inode_durable σ.

Definition inode_state l (d_ref: loc) (lref: loc) : iProp Σ :=
  "#d" ∷ readonly (l ↦[Inode.S :: "d"] #d_ref) ∗
  "#m" ∷ readonly (l ↦[Inode.S :: "m"] #lref).

Definition is_inode l k P : iProp Σ :=
  ∃ (d lref: loc),
    "Hro_state" ∷ inode_state l d lref ∗
    "#Hlock" ∷ is_crash_lock inodeN inodeN k #lref (∃ σ, "Hlockinv" ∷ inode_linv l σ ∗ "HP" ∷ P σ) True.

Definition pre_inode l P σ : iProp Σ :=
  ∃ (d lref: loc),
    "Hro_state" ∷ inode_state l d lref ∗
    "Hfree_lock" ∷ is_free_lock lref ∗
    "Hlockinv" ∷ inode_linv l σ.

Global Instance is_inode_Persistent l k P:
  Persistent (is_inode l k P).
Proof. apply _. Qed.


Global Instance is_inode_crash l σ :
  IntoCrash (inode_linv l σ) (λ _, is_inode_durable σ)%I.
Proof.
  hnf; iIntros "Hinv".
  iNamed "Hinv".
  iNamed "Hdurable".
  iExists dirAddrs, indAddrs, indBlkAddrsList, hdr.
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
  int.val addr d↦ block0 -∗ inode_cinv (inode.mk addr ∅ ∅ [] []).
Proof.
  iIntros "Hhdr".
  iExists (replicate (Z.to_nat maxDirect) (U64 0)), (replicate (Z.to_nat maxIndirect) (U64 0)), [], block0.
  unfold is_inode_durable_with.
  repeat iSplit; auto.
  iPureIntro. simpl in *.
  apply Forall2_nil.
Qed.

Theorem wp_Open k {d:loc} {addr σ P} :
  addr = σ.(inode.addr) ->
  {{{ inode_cinv σ ∗ P σ }}}
    indirect_inode.Open #d #addr
  {{{ l, RET #l; is_inode l k P }}}.
Proof.
  intros ->.
  iIntros (Φ) "(Hinode&HP) HΦ"; unfold inode_cinv; iNamed "Hinode".
  iDestruct (big_sepL2_length with "HdataDirect") as %Hblocklen.
  destruct Hlen as [HdirLen [HindirLen [HszMax [HnumInd1 HnumInd2]]]].

  wp_call.
  wp_apply (wp_Read with "Hhdr").
  iIntros (s) "(Hhdr&Hs)".
  wp_pures.
  iDestruct (slice.is_slice_to_small with "Hs") as "Hs".
  rewrite Hencoded.

  assert (encode ([EncUInt64 (length σ.(inode.blocks))] ++ (EncUInt64 <$> dirAddrs) ++ (EncUInt64 <$> indAddrs)++ [EncUInt64 (num_ind σ)] ) =
          encode ([EncUInt64 (length σ.(inode.blocks))] ++ (EncUInt64 <$> dirAddrs) ++ (EncUInt64 <$> indAddrs)++ [EncUInt64 (num_ind σ)] ) ++ [])
  as HappNil.
  { rewrite app_nil_r; auto. }
  rewrite HappNil.
  wp_apply (wp_NewDec _ _ s ([EncUInt64 (U64 (length σ.(inode.blocks)))] ++ (EncUInt64 <$> dirAddrs)++ (EncUInt64 <$> indAddrs) ++ [EncUInt64 (num_ind σ)] ) []
                      with "Hs").
  iIntros (dec) "[Hdec %Hsz]".

  wp_apply (wp_Dec__GetInt with "Hdec"); iIntros "Hdec".
  wp_pures.
  wp_apply (wp_Dec__GetInts _ _ _ dirAddrs _ ((EncUInt64 <$> indAddrs) ++ [EncUInt64 (num_ind σ)]) with "[Hdec]").
  { iFrame.
    iPureIntro.
    unfold maxDirect in *.
    word.
  }
  iIntros (diraddr_s) "[Hdec Hdiraddrs]".
  wp_pures.

  wp_apply (wp_Dec__GetInts _ _ _ indAddrs _ [EncUInt64 (num_ind σ)] with "[Hdec]").
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
    wp_apply (wp_SliceTake uint64T (num_ind σ)).
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
                    (∃ σ, "Hlockinv" ∷ inode_linv l σ ∗ "HP" ∷ P σ)%I
            with "[$Hlock] [-HΦ]") as "#Hlock".
    { iExists _; iFrame.
      iExists (slice_take diraddr_s uint64T (U64 (length σ.(inode.blocks)))), (slice_take indaddr_s uint64T (num_ind σ)),
      dirAddrs, indAddrs, indBlkAddrsList, hdr.
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
    iAssert (is_crash_lock inodeN inodeN k #lref (∃ σ, inode_linv l σ ∗ P σ) True) as "#Hcrash_lock".
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
    wp_apply (wp_SliceTake uint64T (num_ind σ)).
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
                    (∃ σ, "Hlockinv" ∷ inode_linv l σ ∗ "HP" ∷ P σ)%I
            with "[$Hlock] [-HΦ]") as "#Hlock".
    { iExists _; iFrame.
      iExists (slice_take diraddr_s uint64T 500), (slice_take indaddr_s uint64T (num_ind σ)),
      dirAddrs, indAddrs, indBlkAddrsList, hdr.
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
          iPoseProof (is_slice_take_cap indaddr_s uint64T (u64val <$> indAddrs) (num_ind σ) with "Hindaddrs") as "H".
          { rewrite fmap_length -HindirLen /maxIndirect HnumInd; unfold maxIndirect in Hbound; word. }
          by replace (int.nat (U64 (Z.of_nat (num_ind σ)))) with (num_ind σ) by word.
        }
    }
    iAssert (is_crash_lock inodeN inodeN k #lref (∃ σ, inode_linv l σ ∗ P σ) True) as "#Hcrash_lock".
    { admit. }
    iModIntro.
    iApply "HΦ".
    iExists _, _; iFrame "#".
  }
Admitted.

Theorem is_inode_durable_size σ (dirAddrs : list u64) (indBlkAddrsList: list (list u64)):
  is_inode_durable σ -∗ ⌜((length dirAddrs) + (foldl (λ n x, n + (length x)) 0 indBlkAddrsList)
                         = length σ.(inode.blocks))%nat⌝.
Proof.
  iNamed 1.
  iDestruct (big_sepL2_length with "HdataDirect") as "%H1".
  iDestruct (big_sepL2_length with "HdataIndirect") as "%H2".
Admitted.

Definition slice_subslice A n m s := slice_skip (slice_take s A m) A n.

Definition is_alloced_blocks_slice σ s (direct_s indirect_s indblks_s : Slice.t)
           (dirAddrs indAddrs : list u64) (indBlkAddrsList: list (list u64)) : iProp Σ :=
      is_slice direct_s uint64T 1 (take (length σ.(inode.blocks)) dirAddrs) ∗
      is_slice indirect_s uint64T 1 (take (num_ind σ) indAddrs) ∗
      is_slice indblks_s uint64T 1 (foldl (λ acc ls, acc ++ ls) [] indBlkAddrsList) ∗
      ⌜slice_subslice uint64T 0 (direct_s.(Slice.sz)) s = direct_s ∧
      slice_subslice uint64T (direct_s.(Slice.sz)) ((int.nat direct_s.(Slice.sz)) + (int.nat indirect_s.(Slice.sz)))%nat s = indirect_s ∧
      slice_subslice uint64T ((int.nat direct_s.(Slice.sz)) + (int.nat indirect_s.(Slice.sz)))%nat s.(Slice.sz) s = indblks_s⌝.

Theorem wp_Inode__UsedBlocks {l γ addr σ} :
  {{{ pre_inode l addr σ }}}
    Inode__UsedBlocks #l
    {{{ (s direct_s indirect_s indblks_s:Slice.t)
          (dirAddrs indAddrs: list u64) (indBlkAddrsList: list (list u64)),
      RET (slice_val s);
      is_alloced_blocks_slice σ s direct_s indirect_s indblks_s dirAddrs indAddrs indBlkAddrsList ∗
      (⌜list_to_set (take (Nat.min (int.nat maxDirect) (length σ.(inode.blocks))) dirAddrs) = σ.(inode.direct_addrs)⌝) ∗
      (⌜Forall_idx u64 (λ (index : nat) (a: u64),
                        ∃ indBlkAddrs, indBlkAddrsList !! index = Some indBlkAddrs ∧
                                       σ.(inode.indirect_addrs) !! a = Some (list_to_set indBlkAddrs))
        0 (take (num_ind σ) indAddrs)⌝) ∗
     (is_alloced_blocks_slice σ s direct_s indirect_s indblks_s dirAddrs indAddrs indBlkAddrsList -∗ pre_inode l addr σ) }}}.
Proof.
  iIntros (Φ) "Hinode HΦ"; iNamed "Hinode".
  wp_call.
  iNamed "Hlockinv".
  wp_apply wp_ref_of_zero; auto.
  iIntros (l0) "Hl0".
  wp_let.
  Check wp_NewSlice.
  wp_apply wp_NewSlice; auto.
  {
    admit.
  }
  iIntros (s) "Hs".
  wp_store.
Admitted.

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
        (indBlk: Block) (indBlkAddrs : list u64)
        (index: nat) (d : loc) (a : u64) (padding: list u64):
  {{{
    "%Hwf" ∷ ⌜inode.wf σ⌝ ∗
    "%Hlen" ∷ ⌜Z.of_nat (length(indAddrs)) = int.val maxIndirect ∧ numInd <= maxIndirect⌝ ∗
    "#d" ∷ readonly (l ↦[Inode.S :: "d"] #d) ∗
    "%Haddr" ∷ ⌜Some a = (take (numInd) indAddrs) !! index⌝ ∗
    "%HindBlk" ∷ ⌜Some indBlk = σ.(inode.blocks_indirect) !! index⌝ ∗
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

Theorem wp_Inode__Read k {l P} {off: u64} Q :
  {{{ is_inode l k P ∗
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
  iIntros (Φ) "(Hinode&Hfupd) HΦ"; iNamed "Hinode"; iNamed "Hro_state".
  wp_call.
  wp_loadField.
  wp_apply (crash_lock.acquire_spec with "Hlock"); auto.
  iIntros "His_locked".
  wp_pures.

  iAssert ((∃ σ, inode_linv l σ ∗ P σ)%I) as (σ) "(-#Hlockinv & -#HP)". { admit. }
  iNamed "Hlockinv".
  iNamed "Hdurable".
  destruct Hlen as [HdirLen [HindirLen [HszMax [HnumInd1 HnumInd2]]]].
  wp_loadField.
  wp_op.
  wp_if_destruct;
    replace (int.val (U64 (Z.of_nat (length σ.(inode.blocks))))) with (Z.of_nat (length σ.(inode.blocks))) in Heqb
    by (unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *; word).
  - iMod ("Hfupd" $! σ σ with "[$HP]") as "[HP HQ]".
    { iPureIntro.
      eauto. }
    wp_loadField.
    wp_apply (crash_lock.release_spec with "His_locked"); auto.
    (*{ iExists _; iFrame.
      iExists addrs.
      iExists direct_s, indirect_s, dirAddrs, indAddrs, sz, numInd, hdr. iFrame "∗ %".
      iPureIntro. repeat (split; auto).
    }*)
    wp_pures.
    change slice.nil with (slice_val Slice.nil).
    iApply "HΦ"; iFrame.
    rewrite lookup_ge_None_2 //.
    word.
  - wp_op.
    assert (int.val off < length σ.(inode.blocks)) as Hszoff by lia.
    unfold maxDirect in *.
    wp_if_destruct.

    (* Is direct block *)
    {
      wp_loadField.
      destruct (list_lookup_lt _ dirAddrs (int.nat off)) as [addr Hlookup].
      { rewrite /maxDirect. word. }
      iDestruct (is_slice_split with "Hdirect") as "[Hdirect_small Hdirect]".
      wp_apply (wp_SliceGet _ _ _ _ _ (take (length (σ.(inode.blocks))) dirAddrs) _ addr with "[Hdirect_small]").
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
      iExists _; iFrame.
    }


    (* Is indirect block *)
    {
      wp_apply wp_indNum.
      { iPureIntro. auto. }

      iIntros (v) "%Hv".

      (* Here are a bunch of facts *)
      assert (int.val off >= int.val 500) as Hoff500 by word.
      assert (length σ.(inode.blocks) > 500) as Hsz by word.
      assert (num_ind σ <= maxIndirect) as HnumIndMax.
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

      assert (int.val v < num_ind σ) as HvMax. {
        unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *. word.
      }
      destruct (list_lookup_lt _ (take (num_ind σ) indAddrs) (int.nat v)) as [addr Hlookup].
      {
        unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
        rewrite firstn_length Hv.
        rewrite Min.min_l; word.
      }
      destruct (list_lookup_lt _ (σ.(inode.blocks_indirect)) (int.nat v)) as [indBlk HlookupBlk].
      {
        unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
        unfold num_ind in *; word.
      }

      (* Now we actually step through the program *)
      wp_loadField.
      iDestruct (is_slice_split with "Hindirect") as "[Hindirect_small Hindirect]".
      wp_apply (wp_SliceGet _ _ _ _ 1 (take (num_ind σ) indAddrs) _ addr with "[Hindirect_small]"); iFrame; auto.

      iIntros "Hindirect_small".
      iDestruct (is_slice_split with "[$Hindirect_small $Hindirect]") as "Hindirect".
      iDestruct (big_sepL2_lookup_acc _ (take (num_ind σ) indAddrs) _ (int.nat v) addr with "HdataIndirect") as "[Hb HdataIndirect]"; eauto.

      wp_loadField.
      iDestruct "Hb" as (indBlkAddrs padding) "[%HaddrLookup HaddrIndirect]".
      wp_apply (wp_readIndirect indirect_s (num_ind σ) indAddrs indBlk
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
          - unfold num_ind, maxIndirect in *. word.
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
              apply (Z.lt_le_trans (int.val v) (num_ind σ) 10); auto.
            }
            rewrite Hv.
            word_cleanup.
            admit.
          - rewrite Hv.
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
      iAssert (∃ indBlkAddrs padding,
                  ⌜indBlkAddrsList !! int.nat v = Some indBlkAddrs⌝ ∗
                  is_indirect addr indBlkAddrs indBlk (ind_blocks_at_index σ (int.nat v)) padding)%I
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
      iExists _; iDestruct (is_slice_split with "Hs") as "[Hs_small Hs]"; eauto.
    }
Admitted.

Theorem wp_Inode__Size k {l P} (Q: u64 -> iProp Σ) :
  {{{ is_inode l k P ∗
      (∀ σ σ',
          ⌜σ' = σ⌝ ∗
          P σ ={⊤}=∗ P σ' ∗ Q (length σ'.(inode.blocks)))
  }}}
    Inode__Size #l
  {{{ sz, RET #sz; Q sz }}}.
Proof.
  iIntros (Φ) "(Hinv & Hfupd) HΦ"; iNamed "Hinv"; iNamed "Hro_state".
  wp_call.
  wp_loadField.
  wp_apply (crash_lock.acquire_spec with "Hlock"); auto.
  iIntros "His_locked".
  wp_pures.

  iAssert ((∃ σ, inode_linv l σ ∗ P σ)%I) as (σ) "(-#Hlockinv & -#HP)". { admit. }
  iNamed "Hlockinv".
  iNamed "Hdurable".
  wp_loadField.
  wp_let.
  wp_loadField.
  iMod ("Hfupd" $! σ σ with "[$HP]") as "[HP HQ]".
  { iPureIntro.
    split; auto.
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
      replace (Z.to_nat (int.val (88 - 8 * numInd) - 8 * int.val (10 - int.val indirect_s.(Slice.sz)) - 8))
        with (int.nat 0) by (rewrite -HallocedIndAddrsLen; word).
      rewrite replicate_0 app_nil_r.
      rewrite -HallocedIndAddrsLen.
      assert (indirect_s.(Slice.sz) = numInd) as foo by word; rewrite foo.
      repeat (rewrite -app_assoc).
      word_cleanup. reflexivity.
    + rewrite H0.
      rewrite H; reflexivity.
Qed.

Definition reserve_fupd E (Palloc: alloc.t → iProp Σ) : iProp Σ :=
  ∀ (σ σ': alloc.t) ma,
    ⌜match ma with
     | Some a => a ∈ alloc.free σ ∧ σ' = <[a:=block_reserved]> σ
     | None => σ' = σ ∧ alloc.free σ = ∅
     end⌝ -∗
  Palloc σ ={E}=∗ Palloc σ'.

(* free really means unreserve (we don't have a way to unallocate something
marked used) *)
Definition free_fupd E (Palloc: alloc.t → iProp Σ) (a:u64) : iProp Σ :=
  ∀ (σ: alloc.t),
    ⌜σ !! a = Some block_reserved⌝ -∗
  Palloc σ ={E}=∗ Palloc (<[a:=block_free]> σ).

Definition use_fupd E (Palloc: alloc.t → iProp Σ) (a: u64): iProp Σ :=
  (∀ σ : alloc.t,
      ⌜σ !! a = Some block_reserved⌝ -∗
                     Palloc σ ={E}=∗ Palloc (<[a:=block_used]> σ)).

Let Ψ (a: u64) := (∃ b, int.val a d↦ b)%I.
Let allocN := nroot.@"allocator".

Theorem wpc_Inode__Append {k E2}
        {l γ k' P}
        (* allocator stuff *)
        {Palloc γalloc domain n}
        (Q: iProp Σ) (Qc: iProp Σ)
        (alloc_ref: loc) q (b_s: Slice.t) (b0: Block) :
  (S (S k) < n)%nat →
  (S (S k) < k')%nat →
  ↑nroot.@"readonly" ⊆ (@top coPset _) ∖ ↑Ncrash allocN →
  {{{ "Hinode" ∷ is_inode l (LVL k') P ∗
      "Hbdata" ∷ is_block b_s q b0 ∗
      "HQc" ∷ (Q -∗ Qc) ∗
      "#Halloc" ∷ is_allocator Palloc Ψ allocN alloc_ref domain γalloc n ∗
      "#Halloc_fupd" ∷ □ reserve_fupd (⊤ ∖ ↑allocN) Palloc ∗
      "#Hfree_fupd" ∷ □ (∀ a, free_fupd (⊤ ∖ ↑allocN) Palloc a) ∗
      "Hfupd" ∷ ((∀ σ σ' addr',
        ⌜length σ.(inode.blocks) < maxDirect -> σ' = set inode.blocks (λ bs, bs ++ [b0])
                              (set inode.direct_addrs ({[addr']} ∪.) σ)⌝ -∗
        ⌜length σ.(inode.blocks) >= maxDirect -> ∀ (addrs' : gset u64), σ' = set inode.blocks (λ bs, bs ++ [b0])
                              (set inode.indirect_addrs (<[addr':=addrs']>) σ)⌝ -∗
        ⌜inode.wf σ⌝ -∗
        ∀ s,
        ⌜s !! addr' = Some block_reserved⌝ -∗
         ▷ P σ ∗ ▷ Palloc s ={⊤ ∖ ↑allocN ∖ ↑inodeN}=∗
         ▷ P σ' ∗ ▷ Palloc (<[addr' := block_used]> s) ∗ Q) ∧ Qc)
  }}}
    Inode__Append #l (slice_val b_s) #alloc_ref @ NotStuck; LVL (S (S k)); ⊤; E2
  {{{ (ok: bool), RET #ok; if ok then Q else emp }}}
  {{{ Qc }}}.
Proof.
  iIntros (??? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
  iNamed "Hinode". iNamed "Hro_state".
  wpc_call.
  { iRight in "Hfupd"; auto. }
  iCache with "HΦ Hfupd".
  { crash_case.
    iRight in "Hfupd"; auto. }
  wpc_apply (wpc_Reserve _ _ _ (λ ma, emp)%I emp with "[$Halloc]"); auto.
  { (* Reserve fupd *)
    iSplit; auto.
    iIntros (σ σ' ma Htrans) "HP".
    (* XXX Why is this working for inode_proof but not here??? *)
    admit. (*iMod ("Halloc_fupd" with "[] HP"); eauto. *)
  }
  iSplit.
  { iIntros "_"; iFromCache. }
  iIntros "!>" (a ok) "Hblock".
  wpc_pures.
  wpc_if_destruct.
  - wpc_pures.
    iRight in "HΦ".
    by iApply "HΦ".
  - iDestruct "Hblock" as "[_ Hb]".
    wpc_pures.
    wpc_bind_seq.

    (*XXX I am not really sure what this does *)
    iApply (prepare_reserved_block_reuse with "Hb"); auto.
    iSplit; first by iFromCache.
    iIntros "Hb Hreserved".
    iDeexHyp "Hb".
    iAssert (□ ∀ b0 R1 R2, int.val a d↦ b0 ∗
                       ((Qc -∗ Φc) ∧ R1) ∗
                       (R2 ∧ Qc) -∗
                      Φc ∗ ▷ block_cinv Ψ γalloc a)%I as "#Hbc".
    { iIntros "!>" (b' R1 R2) "(Hb&HΦ&Hfupd)".
      iRight in "Hfupd".
      iSplitL "HΦ Hfupd".
      { crash_case; auto. }
      iApply block_cinv_free_pred.
      iExists _; iFrame. }

    iCache with "HΦ Hfupd Hb".
    { iApply ("Hbc" with "[$]"). }
    wpc_apply (wpc_Write' with "[$Hb $Hbdata]").
    iSplit.

    { iIntros "[Hb|Hb]"; try iFromCache.
      iApply ("Hbc" with "[$]"). }
    iIntros "!> [Hda _]".
    iFrame "Hreserved".
    iSplitR "Hda"; last first.
    { instantiate (1:=λ _, _); simpl.
      iSplitL; [ iAccu | ].
      iAlways.
      iIntros "Hda".
      iApply block_cinv_free_pred. iExists _; iFrame. }
    iIntros "Hreserved".
    iSplit; first iFromCache.
    wpc_pures.
    wpc_frame_seq.
    wp_loadField.
    wp_apply (crash_lock.acquire_spec with "Hlock"); auto.
    iIntros "His_locked". iNamed 1.
    wpc_pures.
    wpc_bind_seq.

    (* Check Total Size invocation *)
    wpc_call.
    crash_lock_open "His_locked".
    iNamed 1.
    iNamed "Hlockinv".
    iCache with "HΦ Hfupd HP Hdurable".
    { iSplitL "HΦ Hfupd"; first by iFromCache. auto.
      (*iExists _; iFrame.
      iExists _; iFrame.*) }

    wpc_frame.
    wp_loadField.
    wp_pures.

    wp_if_destruct; iNamed 1.
    { (* Size is too large *)
      iSplitR "HP Hdurable direct Hdirect indirect Hindirect size addr"; last first.
      { iExists _; iFrame.
        iExists _, _, _, _, _, _; iFrame "∗ %". }
      iIntros "His_locked".
      iSplit; first iFromCache.
      wpc_pures.
      wpc_frame_seq.
      wp_loadField.
      wp_apply (crash_lock.release_spec with "His_locked"); auto.
      iNamed 1.
      wpc_pures.
      wpc_frame_seq.
      wp_apply (wp_Free _ _ _ emp with "[$Halloc Hreserved]").
      { auto. }
      { auto. }
      { iSplitL "Hreserved".
        { admit. (*XXX Now this doesn't work either? *)
                 (*iApply (reserved_block_weaken with "[] Hreserved").
          iIntros "!> Hda".
          iExists _; iFrame.*) }
        iIntros (σ' Hreserved) "HP".
        (* XXX ? iMod ("Hfree_fupd" with "[//] HP") as "$". *)
        (* auto *)
        admit. }
      iIntros "_".
      wp_pures.
      iNamed 1.
      wpc_pures.
      iRight in "HΦ".
      iApply "HΦ"; auto.
    }
    { (* Size was ok, proceed to see if we can directly append *)
      iSplitR "HP Hdurable direct Hdirect indirect Hindirect size addr"; last first.
      { iExists _; iFrame.
        iExists _, _, _, _, _, _; iFrame "∗ %". }
      iIntros "His_locked".
      iSplit; first iFromCache.

      crash_lock_open "His_locked". iNamed 1. iNamed "Hlockinv". iNamed "Hdurable".
      destruct Hlen as [HdirLen [HindirLen [HszMax [HnumInd1 HnumInd2]]]].
      iCache with "HΦ Hfupd HP".
      { iSplitL "HΦ Hfupd"; first by iFromCache. auto.
      (*iExists _; iFrame.
      iExists _; iFrame.*) }

      wpc_pures.
      wpc_frame_seq.

      (* Invoke appendDirect *)
      wp_call.
      wp_loadField.
      wp_if_destruct.
      + (* We have enough space to append direct block! *)
        iDestruct (is_slice_sz with "Hdirect") as %Hlen1.
        iDestruct (is_slice_sz with "Hdirect") as %HlenDir.
        iDestruct (is_slice_sz with "Hindirect") as %HlenInd.
        unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
        replace (int.val (U64 (Z.of_nat (length σ0.(inode.blocks))))) with (Z.of_nat (length σ0.(inode.blocks))) in Heqb0 by word.

        wp_loadField.
        wp_apply (wp_SliceAppend (V:=u64) with "[$Hdirect]").
        { iPureIntro.
          rewrite /list.untype fmap_take /fmap_length in Hlen1.
          rewrite take_length Min.min_l in Hlen1; try word.
          rewrite fmap_length. word.
        }
        iIntros (direct_s') "Hdirect".
        Transparent slice.T.
        wp_storeField.
        wp_loadField.
        wp_storeField.
        wp_apply (wp_Inode__mkHdr l
                                (length σ0.(inode.blocks) + 1)
                                (length σ0.(inode.blocks_indirect))
                                (take (length σ0.(inode.blocks)) dirAddrs0 ++ [a])
                                (take (length σ0.(inode.blocks_indirect)) indAddrs0)
                                direct_s' indirect_s0 _ with "[direct indirect size Hdirect Hindirect]").
        {
          iFrame.
          replace (word.add (U64 (Z.of_nat (length σ0.(inode.blocks)))) (U64 1))
                 with (U64 (Z.of_nat (length σ0.(inode.blocks)) + 1)); auto; word.
        }
        iIntros (s b') "(Hb & %Hencoded' &?&?&?&?&?)"; iNamed.
        wp_let.
        wp_loadField.
        wp_apply (wp_Write with "[Hhdr Hb]").
        { iExists hdr0; iFrame. }

        iIntros "[Hhdr Hb]".
        wp_pures.
        iIntros "(? & ? & ?)"; iNamed.
        wpc_pures.
        wpc_frame_seq.
        wp_loadField.
        (* XXX Where did all the lock facts go???
        wp_apply (crash_lock.release_spec with "His_locked"). *)
        admit.
      + (*Let's check to see if indirect blocks have room*)
        iIntros "(?&?&?)"; iNamed.
        wpc_pures.
        admit.
    }
Admitted.
End goose.
