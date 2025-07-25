From RecordUpdate Require Import RecordSet.
From Perennial.goose_lang Require Import crash_modality.

From Goose.github_com.mit_pdos.perennial_examples Require Import indirect_inode.

From Perennial.program_proof.examples Require Import alloc_crash_proof.
From Perennial.goose_lang.lib Require Import lock.crash_lock.
From Perennial.program_proof Require Import disk_prelude.
From Perennial.goose_lang.lib Require Import typed_slice.
From Perennial.Helpers Require Import List.
From Perennial.program_proof Require Import marshal_block disk_lib.

Definition maxDirect: Z := 500.
Definition maxIndirect: Z := 10.
Definition indirectNumBlocks: Z := 512.
Definition MaxBlocks: Z := maxDirect + maxIndirect*indirectNumBlocks.
Definition roundUpDiv (x k: Z) := (x + (k-1)) / k.
Definition lastBlockFiller (blkLen : Z) (x : list (list u64)) : nat :=
   Z.to_nat ((blkLen - (length (concat x) `mod` blkLen)) `mod` blkLen).

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Lemma roundUpDiv_lt_succ (x k: Z) : x >= 0 -> k > 0 -> (x / k) < roundUpDiv x k -> (x / k) + 1 = roundUpDiv x k.
Proof.
  intros. unfold roundUpDiv in *.
  destruct (bool_decide (x `mod` k = 0)) eqn:Hx.
  + apply bool_decide_eq_true in Hx.
    rewrite (Z.div_mod x k) in H1; [|lia].
    rewrite Hx Z.add_0_r Z.mul_comm in H1.
    rewrite (Z.div_mul (x `div` k) k) in H1; [|lia].
    rewrite (Z.div_add_l (x `div` k) k (k-1)) in H1; [|lia].
    rewrite (Z.div_small (k-1) k) in H1; [|split; lia].
    lia.
  + apply bool_decide_eq_false in Hx.
    rewrite (Z.div_mod x k); [|lia].
    rewrite Z.mul_comm.
    rewrite (Z.div_add_l (x `div` k) k (x `mod` k)); [|lia].
    rewrite (Z.div_small (x `mod` k) k); [|lia].
    rewrite Z.add_0_r.
    rewrite -Z.add_assoc.
    rewrite (Z.div_add_l (x `div` k) k (x `mod` k + (k-1))); [|lia].
    assert ((x `mod` k + (k-1)) `div` k = 1) as Hone.
    {
      pose proof (Z_mod_lt x k H0) as [Hpos Hlt].
      assert (1*k <= x `mod` k + (k-1)) as Hlb by lia.
      assert (x `mod` k + (k-1) < 2*k) as Hub by lia.
      assert (0 < k) as Hk by lia.
      pose (Zdiv_lt_upper_bound _ _ _ Hk Hub).
      pose (Zdiv_le_lower_bound _ _ _ Hk Hlb).
      lia.
    }
    by rewrite Hone.
Qed.

Lemma roundUpDiv_gt_0 (x k : Z) :
  k > 0 -> roundUpDiv x k > 0 -> x > 0.
Proof.
  intros.
  unfold roundUpDiv in *.
Admitted.

Lemma roundUpDiv_mul_le (x k z: Z) :
  x >= 0 -> k > 0 -> z < roundUpDiv x k -> k * z <= x.
Proof.
  intros.
  unfold roundUpDiv in *.
  assert (∃ c, c > 0 ∧ z = (x + (k-1)) `div` k - c) as [c [Hc Hz]].
  {
    exists ((x + (k-1)) `div` k - z).
    word.
  }
  rewrite Hz.
  rewrite Z.mul_add_distr_l.
Admitted.

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

Module impl_s.
  Record t :=
    mk { (* addresses consumed by this inode *)
        hdr: Block;
        numInd: nat;
        dirAddrs: list u64;
        indAddrs: list u64;
        indBlkAddrsList: list (list u64);
      }.
  Global Instance _eta: Settable _ := settable! mk <hdr; numInd; dirAddrs; indAddrs; indBlkAddrsList>.
  Global Instance _witness: Inhabited t := populate!.
End impl_s.

Hint Unfold inode.wf MaxBlocks indirectNumBlocks maxDirect maxIndirect: word.

Section goose.
Context `{!heapGS Σ}.
Context `{!stagedG Σ}.
Context `{!allocG Σ}.

Context (inodeN allocN: namespace).

Implicit Types (σ: inode.t).
Implicit Types (l:loc) (γ:gname) (P: inode.t → iProp Σ).

Definition is_indirect (a: u64) (indBlkAddrs: list u64) (indBlock : Block)
           (specBlocks : list Block) : iProp Σ :=
  "diskAddr" ∷ uint.Z a d↦ indBlock ∗
  "%HindBlockLen" ∷ ⌜length (indBlkAddrs ++ replicate (Z.to_nat ((indirectNumBlocks - (length indBlkAddrs)) `mod` indirectNumBlocks)) (W64 0)) = Z.to_nat indirectNumBlocks
  ∧ length indBlkAddrs <= 512
  ∧ length indBlkAddrs > 0⌝ ∗
  "%Hencoded" ∷ ⌜block_encodes indBlock (EncUInt64 <$> (indBlkAddrs) ++ replicate (Z.to_nat ((indirectNumBlocks - (length indBlkAddrs)) `mod` indirectNumBlocks)) (W64 0))⌝ ∗
  "%Hlen" ∷ ⌜length(indBlkAddrs) = length(specBlocks)⌝ ∗
  "Hdata" ∷ ([∗ list] a;b ∈ indBlkAddrs;specBlocks, uint.Z a d↦ b)
.

Definition ind_blocks_at_index σ index : list Block :=
  let begin := Z.to_nat (maxDirect + (index * indirectNumBlocks)) in
  List.subslice begin (begin + (Z.to_nat indirectNumBlocks)) σ.(inode.blocks).

Definition is_inode_durable_data σ (ds: impl_s.t) : iProp Σ :=
    (* direct addresses correspond to data blocks in inode spec *)
    "HdataDirect" ∷ (let len := Nat.min (Z.to_nat maxDirect) (length σ.(inode.blocks)) in
                     [∗ list] a;b ∈ take len ds.(impl_s.dirAddrs);take len σ.(inode.blocks), uint.Z a d↦ b) ∗
    (* indirect addresses correspond to a block's worth of data blocks in inode spec *)
    "HdataIndirect" ∷ ∃ indBlocks,
    ⌜length indBlocks = length (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs))⌝ ∗
    ([∗ list] index↦a;indBlock ∈ take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs);indBlocks,
    ∃ indBlkAddrs, ⌜ds.(impl_s.indBlkAddrsList) !! index = Some indBlkAddrs⌝ ∗
                    is_indirect a indBlkAddrs indBlock (ind_blocks_at_index σ index)).

Definition is_inode_durable_hdr σ (addr: u64) (ds: impl_s.t) : iProp Σ :=
  "%Hencoded" ∷ ⌜block_encodes ds.(impl_s.hdr) ([EncUInt64 (length σ.(inode.blocks))]
                                                 ++ (EncUInt64 <$> ds.(impl_s.dirAddrs))
                                                 ++ (EncUInt64 <$> ds.(impl_s.indAddrs))
                                                 ++ [EncUInt64 ds.(impl_s.numInd)])⌝ ∗
  "Hhdr" ∷ (uint.Z addr d↦ ds.(impl_s.hdr)).

Definition is_inode_durable_facts σ (addr: u64) (ds: impl_s.t)
  : iProp Σ  :=
    "%Hwf" ∷ ⌜inode.wf σ⌝ ∗
    "%Haddrs_set" ∷ ⌜list_to_set (take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs)
                                       ++ (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs))
                                       ++ concat ds.(impl_s.indBlkAddrsList))
    = σ.(inode.addrs)⌝ ∗
    "%HdirAddrs" ∷ ⌜ ∃ daddrs, ds.(impl_s.dirAddrs) = daddrs ++ (replicate (Z.to_nat (maxDirect) - (min (length σ.(inode.blocks)) (Z.to_nat maxDirect))) (W64 0))⌝ ∗
    "%HindAddrs" ∷ ⌜ ∃ indaddrs, ds.(impl_s.indAddrs) = indaddrs ++ (replicate (Z.to_nat (maxIndirect) - ds.(impl_s.numInd)) (W64 0))⌝ ∗
    "%Hlen" ∷ (⌜
      maxDirect = length(ds.(impl_s.dirAddrs)) ∧
      maxIndirect = length(ds.(impl_s.indAddrs)) ∧
      (Z.of_nat (length σ.(inode.blocks))) <= MaxBlocks⌝) ∗
    "%HnumInd" ∷ ⌜Z.of_nat ds.(impl_s.numInd)
                                 = roundUpDiv (Z.of_nat (((Z.to_nat maxDirect) `max` length σ.(inode.blocks))%nat) - maxDirect) indirectNumBlocks⌝ ∗

    "%HindBlkAddrsListLen" ∷ ⌜length(ds.(impl_s.indBlkAddrsList)) = ds.(impl_s.numInd)⌝.

Definition is_inode_durable_with σ addr ds : iProp Σ  :=
    "Hfacts" ∷ is_inode_durable_facts σ addr ds ∗
    "Hhdr" ∷ is_inode_durable_hdr σ addr ds ∗
    "Hdata" ∷ is_inode_durable_data σ ds
.

Definition is_inode_volatile_with l σ addr direct_s indirect_s ds : iProp Σ :=
    "addr" ∷ l ↦[Inode :: "addr"] #addr ∗
    "size" ∷ l ↦[Inode :: "size"] #(length σ.(inode.blocks)) ∗
    "direct" ∷ l ↦[Inode :: "direct"] (slice_val direct_s) ∗
    "indirect" ∷ l ↦[Inode :: "indirect"] (slice_val indirect_s) ∗
    "Hdirect" ∷ own_slice direct_s uint64T 1 (take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs)) ∗
    "Hindirect" ∷ own_slice indirect_s uint64T 1 (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs))
.

Definition inode_linv_with (l:loc) σ addr direct_s indirect_s ds : iProp Σ :=
    "Hdurable" ∷ is_inode_durable_with σ addr ds ∗
    "Hvolatile" ∷ is_inode_volatile_with l σ addr direct_s indirect_s ds.

Definition inode_linv (l:loc) σ addr : iProp Σ :=
  ∃ (direct_s indirect_s: Slice.t) (ds: impl_s.t),
    inode_linv_with l σ addr direct_s indirect_s ds.

Definition inode_cinv σ addr: iProp Σ :=
  ∃ ds, is_inode_durable_with σ addr ds.

Definition inode_state l (d_ref: loc) (lref: loc) : iProp Σ :=
  "#d" ∷ readonly (l ↦[Inode :: "d"] #d_ref) ∗
  "#m" ∷ readonly (l ↦[Inode :: "m"] #lref).

Definition is_inode l k P addr : iProp Σ :=
  ∃ (d lref: loc),
    "Hro_state" ∷ inode_state l d lref ∗
    "#Hlock" ∷ is_crash_lock inodeN k #lref (∃ σ, "Hlockinv" ∷ inode_linv l σ addr ∗ "HP" ∷ P σ) True.

Definition pre_inode l P σ addr: iProp Σ :=
  ∃ (d lref: loc),
    "Hro_state" ∷ inode_state l d lref ∗
    "Hfree_lock" ∷ is_free_lock lref ∗
    "Hlockinv" ∷ inode_linv l σ addr.

Global Instance is_inode_Persistent l k P addr:
  Persistent (is_inode l k P addr).
Proof. apply _. Qed.

Global Instance is_inode_crash l σ addr:
  IntoCrash (inode_linv l σ addr) (λ _, ∃ ds, is_inode_durable_with σ addr ds)%I.
Proof.
  hnf. iIntros "Hinv".
  iNamed "Hinv".
  iNamed "Hdurable".
  iExists ds.
  iFrame "∗%".
  auto.
Qed.

Lemma indirect_block_middle_full σ index :
  index < roundUpDiv (length σ.(inode.blocks) - maxDirect) indirectNumBlocks ->
  length (ind_blocks_at_index σ index) = Z.to_nat indirectNumBlocks.
Proof.
Admitted.

Lemma indBlkAddrsList_blocks_middle_full σ (i:nat) indAddrs indBlkAddrsList indBlocks:
  ⌜length indBlocks >= i⌝ -∗
  ⌜indirectNumBlocks * i <= length σ.(inode.blocks)⌝ -∗
  ([∗ list] index↦a;indBlock ∈ take i indAddrs;take i indBlocks,
  ∃ indBlkAddrs,
    ⌜indBlkAddrsList !! index = Some indBlkAddrs⌝
    ∗ is_indirect a indBlkAddrs indBlock (ind_blocks_at_index σ index)) -∗
  ⌜(length (concat (take i indBlkAddrsList)) `mod` indirectNumBlocks) = 0⌝.
Admitted.

Theorem init_inode addr :
  uint.Z addr d↦ block0 -∗ inode_cinv (inode.mk ∅ []) addr.
Proof.
  iIntros "Hhdr".
  unfold inode_cinv.
  iExists (impl_s.mk block0 0%nat (replicate (Z.to_nat maxDirect) (W64 0)) (replicate (Z.to_nat maxIndirect) (W64 0)) []).
  unfold is_inode_durable_with.
  repeat iSplit; auto.
  + iExists []; auto.
  + iExists []; auto.
  + iSplitL "Hhdr".
    -- unfold is_inode_durable_hdr. repeat iSplit; auto.
    -- unfold is_inode_durable_data. repeat iSplit; auto.
       iExists []. auto.
Qed.

Theorem wp_Open k {d:loc} {addr σ P} :
  {{{ inode_cinv σ addr ∗ P σ }}}
    indirect_inode.Open #d #addr
    {{{ l, RET #l; is_inode l k P addr}}}.
Proof.
  iIntros (Φ) "(Hinode&HP) HΦ"; unfold inode_cinv;
    iNamed "Hinode"; iNamed "Hdata"; iNamed "Hfacts"; iNamed "Hhdr".
  iDestruct (big_sepL2_length with "HdataDirect") as %Hblocklen.
  destruct Hlen as [HdirLen [HindirLen HszMax]].

  wp_rec. wp_pures.
  wp_apply (wp_Read with "Hhdr").
  iIntros (s) "(Hhdr&Hs)".
  wp_pures.
  iDestruct (slice.own_slice_to_small with "Hs") as "Hs".
  wp_apply (wp_new_dec with "Hs"); first by eauto.
  iIntros (dec) "Hdec".

  wp_apply (wp_Dec__GetInt with "Hdec"); iIntros "Hdec".
  wp_pures.
  wp_apply (wp_Dec__GetInts with "Hdec"); first by len.
  iIntros (diraddr_s) "[Hdec Hdiraddrs]".
  wp_pures.

  wp_apply (wp_Dec__GetInts with "Hdec"); first by len.
  iIntros (indaddr_s) "[Hdec Hindaddrs]".
  wp_pures.

  wp_apply (wp_Dec__GetInt with "Hdec"); iIntros "Hdec".
  wp_pures.

  wp_rec. wp_pures.
  iDestruct "Hdiraddrs" as "[[HdirPtsto %Hdirs_len'] Hdirs_cap]".
  iDestruct "Hindaddrs" as "[[HindPtsto %Hinds_len'] Hinds_cap]".
  assert (length ds.(impl_s.dirAddrs) = uint.nat diraddr_s.(Slice.sz) ∧
         length ds.(impl_s.indAddrs) = uint.nat indaddr_s.(Slice.sz)) as [Hdirs_len Hinds_len].
  {
    split; [rewrite -Hdirs_len' | rewrite -Hinds_len']; rewrite length_fmap; len.
  }
  iAssert (own_slice diraddr_s uint64T 1 ds.(impl_s.dirAddrs)) with "[HdirPtsto Hdirs_cap]" as "Hdiraddrs".
  {
    unfold own_slice. iFrame.
    iPureIntro; auto.
  }
  iAssert (own_slice indaddr_s uint64T 1 ds.(impl_s.indAddrs)) with "[HindPtsto Hinds_cap]" as "Hindaddrs".
  {
    unfold own_slice. iFrame.
    iPureIntro; auto.
  }

  destruct (bool_decide (uint.Z (length σ.(inode.blocks)) <= maxDirect)) eqn:HnumDir; unfold maxDirect in HnumDir; rewrite HnumDir; wp_pures.
  all: rewrite -wp_fupd; wp_apply wp_new_free_lock.
  all: iIntros (lref) "Hlock".
  {
    apply bool_decide_eq_true in HnumDir.
    replace (uint.Z (W64 (Z.of_nat (length σ.(inode.blocks))))) with (Z.of_nat (length σ.(inode.blocks))) in HnumDir by word.
    assert (Z.of_nat ds.(impl_s.numInd) = 0) as HnumInd0.
    {
      rewrite HnumInd.
      unfold roundUpDiv, MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *; try word.
    }
    wp_apply (wp_SliceTake (length σ.(inode.blocks))).
    {
      assert (uint.Z maxDirect = uint.Z (diraddr_s.(Slice.sz))).
      { unfold maxDirect in *. word. }
      replace (uint.Z (W64 (Z.of_nat (length σ.(inode.blocks))))) with (Z.of_nat (length σ.(inode.blocks))) in H; word.
    }
    wp_apply (wp_SliceTake (ds.(impl_s.numInd))).
    {
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
      iExists (slice_take diraddr_s (length σ.(inode.blocks))), _, ds.
      iFrame.
      iSplit; iFrame.
      - iFrame "∗ %".
        iPureIntro. repeat (split; auto).
      - iSplitL "Hdiraddrs"; unfold own_slice; rewrite /list.untype fmap_take//.
        {
          unfold maxDirect in *.
          change (into_val.to_val <$> ds.(impl_s.dirAddrs)) with (u64val <$> ds.(impl_s.dirAddrs)).
          iPoseProof (own_slice_take_cap _ _ (u64val <$> ds.(impl_s.dirAddrs)) (W64 (Z.of_nat (length σ.(inode.blocks)))) with "Hdiraddrs") as "H".
          { len. }
          replace (uint.nat (W64 (Z.of_nat (length σ.(inode.blocks))))) with (length σ.(inode.blocks)); auto.
          word.
        }
        {
          rewrite HnumInd0.
          assert (ds.(impl_s.numInd) = 0%nat) by word; rewrite H.
          iApply (own_slice_take_cap indaddr_s uint64T (u64val <$> ds.(impl_s.indAddrs)) (0) with "Hindaddrs"); word.
        }
    }
    iAssert (is_crash_lock inodeN k #lref (∃ σ, inode_linv l σ addr ∗ P σ) True) as "#Hcrash_lock".
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
        replace (uint.Z (W64 (Z.of_nat (length σ.(inode.blocks))))) with (Z.of_nat (length σ.(inode.blocks))) in H; word.
    }
    assert (Z.of_nat ds.(impl_s.numInd) = (roundUpDiv ((Z.of_nat (length σ.(inode.blocks))) - maxDirect) indirectNumBlocks))
    as HnumIndGt. {
      rewrite HnumInd Nat.max_r; word.
    }
    assert ((roundUpDiv ((Z.of_nat (length σ.(inode.blocks))) - maxDirect) indirectNumBlocks) < maxIndirect + 1)
      as HmaxCmp. {
      unfold MaxBlocks, roundUpDiv, indirectNumBlocks, maxDirect, indirectNumBlocks, maxIndirect in *.
      apply Zdiv_lt_upper_bound; eauto; lia.
    }

    wp_apply (wp_SliceTake maxDirect).
    {
      assert (maxDirect = uint.Z (diraddr_s.(Slice.sz))).
      {
        unfold maxDirect in Hdirs_len, HdirLen. unfold maxDirect. by word.
      }
      rewrite -H; word.
    }
    wp_apply (wp_SliceTake (ds.(impl_s.numInd))).
    {
      rewrite HnumIndGt.
      unfold roundUpDiv, maxIndirect, maxDirect, indirectNumBlocks in *.
      replace (uint.Z indaddr_s.(Slice.sz)) with 10 by word.
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
      iExists _, _, ds.
      iFrame.
      iSplit; iFrame.
      - iFrame "∗ %".
        iPureIntro. repeat (split; auto).
      - iSplitL "Hdiraddrs"; unfold own_slice; rewrite /list.untype fmap_take//.
        {
          change (to_val <$> ds.(impl_s.dirAddrs)) with (u64val<$> ds.(impl_s.dirAddrs)).
          unfold maxDirect in HdirLen, HszBound.
          rewrite take_ge; last by len.
          iEval (rewrite -(firstn_all (u64val <$> ds.(impl_s.dirAddrs))) length_fmap /maxDirect).
          replace (length ds.(impl_s.dirAddrs)) with 500%nat by word.
          iApply (own_slice_take_cap with "Hdiraddrs").
          rewrite length_fmap; word.
        }
        {
          iPoseProof (own_slice_take_cap indaddr_s uint64T (u64val <$> ds.(impl_s.indAddrs)) (ds.(impl_s.numInd)) with "Hindaddrs")
            as "H".
          {
            unfold roundUpDiv, MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *. len.
          }
          by replace (uint.nat (W64 (Z.of_nat ds.(impl_s.numInd)))) with (ds.(impl_s.numInd)) by word.
        }
    }
    iAssert (is_crash_lock inodeN k #lref (∃ σ, inode_linv l σ addr ∗ P σ) True) as "#Hcrash_lock".
    { admit. }
    iModIntro.
    iApply "HΦ".
    iExists _, _; iFrame "#".
  }
Admitted.

Theorem is_inode_durable_size σ addr ds :
  is_inode_durable_with σ addr ds -∗ ⌜(length ((take (length σ.(inode.blocks)) (ds.(impl_s.dirAddrs))) ++ concat ds.(impl_s.indBlkAddrsList))
                                               = length σ.(inode.blocks))%nat⌝.
Proof.
  iNamed 1.
  iNamed "Hfacts"; iNamed "Hhdr"; iNamed "Hdata".
  destruct Hlen as [HdirAddrsLen [HindAddrsMax HnumIndBound]].
  iDestruct (big_sepL2_length with "HdataDirect") as "%H1".
  iDestruct "HdataIndirect" as (indBlocks) "[HindBlocksLen HdataIndirect]".
  iDestruct (big_sepL2_length with "HdataIndirect") as "%H2".
  destruct (bool_decide (maxDirect < length (σ.(inode.blocks)))) eqn:Hdir;
    rewrite length_app;
    unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
  + apply bool_decide_eq_true in Hdir.
    repeat rewrite length_take in H1.
    admit.
  + apply bool_decide_eq_false in Hdir.
    repeat rewrite length_take in H1.
Admitted.

Definition slice_subslice A n m s := slice_skip (slice_take s m) A n.

Definition is_alloced_blocks_slice σ s (direct_s indirect_s : Slice.t)
           numInd (dirAddrs indAddrs : list u64) (indBlkAddrsList: list (list u64)) : iProp Σ :=
      "direct" ∷ own_slice direct_s uint64T 1 (take (length σ.(inode.blocks)) dirAddrs) ∗
      "indirect" ∷ own_slice indirect_s uint64T 1 (take (numInd) indAddrs) ∗
      "indblocks" ∷ own_slice (slice_subslice uint64T
                               ((uint.nat direct_s.(Slice.sz)) + (uint.nat indirect_s.(Slice.sz)))%nat
                               s.(Slice.sz) s)
      uint64T 1 (concat indBlkAddrsList ++
                        replicate (lastBlockFiller indirectNumBlocks indBlkAddrsList) (W64 0)).

Theorem wp_indNum {off: u64} :
  {{{
       ⌜uint.Z off >= maxDirect⌝
  }}}
    indNum #off
  {{{(v: u64), RET #v;
      ⌜uint.Z v = (uint.Z off - maxDirect) `div` indirectNumBlocks⌝
  }}}.
Proof.
  iIntros (ϕ) "%H Hϕ".
  wp_rec. wp_pures.
  iApply "Hϕ".
  iPureIntro.
  unfold indirectNumBlocks. unfold maxDirect in *.
  word_cleanup.
  word.
Qed.

Theorem wp_indOff {off: u64} :
  {{{
       ⌜uint.Z off >= maxDirect⌝
  }}}
    indOff #off
  {{{(v: u64), RET #v;
     ⌜uint.Z v = (uint.Z off - maxDirect) `mod` indirectNumBlocks⌝
  }}}.
Proof.
  iIntros (ϕ) "%H Hϕ".
  wp_rec. wp_pures.
  iApply "Hϕ".
  iPureIntro.
  unfold indirectNumBlocks. unfold maxDirect in *.
  word_cleanup.
  word.
Qed.

Theorem wp_readIndirect {l σ}
        ds indirect_s (indBlk: Block) (indBlkAddrs : list u64) (index: nat) (d : loc) (a : u64):
  {{{
    "%Hwf" ∷ ⌜inode.wf σ⌝ ∗
    "%Hsize" ∷ ⌜length σ.(inode.blocks) <= MaxBlocks⌝ ∗
    "%HindexMax" ∷ ⌜(index < ds.(impl_s.numInd))⌝ ∗
    "%Hlen" ∷ ⌜Z.of_nat (length(ds.(impl_s.indAddrs))) = uint.Z maxIndirect
    ∧ ds.(impl_s.numInd) <= maxIndirect⌝ ∗
    "#d" ∷ readonly (l ↦[Inode :: "d"] #d) ∗
    "%Haddr" ∷ ⌜Some a = (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs)) !! index⌝ ∗
    "indirect" ∷ l ↦[Inode :: "indirect"] (slice_val indirect_s) ∗
    "HindBlkAddrs" ∷ is_indirect a indBlkAddrs indBlk (ind_blocks_at_index σ index)
  }}}
     readIndirect #d #a
  {{{ indBlkAddrs_s, RET slice_val indBlkAddrs_s;
    "HindBlkIndirect" ∷ is_indirect a indBlkAddrs indBlk (ind_blocks_at_index σ index) ∗
    "HindBlkAddrs" ∷ own_slice indBlkAddrs_s uint64T 1
                      (indBlkAddrs ++ replicate (Z.to_nat ((indirectNumBlocks - (length indBlkAddrs)) `mod` indirectNumBlocks)) (W64 0)) ∗
    "indirect" ∷ l ↦[Inode :: "indirect"] (slice_val indirect_s)
  }}}.
Proof.
  iIntros (ϕ) "H Hϕ". iNamed "H". iNamed "HindBlkAddrs".
  destruct Hlen as [HindAddrsMax HnumIndBound].
  wp_rec. wp_pures.

  wp_apply ((wp_Read a 1 indBlk) with "[diskAddr]"); auto.
  iIntros (s) "[diskAddr Hs]".
  wp_pures.
  unfold is_block_full.
  iDestruct (slice.own_slice_to_small with "Hs") as "Hs".

  wp_apply (wp_new_dec with "Hs"); first by eauto.
  iIntros (dec) "Hdec".
  wp_pures.

  wp_apply (wp_Dec__GetInts_complete with "Hdec").
  {
    (* rewrite length_app length_replicate /indirectNumBlocks. *)
    unfold ind_blocks_at_index, MaxBlocks, maxIndirect, maxDirect, indirectNumBlocks in *.
    destruct HindBlockLen as [HindBlockLen [HindBlkAddrsLenUB HLB]].
    rewrite Zmod_small; try word.
    by replace (Z.to_nat (512 - Z.of_nat (length indBlkAddrs)))
      with (Z.to_nat ((512 - Z.of_nat (length indBlkAddrs)) `mod` 512)) by word.
  }
  iIntros (indBlkAddrsPadding_s) "[_ HindBlks]".

  iApply "Hϕ"; iFrame; auto.
Qed.

Theorem wp_Inode__UsedBlocks {l γ P addr σ} :
  {{{ pre_inode l P σ addr }}}
    Inode__UsedBlocks #l
    {{{ (s direct_s indirect_s :Slice.t) (ds: impl_s.t),
        RET (slice_val s);
        ⌜list_to_set ((take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs))
                   ++ (take (ds.(impl_s.numInd)) (ds.(impl_s.indAddrs)))
                   ++ concat ds.(impl_s.indBlkAddrsList))
        = σ.(inode.addrs)⌝ ∗
      is_alloced_blocks_slice σ s direct_s indirect_s ds.(impl_s.numInd) ds.(impl_s.dirAddrs) ds.(impl_s.indAddrs) ds.(impl_s.indBlkAddrsList) ∗
      (is_alloced_blocks_slice σ s direct_s indirect_s ds.(impl_s.numInd) ds.(impl_s.dirAddrs) ds.(impl_s.indAddrs) ds.(impl_s.indBlkAddrsList) -∗
                               pre_inode l P σ addr) }}}.
Proof using allocG0 allocN heapG0 inodeN stagedG0 Σ.
  iIntros (Φ) "Hinode HΦ"; iNamed "Hinode".
  wp_rec. wp_pures.
  iNamed "Hlockinv".
  iNamed "Hvolatile"; iNamed "Hdurable"; iNamed "Hfacts"; iNamed "Hhdr"; iNamed "Hdata".
  destruct Hlen as [HdirLen [HindirLen HszMax]].
  wp_apply wp_ref_of_zero; auto.
  iIntros (l0) "Hl0".
  wp_pures.
  wp_apply (wp_NewSlice _ _ (uint64T)).
  iIntros (s) "Hs".
  wp_store.
  wp_loadField; wp_pures.
  wp_loadField; wp_pures.

  iDestruct (own_slice_sz with "Hdirect") as %HDirlen.
  iDestruct (own_slice_sz with "Hindirect") as %HIndlen.
  iDestruct (own_slice_split with "Hdirect") as "[Hdirect_small Hdirect]".
  iDestruct (own_slice_split with "Hindirect") as "[Hindirect_small Hindirect]".

  wp_apply (wp_forSlicePrefix
              (fun done todo =>
               ∃ s usedBlksList,
                 "%" ∷ ⌜ done ++ todo = (take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs)) ⌝ ∗
                 "%" ∷ ⌜ done = usedBlksList ⌝ ∗
                 "Hl0" ∷ (l0 ↦[slice.T uint64T] (slice_val s)) ∗
                 "HusedSlice" ∷ own_slice s uint64T 1 usedBlksList
      )%I
  with "[] [Hl0 Hdirect_small Hs]").
  { iIntros (i a done todo _).
    iModIntro.
    iIntros (lϕ) "Hinv HΦ"; iNamed "Hinv".
    wp_pures.
    wp_load.
    iDestruct (own_slice_sz with "HusedSlice") as %HusedSlicelen.
    wp_apply (wp_SliceAppend (V:=u64) with "[$HusedSlice]").

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
                 "%" ∷ ⌜ done ++ todo = (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs)) ⌝ ∗
                 "%" ∷ ⌜ done = usedIndBlks ⌝ ∗
                 "Hl0" ∷ (l0 ↦[slice.T uint64T] (slice_val s)) ∗
                 "indirect" ∷ (l ↦[Inode :: "indirect"] (slice_val indirect_s)) ∗
                 "HusedSlice" ∷ own_slice s uint64T 1 (usedBlksList ++ usedIndBlks)
      )%I
  with "[] [Hl0 Hindirect_small indirect HusedSlice]").
  { iIntros (i a done todo _).
    iModIntro.
    iIntros (lϕ) "Hinv HΦ"; iNamed "Hinv".
    wp_pures.
    wp_load.

    iDestruct (own_slice_sz with "HusedSlice") as %HusedSlicelen.
    wp_apply (wp_SliceAppend (V:=u64) with "[$HusedSlice]").

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

  (*facts for readIndirect*)
  assert (ds.(impl_s.numInd) <= maxIndirect) as HnumIndMax.
  {
    unfold roundUpDiv, MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *. lia.
  }
  assert ((uint.nat direct_s.(Slice.sz) + uint.nat indirect_s.(Slice.sz)) < Z.to_nat MaxBlocks)%nat as HslicesLen.
  {
    rewrite -HDirlen -HIndlen.
    repeat rewrite length_take.
    word.
  }

  iNamed "Hro_state".
  iDestruct "HdataIndirect" as (indBlocks) "[%HindBlocksLen HdataIndirect]".
  wp_apply (wp_forSlicePrefix
              (fun done todo =>
               ∃ s,
                 "%" ∷ ⌜ done ++ todo = (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs)) ⌝ ∗
                 "Hl0" ∷ (l0 ↦[slice.T uint64T] (slice_val s)) ∗
                 "indirect" ∷ (l ↦[Inode :: "indirect"] (slice_val indirect_s)) ∗
                 "HusedSlice" ∷
                  own_slice s uint64T 1
                           (usedBlksList
                              ++ usedIndBlks
                              ++ concat (take (length done) ds.(impl_s.indBlkAddrsList))
                              ++ (replicate (lastBlockFiller indirectNumBlocks
                                                            (take (length done) ds.(impl_s.indBlkAddrsList)))
                                                            (W64 0))) ∗
                 "HindBlks" ∷ [∗ list] i↦a;indBlk ∈ done ++ todo;indBlocks, ∃ indBlkAddrs,
                                                ⌜ ds.(impl_s.indBlkAddrsList) !! i = Some indBlkAddrs ⌝ ∗
                                                is_indirect a indBlkAddrs indBlk (ind_blocks_at_index σ i)
      )%I
  with "[] [Hindirect_small Hl0 HusedSlice indirect HdataIndirect]").
  { iIntros (i a done todo _).
    iModIntro.
    iIntros (lϕ) "Hinv HΦ"; iNamed "Hinv".
    wp_pures.
    wp_loadField.
    replace (indBlocks) with ((take (length done) indBlocks) ++ (drop (length done) indBlocks))
      by (rewrite take_drop; auto).
    iApply (big_sepL2_app_inv _ done (a :: todo) (take (length done) indBlocks) (drop (length done) indBlocks)) in "HindBlks"; auto.
    {
      rewrite length_take HindBlocksLen -H3. len.
    }
    iDestruct "HindBlks" as "[HindBlksDone HindBlksTodo]".
    assert (∃ indblk, indblk :: (drop (length done + 1)) indBlocks = (drop (length done)) indBlocks)
      as [indblk Hindblk].
    {
      assert (∃ indblk, indBlocks !! length done = Some indblk) as [indblk Htmp].
      + apply lookup_lt_is_Some. rewrite HindBlocksLen -H3. len.
      + exists indblk.
        replace (length done + 1)%nat with (S (length done))%nat by word.
        rewrite -drop_S; auto.
    }
    rewrite -Hindblk.
    iDestruct (big_sepL2_cons with "HindBlksTodo") as "[Ha HindBlksTodo]".
    iEval (rewrite -plus_n_O) in "Ha".
    iDestruct "Ha" as (indBlkAddrs) "[%HindBlkAddrsLookup Ha]".
    wp_apply (wp_readIndirect ds indirect_s indblk indBlkAddrs (length done) d a with "[Ha indirect]").
    {
      iFrame.
      repeat (iSplitR; [iPureIntro; eauto|]).
      { assert (length (done ++ a :: todo) = length (take ds.(impl_s.numInd) ds.(impl_s.indAddrs))) as tmp by (rewrite H3; auto).
        rewrite length_app length_take length_cons min_l in tmp; lia.
      }
      iSplitR; iFrame; eauto.
      + by rewrite -H3 list_lookup_middle.
    }
    iIntros (indBlkAddrs_s) "H".
    iNamed "H".
    wp_load.
    wp_apply (wp_SliceAppendSlice (V:=u64) with "[HusedSlice HindBlkAddrs]"); iFrame.
    iIntros (s') "Hs'".
    wp_store.
    iApply "HΦ".

    iExists s'.
    iNamed "HindBlkIndirect".
    iFrame.
    iSplitR; [iPureIntro; rewrite -app_assoc; simpl; eauto|].
    rewrite length_app.
    iAssert (∀ i, ⌜(i <= length done)%nat⌝ -∗
                   ⌜(length (concat (take i ds.(impl_s.indBlkAddrsList))) `mod` indirectNumBlocks) = 0⌝)%I
      with "[HindBlksDone]" as "%Hfull".
    {
      iIntros.
      destruct (bool_decide (ds.(impl_s.numInd) > 0)) eqn:Hloop0.
      { apply bool_decide_eq_true in Hloop0.
        assert (length done < length indBlocks) as HdoneLen by (rewrite HindBlocksLen -H3; len).
        iApply (indBlkAddrsList_blocks_middle_full σ i0 ds.(impl_s.indAddrs) ds.(impl_s.indBlkAddrsList) indBlocks);
          [iPureIntro; lia | iPureIntro |]; auto.
        {
          apply (Z.le_trans _ (length σ.(inode.blocks) - maxDirect) _); try word.
          assert (((Z.to_nat maxDirect `max` length σ.(inode.blocks))%nat - maxDirect) > 0)
              by (apply (roundUpDiv_gt_0 ((Z.to_nat maxDirect `max` length σ.(inode.blocks))%nat - maxDirect) indirectNumBlocks); word).
          apply (roundUpDiv_mul_le (length σ.(inode.blocks) - maxDirect) indirectNumBlocks i0); try word.
          rewrite max_r in HnumInd.
          - rewrite -HnumInd.
            rewrite HindBlocksLen length_take in HdoneLen.
            rewrite min_l in HdoneLen; word.
          - destruct (bool_decide (Z.to_nat maxDirect > length σ.(inode.blocks))) eqn:Hgt; word.
        }
        rewrite -(take_drop i0 (take (length done) indBlocks)).
        rewrite -(take_drop i0 done).
        iApply big_sepL2_app_inv in "HindBlksDone"; [len|].
        iDestruct "HindBlksDone" as "[Hi0 _]".
        len.
        rewrite take_take.
        rewrite min_l; [|word].
        replace (take i0 ds.(impl_s.indAddrs)) with (take i0 done); auto.
        replace (take (i0) ds.(impl_s.indAddrs))
            with (take (i0) (take ds.(impl_s.numInd) ds.(impl_s.indAddrs))).
          - rewrite -H3. rewrite take_app_le; auto.
          - rewrite take_take min_l; auto.
            rewrite HindBlocksLen length_take in HdoneLen.
            len.
      }
      {
        apply bool_decide_eq_false in Hloop0.
        assert (ds.(impl_s.numInd) = 0%nat) as His0 by word.
        rewrite His0 in HindBlkAddrsListLen.
        replace (ds.(impl_s.indBlkAddrsList)) with (@nil (list u64)).
        + rewrite take_nil. simpl. auto.
        + by apply nil_length_inv in HindBlkAddrsListLen.
      }
    }
    iSplitL "Hs'".
    {
      assert ((take (length done + length [a]) ds.(impl_s.indBlkAddrsList))
        = (take (length done) ds.(impl_s.indBlkAddrsList)) ++ [indBlkAddrs]) as Ha.
      { simpl.
        replace (take (length done+1) ds.(impl_s.indBlkAddrsList))
          with ((take (length done) ds.(impl_s.indBlkAddrsList)) ++ [indBlkAddrs]).
        2: {
          replace (length done + 1)%nat with (S (length done)%nat) by word.
          rewrite -take_S_r; auto.
        }
        auto.
      }
      rewrite Ha.
      rewrite concat_app.
      assert (concat [indBlkAddrs] = indBlkAddrs) as HconcatSingleton by (simpl; rewrite app_nil_r; auto).
      replace ((lastBlockFiller indirectNumBlocks (take (length done) ds.(impl_s.indBlkAddrsList)))) with (0%nat).
      2: {
        rewrite /lastBlockFiller Hfull; simpl; auto.
      }
      repeat rewrite app_assoc.
      rewrite replicate_0 app_nil_r.
      rewrite app_nil_r.
      unfold lastBlockFiller.
      rewrite concat_app HconcatSingleton.
      len.
      replace (Z.of_nat (length (concat (take (length done) ds.(impl_s.indBlkAddrsList))) + length indBlkAddrs) `mod` indirectNumBlocks)
        with ((Z.of_nat (length (concat (take (length done) ds.(impl_s.indBlkAddrsList)))) + (Z.of_nat (length indBlkAddrs))) `mod` indirectNumBlocks) by word.
      rewrite Z.add_mod; [|simpl; auto].
      rewrite Hfull; auto.
      rewrite Z.add_0_l.
      repeat rewrite Zminus_mod_idemp_r.
      rewrite Z.mod_small; try word.
      auto.
    }
    rewrite -app_assoc.
    iApply (big_sepL2_app with "[HindBlksDone]"); [by simpl|].
    simpl.

    iSplitL "diskAddr Hdata"; simpl; auto.
    {
      iExists indBlkAddrs.
      rewrite -plus_n_O.
      iFrame.
      repeat (iSplitR; iPureIntro; auto).
    }
  }
  {
    rewrite app_nil_l.
    iFrame.
    iExists s1.
    iFrame.
    iSplitR; auto.
    simpl; rewrite app_nil_r; auto.
  }
  iIntros "[Hindirect_small H]".
  iNamed "H".
  iDestruct (own_slice_sz with "HusedSlice") as %Hs2len.

  wp_pures.
  wp_load.
  iApply ("HΦ" $! s2 direct_s indirect_s ds); eauto.
  iSplitR; [iPureIntro; eauto|].
  iFrame.
  iSplitL "HusedSlice".
  + unfold slice_subslice.
    iDestruct "HusedSlice" as "[Hsmall Hcap]".
    rewrite app_assoc.
    iApply (slice_small_split s2 (uint.Z (uint.nat direct_s.(Slice.sz) + uint.nat indirect_s.(Slice.sz))) uint64T 1) in "Hsmall".
    {
      rewrite -H0 -H2 -HDirlen -HIndlen.
      repeat rewrite length_app length_take.
      word.
    }
    iDestruct "Hsmall" as "[HsmallTake HsmallSkip]".
    unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
    replace (slice_take s2 s2.(Slice.sz)) with s2 by (destruct s2; simpl; auto).
    assert ((uint.nat direct_s.(Slice.sz) + uint.nat indirect_s.(Slice.sz)) = length (usedBlksList ++ usedIndBlks))
      as HrewriteMe.
    {
      rewrite length_app -H0 -H2 HDirlen HIndlen.
      word.
    }
    rewrite HrewriteMe.
    replace (uint.nat (uint.Z (length (usedBlksList ++ usedIndBlks)))) with (length (usedBlksList ++ usedIndBlks)) by word.
    rewrite drop_app_length length_take min_l; try word.
    rewrite -HindBlkAddrsListLen.
    rewrite firstn_all.
    iApply own_slice_split.
    iSplitL "HsmallSkip".
    {
      by replace
        (W64 (uint.Z (W64 (Z.of_nat (length (usedBlksList ++ usedIndBlks))))))
        with (W64 (Z.of_nat (uint.nat direct_s.(Slice.sz) + uint.nat indirect_s.(Slice.sz)))) by word.
    }
    iApply (own_slice_cap_skip with "Hcap").
    replace (uint.Z (W64 (Z.of_nat (uint.nat direct_s.(Slice.sz) + uint.nat indirect_s.(Slice.sz)))))
      with (Z.of_nat (uint.nat direct_s.(Slice.sz)) + Z.of_nat (uint.nat indirect_s.(Slice.sz))) by word.
    rewrite HrewriteMe.
    assert (Z.of_nat (length
          (usedBlksList ++
          usedIndBlks ++
          concat (take (length (take ds.(impl_s.numInd) ds.(impl_s.indAddrs))) ds.(impl_s.indBlkAddrsList)) ++
          replicate
            (lastBlockFiller (Z.to_nat 512)
                (take (length (take ds.(impl_s.numInd) ds.(impl_s.indAddrs))) ds.(impl_s.indBlkAddrsList)))
            (W64 0))) = uint.Z s2.(Slice.sz)) as HrewriteMe2 by word.
    rewrite -HrewriteMe2.
    len.
  + iIntros "Halloced".
    iExists d, lref.
    unfold inode_state; iSplitR; [iSplit; auto|].
    iFrame.
    iExists direct_s, indirect_s, ds.
    iFrame.
    iNamed "Halloced".
    iFrame.
    iSplitR; [iPureIntro; repeat split; auto|].
    iSplitR; [iPureIntro; auto|].
    iExists indBlocks.
    iSplitR; [iPureIntro; auto|].
    rewrite app_nil_r.
    iFrame.
Qed.

Theorem wp_Inode__Read {l P k addr} {off: u64} Q :
  {{{ "Hinode" ∷ is_inode l k P addr ∗
      "Hfupd" ∷ (∀ σ σ' mb,
        ⌜σ' = σ ∧ mb = σ.(inode.blocks) !! uint.nat off⌝ ∗
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
  wp_rec. wp_pures.
  wp_loadField.
  wp_apply (crash_lock.wp_Mutex__Lock with "Hlock"); auto.
  iIntros "His_locked".
  wp_pures.

  iAssert ((∃ σ , inode_linv l σ addr ∗ P σ)%I) as (σ) "(-#Hlockinv & -#HP)". { admit. }
  iNamed "Hlockinv".
  iNamed "Hvolatile"; iNamed "Hdurable"; iNamed "Hfacts"; iNamed "Hhdr"; iNamed "Hdata".
  destruct Hlen as [HdirLen [HindirLen HszMax]].
  wp_loadField.
  wp_op.
  wp_if_destruct;
    replace (uint.Z (W64 (Z.of_nat (length σ.(inode.blocks))))) with (Z.of_nat (length σ.(inode.blocks))) in Heqb
    by (unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *; word).
  - iMod ("Hfupd" $! σ σ None with "[$HP]") as "[HP HQ]".
    { iPureIntro.
      rewrite lookup_ge_None_2 //.
      word.
    }
    wp_loadField.
    wp_apply (crash_lock.wp_Mutex__Unlock with "His_locked"); auto.
    wp_pures.
    change slice.nil with (slice_val Slice.nil).
    iApply "HΦ"; iFrame; auto.
  - wp_op.
    assert (uint.Z off < length σ.(inode.blocks)) as Hszoff by lia.
    unfold maxDirect in *.
    wp_if_destruct.

    (* Is direct block *)
    {
      wp_loadField.
      destruct (list_lookup_lt ds.(impl_s.dirAddrs) (uint.nat off)) as [a Hlookup].
      { rewrite /maxDirect. word. }
      iDestruct (own_slice_split with "Hdirect") as "[Hdirect_small Hdirect]".
      wp_apply (wp_SliceGet _ _ _ _ _ (take (length (σ.(inode.blocks))) ds.(impl_s.dirAddrs)) _ a with "[Hdirect_small]").
      { iSplit; auto.
        unfold maxDirect in *.
        iPureIntro.
        rewrite lookup_take_lt; auto.
        word.
      }
      iIntros "Hdirect_small".
      wp_pures.
      iDestruct (big_sepL2_lookup_1_some _ _ _ (uint.nat off) a with "HdataDirect") as "%Hblock_lookup"; eauto.
      { rewrite lookup_take_lt; [auto | word]. }
      destruct Hblock_lookup as [b0 Hlookup2].
      iDestruct (own_slice_split with "[$Hdirect_small $Hdirect]") as "Hdirect".
      iDestruct (big_sepL2_lookup_acc _ _ _ _ a with "HdataDirect") as "[Hb HdataDirect]"; eauto.
      { rewrite lookup_take_lt; [auto | word]. }
      wp_apply (wp_Read with "Hb"); iIntros (s) "[Hb Hs]".
      iSpecialize ("HdataDirect" with "Hb").
      wp_loadField.
      iMod ("Hfupd" $! σ σ with "[$HP]") as "[HP HQ]".
      { iPureIntro; eauto. }
      wp_apply (crash_lock.wp_Mutex__Unlock with "His_locked"); auto.
      wp_pures.
      iApply "HΦ"; iFrame.
      rewrite lookup_take_lt in Hlookup2; [ | word ].
      rewrite Hlookup2.
      iDestruct (own_slice_split with "Hs") as "[Hs _]".
      iFrame.
    }

    (* Is indirect block *)
    {
      wp_apply wp_indNum.
      { iPureIntro. auto. }

      iIntros (index) "%Hindex".

      (* Here are a bunch of facts *)
      assert (uint.Z off >= uint.Z 500) as Hoff500 by word.
      assert (length σ.(inode.blocks) > 500) as Hsz by word.
      assert (ds.(impl_s.numInd) <= maxIndirect) as HnumIndMax.
      {
        unfold roundUpDiv, MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *. lia.
      }
      assert (((uint.Z off - 500) `div` 512) <= ((length σ.(inode.blocks) - 500) `div` 512)) as Hoff. {
        apply Z.div_le; lia.
      }

      assert (uint.Z index < ds.(impl_s.numInd)) as HindexMax. {
        unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
        unfold roundUpDiv, MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *. lia.
      }
      destruct (list_lookup_lt (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs)) (uint.nat index)) as [a Hlookup].
      {
        unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
        rewrite firstn_length Hindex.
        rewrite Nat.min_l; word.
      }

      (* Now we actually step through program the *)
      wp_loadField.
      iDestruct (own_slice_split with "Hindirect") as "[Hindirect_small Hindirect]".
      wp_apply (wp_SliceGet _ _ _ _ 1 (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs)) _ a with "[Hindirect_small]"); iFrame; auto.

      iIntros "Hindirect_small".
      iDestruct (own_slice_split with "[$Hindirect_small $Hindirect]") as "Hindirect".
      iDestruct "HdataIndirect" as (indBlocks) "[%HindBlocksLen HdataIndirect]".
      assert (∃ indBlock, indBlocks !! uint.nat index = Some indBlock) as [indBlk HlookupIndBlock].
      {
        apply lookup_lt_is_Some_2.
        rewrite HindBlocksLen.
        apply (lookup_lt_Some _ _ _ Hlookup).
      }
      iDestruct (big_sepL2_lookup_acc _ (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs)) _ (uint.nat index) a with "HdataIndirect")
        as "[Hb HdataIndirect]"; eauto.

      wp_loadField.
      iDestruct "Hb" as (indBlkAddrs) "[%HaddrLookup HaddrIndirect]".
      wp_apply (wp_readIndirect ds indirect_s indBlk indBlkAddrs (uint.nat index) d a
                  with "[indirect Hindirect HaddrIndirect]").
      {
        iFrame. repeat iSplit; eauto.
        iPureIntro; len.
      }
      iIntros (indBlkAddrs_s) "H". iNamed "H". iNamed "HindBlkIndirect".

      wp_pures.
      wp_apply wp_indOff.
      { iPureIntro; auto. }
      iIntros (offset) "%Hoffset".

      (* More facts about offset *)
      assert ((uint.Z off - 500) `div` 512 * 512 = (512 * (uint.Z off - 500) `div` 512)) as HMulComm by lia.

      assert ((uint.Z off - 500) `div` 512 * 512  <= ((512 * (uint.Z off - 500)) `div` 512)) as HdivMulLe by lia.

      assert (uint.Z index * indirectNumBlocks <= uint.Z off -maxDirect ∧
              uint.Z off -maxDirect < (uint.Z index * indirectNumBlocks) + indirectNumBlocks)
        as [HoffLBound HoffUBound] by word.

      assert (uint.Z offset < length indBlkAddrs) as HoffsetInBounds.
      {
        unfold ind_blocks_at_index in Hlen.
        rewrite Hlen.
        rewrite Hoffset.
        unfold maxDirect, indirectNumBlocks in *.
        assert ((512 * uint.Z index) + uint.Z offset = uint.Z off - 500) by word.
        assert (uint.Z offset = (uint.Z off - 500) - (512 * uint.Z index)) as HoffsetVal by word.
        destruct (dec_ge (length σ.(inode.blocks)) ((500 + uint.nat index * 512) + 512)) as [HlenGe | HlenNotGe].
        (* Subslice fully contained in blocks *)
        {
          rewrite subslice_length.
          - word.
          - word.
        }
        (* Subslice goes to end of blocks *)
        {
          pose (not_ge _ _ HlenNotGe) as HlenUBound.
          rewrite subslice_to_end; [ | word ].
          rewrite skipn_length.
          word.
        }
      }
      destruct (list_lookup_lt (ind_blocks_at_index σ (uint.nat index)) (uint.nat offset)) as [inodeblkaddr HlookupInodeBlk].
      { rewrite -Hlen. word. }
      destruct (list_lookup_lt (indBlkAddrs) (uint.nat offset)) as [blkaddr HlookupBlkInd]; try word.
      assert ((σ.(inode.blocks)) !! (uint.nat off) = Some inodeblkaddr) as HlookupInodeBlk'.
      {
        rewrite /ind_blocks_at_index Hoffset in HlookupInodeBlk.
        unfold subslice in *.
        rewrite lookup_drop in HlookupInodeBlk.
        unfold maxDirect, indirectNumBlocks in *.
        rewrite Hindex in HlookupInodeBlk.
        rewrite -HlookupInodeBlk.
        rewrite -> lookup_take_lt by word.
        f_equal; word. }

      (* Continue through the program *)
      iDestruct (own_slice_split with "HindBlkAddrs") as "[HindBlkAddrs_small HindBlkAddrs]".

      assert ((indBlkAddrs ++ replicate (Z.to_nat ((indirectNumBlocks - length indBlkAddrs) `mod` indirectNumBlocks)) (W64 0)) !! uint.nat offset = Some blkaddr) as HlookupBlkIndPadded. {
        rewrite -(lookup_app_l indBlkAddrs
                               (replicate (Z.to_nat ((indirectNumBlocks - length indBlkAddrs) `mod` indirectNumBlocks)) (W64 0)))
       in HlookupBlkInd; auto; try word.
      }
      wp_apply (wp_SliceGet _ _ _ _ 1 (indBlkAddrs++_) _ blkaddr with "[HindBlkAddrs_small]"); iFrame; auto.

      iIntros "HindBlkAddrs_small".
      iDestruct (own_slice_split with "[$HindBlkAddrs_small $HindBlkAddrs]") as "HindBlkAddrs".
      iDestruct (big_sepL2_lookup_acc _ _ _ _ _ with "Hdata") as "[Hb' Hdata]"; eauto.

      wp_apply (wp_Read with "Hb'"); iIntros (s) "[Hb' Hs]".
      wp_pures.

      iSpecialize ("Hdata" with "Hb'").
      iAssert (∃ indBlkAddrs,
                  ⌜ds.(impl_s.indBlkAddrsList) !! uint.nat index = Some indBlkAddrs⌝ ∗
                  is_indirect a indBlkAddrs indBlk (ind_blocks_at_index σ (uint.nat index)))%I
        with "[diskAddr HindBlkAddrs Hdata]" as "HaddrIndirect".
      {
        iExists indBlkAddrs.
        unfold is_indirect.
        iFrame. iSplit; auto.
      }
      iSpecialize ("HdataIndirect" with "HaddrIndirect").

      wp_loadField.
      iMod ("Hfupd" $! σ σ with "[$HP]") as "[HP HQ]".
      { iPureIntro; eauto. }

      wp_apply (crash_lock.wp_Mutex__Unlock with "His_locked"); auto.
      wp_pures.
      iApply "HΦ"; iFrame.

      rewrite HlookupInodeBlk'.
      iDestruct (own_slice_split with "Hs") as "[Hs_small Hs]"; eauto.
    }
Admitted.

Theorem wp_Inode__Size {l k' P addr} (Q: u64 -> iProp Σ) :
  {{{ "Hinode" ∷ is_inode l k' P addr ∗
      "Hfupd" ∷ (∀ σ σ' sz,
          ⌜σ' = σ ∧ uint.nat sz = inode.size σ⌝ ∗
          ▷ P σ ={⊤}=∗ ▷ P σ' ∗ Q sz)
  }}}
    Inode__Size #l
  {{{ sz, RET #sz; Q sz }}}.
Proof.
  iIntros (Φ) "Hpre HΦ"; iNamed "Hpre".
  iNamed "Hinode"; iNamed "Hro_state".
  wp_rec. wp_pures.
  wp_loadField.
  wp_apply (crash_lock.wp_Mutex__Lock with "Hlock"); auto.
  iIntros "His_locked".
  wp_pures.

  iAssert ((∃ σ, inode_linv l σ addr ∗ P σ)%I) as (σ) "(-#Hlockinv & -#HP)". { admit. }
  iNamed "Hlockinv".
  iNamed "Hvolatile"; iNamed "Hdurable"; iNamed "Hfacts"; iNamed "Hhdr"; iNamed "Hdata".
  wp_loadField.
  wp_pures.
  wp_loadField.
  iMod ("Hfupd" $! σ σ (length σ.(inode.blocks)) with "[$HP]") as "[HP HQ]".
  { iPureIntro.
    split; auto.
    unfold inode.size. word.
  }
  wp_apply (crash_lock.wp_Mutex__Unlock with "His_locked"); auto.
  wp_pures.
  iApply ("HΦ" with "[$]").
Admitted.

Theorem wp_padInts {Stk E} enc (n: u64) (encoded : list encodable) (off: Z):
  {{{
    ⌜ uint.Z 0 ≤ uint.Z n ∧ off >= 8*(uint.Z n) ⌝ ∗
    is_enc enc 4096 encoded off
  }}}
    padInts enc #n @Stk ; E
  {{{ RET #()
;
    is_enc enc 4096 (encoded ++ (EncUInt64 <$> replicate (uint.nat n) (W64 0))) (off-(8*uint.Z n))
  }}}.
Proof.
  iIntros (ϕ) "[%Hi Henc] Hϕ".
  wp_rec. wp_pures.
  wp_rec. wp_pures.
  wp_apply (wp_ref_of_zero _ _ (baseT uint64BT)); first by auto.
  iIntros (i) "Hi".
  wp_pures.

  wp_apply (wp_forUpto (λ i, "%Hiupper_bound" ∷ ⌜uint.Z i <= uint.Z n⌝ ∗
                       "Henc" ∷ is_enc enc 4096 (encoded ++ (EncUInt64 <$> (replicate (uint.nat i) (W64 0))))
                       (off - (8 * uint.Z i)))%I _ _
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
    - word.
    - replace (uint.nat (word.add i0 1)) with (S (uint.nat i0)) by word.
      rewrite replicate_S_end.
      rewrite fmap_app; simpl.
      rewrite app_assoc.
      iExactEq "Henc".
      rewrite /named.
      f_equal; word.
  }
  {
    iSplitL "Henc"; iFrame; auto.
    iSplitR "Henc".
    - word.
    - rewrite replicate_0 fmap_nil app_nil_r.
      iExactEq "Henc".
      rewrite /named.
      f_equal; word.
  }

  iModIntro.
  iIntros "[H Hi]".
  destruct Hi as [Hn Hoff].
  iNamed "H".
  iApply "Hϕ"; iFrame.
Qed.

Theorem wp_Inode__mkHdr {Stk E} l (sz numInd : Z) allocedDirAddrs allocedIndAddrs direct_s indirect_s:
  (length(allocedDirAddrs) <= uint.nat maxDirect ∧
   (Z.of_nat (length(allocedIndAddrs))) = numInd ∧
   sz <= MaxBlocks ∧
   numInd <= maxIndirect)
  ->
  {{{
    "direct" ∷ l ↦[Inode :: "direct"] (slice_val direct_s) ∗
    "indirect" ∷ l ↦[Inode :: "indirect"] (slice_val indirect_s) ∗
    "size" ∷ l ↦[Inode :: "size"] #sz ∗
    "Hdirect" ∷ own_slice direct_s uint64T 1 allocedDirAddrs ∗
    "Hindirect" ∷ own_slice indirect_s uint64T 1 allocedIndAddrs
  }}}
    Inode__mkHdr #l @ Stk; E
  {{{ s hdr, RET (slice_val s);
    is_block s 1 hdr ∗
    "%Hencoded" ∷ ⌜block_encodes hdr ([EncUInt64 sz] ++ (EncUInt64 <$> allocedDirAddrs) ++ (EncUInt64 <$> (replicate (uint.nat (maxDirect - length allocedDirAddrs)) (W64 0)))
                                     ++ (EncUInt64 <$> allocedIndAddrs) ++ (EncUInt64 <$> (replicate (uint.nat (maxIndirect - length allocedIndAddrs)) (W64 0)))
                                     ++ [EncUInt64 numInd])⌝ ∗
    "direct" ∷ l ↦[Inode :: "direct"] (slice_val direct_s) ∗
    "indirect" ∷ l ↦[Inode :: "indirect"] (slice_val indirect_s) ∗
    "size" ∷ l ↦[Inode :: "size"] #sz ∗
    "Hdirect" ∷ own_slice direct_s uint64T 1 allocedDirAddrs ∗
    "Hindirect" ∷ own_slice indirect_s uint64T 1 allocedIndAddrs
  }}}.
Proof.
  iIntros (Hbound Φ) "Hpre HΦ"; iNamed "Hpre".
  wp_rec. wp_pures.
  wp_apply wp_new_enc; iIntros (enc) "Henc".
  wp_pures.
  wp_loadField.
  iDestruct (own_slice_sz with "Hdirect") as %HDirlen.
  iDestruct (own_slice_sz with "Hindirect") as %HIndlen.
  autorewrite with len in HDirlen.
  autorewrite with len in HIndlen.
  destruct Hbound as [HallocedDirAddrsLen [HallocedIndAddrsLen [Hszmax HnumInd]]].

  wp_apply (wp_Enc__PutInt with "Henc").
  { word. }
  iIntros "Henc".
  rewrite app_nil_l.
  wp_loadField.

  iDestruct (own_slice_split with "Hdirect") as "[Hdirect Hcap]".
  wp_apply (wp_Enc__PutInts with "[$Henc $Hdirect]").
  {
    rewrite /maxDirect in HallocedDirAddrsLen.
    word.
  }

  iIntros "[Henc Hdirect]".
  wp_loadField.
  wp_apply wp_slice_len; wp_pures.

  wp_apply (wp_padInts enc (W64 (500 - uint.Z (direct_s.(Slice.sz))))
                       ([EncUInt64 sz] ++ (EncUInt64 <$> allocedDirAddrs))
                       (uint.Z 4096 - 8 - 8 * length allocedDirAddrs) with "[Henc]").
  {
    iSplitR "Henc"; auto.
    iPureIntro.
    split.
    - rewrite HDirlen /maxDirect in HallocedDirAddrsLen. word.
    - rewrite HDirlen. rewrite HDirlen /maxDirect in HallocedDirAddrsLen.
      word.
  }

  iIntros "Henc".
  replace  (uint.Z (W64 4096) - 8 - 8 * Z.of_nat (length allocedDirAddrs) -
              8 * uint.Z (W64 (500 - uint.Z direct_s.(Slice.sz))))
    with 88 by word.

  wp_pures.
  wp_loadField.

  iDestruct (own_slice_split with "Hindirect") as "[Hindirect Hcapind]".
  wp_apply (wp_Enc__PutInts with "[$Henc $Hindirect]").
  { rewrite HallocedIndAddrsLen. word. }
  iIntros "[Henc Hindirect]".
  wp_loadField.
  wp_apply wp_slice_len; wp_pures.

  wp_apply (wp_padInts enc (W64 (10 - uint.Z (indirect_s.(Slice.sz))))
               ((([EncUInt64 sz] ++ (EncUInt64 <$> allocedDirAddrs) ++
               (EncUInt64 <$> replicate (uint.nat (500 - uint.Z direct_s.(Slice.sz))) (W64 0))) ++
               (EncUInt64 <$> allocedIndAddrs)))
               (88 - 8 * length allocedIndAddrs) with "[Henc]").
  {
    iSplitR "Henc"; auto.
    iPureIntro.
    split; rewrite HIndlen /maxIndirect in HallocedIndAddrsLen HnumInd; word.
  }
  iIntros "Henc".
  rewrite /maxIndirect in HnumInd.
  replace (uint.Z (88 - 8 * length allocedIndAddrs) -
           8 * uint.nat (10 - uint.Z indirect_s.(Slice.sz))) with 8 by word.

  wp_pures.
  wp_loadField.
  wp_apply wp_slice_len; wp_pures.
  wp_apply (wp_Enc__PutInt with "Henc").
  { word. }
  iIntros "Henc".
  wp_pures.

  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (s b) "[%Hencoded Hs]".
  wp_pures.
  iApply "HΦ".
  iFrame.
  iPureIntro.
  eapply block_encodes_eq; eauto.
  rewrite -!app_assoc.
  repeat (f_equal; try word).
Qed.
End goose.

(* to preserve backwards-compatibility *)
Ltac Zify.zify_post_hook ::= idtac.
