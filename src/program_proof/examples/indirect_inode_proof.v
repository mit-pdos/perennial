From RecordUpdate Require Import RecordSet.
From Perennial.goose_lang Require Import crash_modality.

From Goose.github_com.mit_pdos.perennial_examples Require Import indirect_inode.

From Perennial.program_proof.examples Require Import alloc_crash_proof.
From Perennial.goose_lang.lib Require Import lock.crash_lock.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import typed_slice.
From Perennial.Helpers Require Import List.
From Perennial.program_proof Require Import marshal_block disk_lib.

Definition maxDirect: Z := 500.
Definition maxIndirect: Z := 10.
Definition indirectNumBlocks: Z := 512.
Definition MaxBlocks: Z := maxDirect + maxIndirect*indirectNumBlocks.
Definition roundUpDiv (x k: Z) := (x + (k-1)) / k.


Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
Remove Hints fractional.into_sep_fractional : typeclass_instances.

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
Context `{!heapG Σ}.
Context `{!crashG Σ}.
Context `{!stagedG Σ}.
Context `{!allocG Σ}.

Context (inodeN allocN: namespace).

Implicit Types (σ: inode.t).
Implicit Types (l:loc) (γ:gname) (P: inode.t → iProp Σ).

Definition is_indirect (a: u64) (indBlkAddrs: list u64) (indBlock : Block)
           (specBlocks : list Block) : iProp Σ :=
  "diskAddr" ∷ int.val a d↦ indBlock ∗
  "%HindBlockLen" ∷ ⌜length (indBlkAddrs ++ replicate (int.nat indirectNumBlocks - (length indBlkAddrs)) (U64 0)) = Z.to_nat indirectNumBlocks
  ∧ length indBlkAddrs <= 512⌝ ∗
  "%Hencoded" ∷ ⌜block_encodes indBlock (EncUInt64 <$> (indBlkAddrs) ++ replicate (int.nat indirectNumBlocks - (length indBlkAddrs)) (U64 0))⌝ ∗
  "%Hlen" ∷ ⌜length(indBlkAddrs) = length(specBlocks)⌝ ∗
  "Hdata" ∷ ([∗ list] a;b ∈ indBlkAddrs;specBlocks, int.val a d↦ b)
.

Definition ind_blocks_at_index σ index : list Block :=
  let begin := int.nat (maxDirect + (index * indirectNumBlocks)) in
  List.subslice begin (begin + (int.nat indirectNumBlocks)) σ.(inode.blocks).

Definition is_inode_durable_data σ (ds: impl_s.t) : iProp Σ :=
    (* direct addresses correspond to data blocks in inode spec *)
    "HdataDirect" ∷ (let len := Nat.min (int.nat maxDirect) (length σ.(inode.blocks)) in
                     [∗ list] a;b ∈ take len ds.(impl_s.dirAddrs);take len σ.(inode.blocks), int.val a d↦ b) ∗
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
  "Hhdr" ∷ (int.val addr d↦ ds.(impl_s.hdr)).

Definition is_inode_durable_facts σ (addr: u64) (ds: impl_s.t)
  : iProp Σ  :=
    "%Hwf" ∷ ⌜inode.wf σ⌝ ∗
    "%Haddrs_set" ∷ ⌜list_to_set (take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs)
                                       ++ (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs))
                                       ++ concat ds.(impl_s.indBlkAddrsList))
    = σ.(inode.addrs)⌝ ∗
    "%HdirAddrs" ∷ ⌜ ∃ daddrs, ds.(impl_s.dirAddrs) = daddrs ++ (replicate (int.nat (maxDirect) - (min (length σ.(inode.blocks)) (int.nat maxDirect))) (U64 0))⌝ ∗
    "%HindAddrs" ∷ ⌜ ∃ indaddrs, ds.(impl_s.indAddrs) = indaddrs ++ (replicate (int.nat (maxIndirect) - ds.(impl_s.numInd)) (U64 0))⌝ ∗
    "%Hlen" ∷ (⌜
      maxDirect = length(ds.(impl_s.dirAddrs)) ∧
      maxIndirect = length(ds.(impl_s.indAddrs)) ∧
      (Z.of_nat (length σ.(inode.blocks))) <= MaxBlocks⌝) ∗
    "%HnumInd" ∷ ⌜Z.of_nat ds.(impl_s.numInd)
                  = roundUpDiv (Z.of_nat (((Z.to_nat maxDirect) `max` length σ.(inode.blocks))%nat) - maxDirect) indirectNumBlocks⌝
.

Definition is_inode_durable_with σ addr ds : iProp Σ  :=
    "Hfacts" ∷ is_inode_durable_facts σ addr ds ∗
    "Hhdr" ∷ is_inode_durable_hdr σ addr ds ∗
    "Hdata" ∷ is_inode_durable_data σ ds
.

Definition is_inode_volatile_with l σ addr direct_s indirect_s ds : iProp Σ :=
    "addr" ∷ l ↦[Inode.S :: "addr"] #addr ∗
    "size" ∷ l ↦[Inode.S :: "size"] #(length σ.(inode.blocks)) ∗
    "direct" ∷ l ↦[Inode.S :: "direct"] (slice_val direct_s) ∗
    "indirect" ∷ l ↦[Inode.S :: "indirect"] (slice_val indirect_s) ∗
    "Hdirect" ∷ is_slice direct_s uint64T 1 (take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs)) ∗
    "Hindirect" ∷ is_slice indirect_s uint64T 1 (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs))
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
  IntoCrash (inode_linv l σ addr) (λ _, ∃ ds, is_inode_durable_with σ addr ds)%I.
Proof.
  hnf. iIntros "Hinv".
  iNamed "Hinv".
  iNamed "Hdurable".
  iExists ds.
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
  unfold inode_cinv.
  iExists (impl_s.mk block0 0%nat (replicate (Z.to_nat maxDirect) (U64 0)) (replicate (Z.to_nat maxIndirect) (U64 0)) []).
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

  wp_call.
  wp_apply (wp_Read with "Hhdr").
  iIntros (s) "(Hhdr&Hs)".
  wp_pures.
  iDestruct (slice.is_slice_to_small with "Hs") as "Hs".
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

  wp_call.
  iDestruct "Hdiraddrs" as "[[HdirPtsto %Hdirs_len'] Hdirs_cap]".
  iDestruct "Hindaddrs" as "[[HindPtsto %Hinds_len'] Hinds_cap]".
  assert (length ds.(impl_s.dirAddrs) = int.nat diraddr_s.(Slice.sz) ∧
         length ds.(impl_s.indAddrs) = int.nat indaddr_s.(Slice.sz)) as [Hdirs_len Hinds_len].
  {
    split; [rewrite -Hdirs_len' | rewrite -Hinds_len']; rewrite fmap_length; len.
  }
  iAssert (is_slice diraddr_s uint64T 1 ds.(impl_s.dirAddrs)) with "[HdirPtsto Hdirs_cap]" as "Hdiraddrs".
  {
    unfold is_slice. iFrame.
    iPureIntro; auto.
  }
  iAssert (is_slice indaddr_s uint64T 1 ds.(impl_s.indAddrs)) with "[HindPtsto Hinds_cap]" as "Hindaddrs".
  {
    unfold is_slice. iFrame.
    iPureIntro; auto.
  }

  destruct (bool_decide (int.val (length σ.(inode.blocks)) <= maxDirect)) eqn:HnumDir; unfold maxDirect in HnumDir; rewrite HnumDir; wp_pures.
  all: rewrite -wp_fupd; wp_apply wp_new_free_lock.
  all: iIntros (lref) "Hlock".
  {
    apply bool_decide_eq_true in HnumDir.
    replace (int.val (U64 (Z.of_nat (length σ.(inode.blocks))))) with (Z.of_nat (length σ.(inode.blocks))) in HnumDir by word.
    assert (Z.of_nat ds.(impl_s.numInd) = 0) as HnumInd0.
    {
      rewrite HnumInd.
      unfold roundUpDiv, MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *; try word.
    }
    wp_apply (wp_SliceTake uint64T (length σ.(inode.blocks))).
    {
      assert (int.val maxDirect = int.val (diraddr_s.(Slice.sz))).
      { unfold maxDirect in *. word. }
      replace (int.val (U64 (Z.of_nat (length σ.(inode.blocks))))) with (Z.of_nat (length σ.(inode.blocks))) in H; word.
    }
    wp_apply (wp_SliceTake uint64T (ds.(impl_s.numInd))).
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
      iExists (slice_take diraddr_s uint64T (length σ.(inode.blocks))), _, ds.
      iFrame.
      iSplit; iFrame.
      - iFrame "∗ %".
        iPureIntro. repeat (split; auto).
      - iSplitL "Hdiraddrs"; unfold is_slice; rewrite /list.untype fmap_take//.
        {
          unfold maxDirect in *.
          change (into_val.to_val <$> ds.(impl_s.dirAddrs)) with (u64val <$> ds.(impl_s.dirAddrs)).
          iPoseProof (is_slice_take_cap _ _ (u64val <$> ds.(impl_s.dirAddrs)) (U64 (Z.of_nat (length σ.(inode.blocks)))) with "Hdiraddrs") as "H".
          { len. }
          replace (int.nat (U64 (Z.of_nat (length σ.(inode.blocks))))) with (length σ.(inode.blocks)); auto.
          word.
        }
        {
          rewrite HnumInd0.
          assert (ds.(impl_s.numInd) = 0%nat) by word; rewrite H.
          iApply (is_slice_take_cap indaddr_s uint64T (u64val <$> ds.(impl_s.indAddrs)) (0) with "Hindaddrs"); word.
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
    assert (Z.of_nat ds.(impl_s.numInd) = (roundUpDiv ((Z.of_nat (length σ.(inode.blocks))) - maxDirect) indirectNumBlocks))
    as HnumIndGt. {
      rewrite HnumInd Max.max_r; word.
    }
    assert ((roundUpDiv ((Z.of_nat (length σ.(inode.blocks))) - maxDirect) indirectNumBlocks) < maxIndirect + 1)
      as HmaxCmp. {
      unfold MaxBlocks, roundUpDiv, indirectNumBlocks, maxDirect, indirectNumBlocks, maxIndirect in *.
      apply Zdiv_lt_upper_bound; eauto; lia.
    }

    wp_apply (wp_SliceTake uint64T maxDirect).
    {
      assert (maxDirect = int.val (diraddr_s.(Slice.sz))).
      {
        unfold maxDirect in Hdirs_len, HdirLen. unfold maxDirect. by word.
      }
      rewrite -H; word.
    }
    wp_apply (wp_SliceTake uint64T (ds.(impl_s.numInd))).
    {
      rewrite HnumIndGt.
      unfold roundUpDiv, maxIndirect, maxDirect, indirectNumBlocks in *.
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
      iExists _, _, ds.
      iFrame.
      iSplit; iFrame.
      - iFrame "∗ %".
        iPureIntro. repeat (split; auto).
      - iSplitL "Hdiraddrs"; unfold is_slice; rewrite /list.untype fmap_take//.
        {
          change (to_val <$> ds.(impl_s.dirAddrs)) with (u64val<$> ds.(impl_s.dirAddrs)).
          unfold maxDirect in HdirLen, HszBound.
          rewrite take_ge; last by len.
          iEval (rewrite -(firstn_all (u64val <$> ds.(impl_s.dirAddrs))) fmap_length /maxDirect).
          replace (length ds.(impl_s.dirAddrs)) with 500%nat by word.
          iApply (is_slice_take_cap with "Hdiraddrs").
          rewrite fmap_length; word.
        }
        {
          iPoseProof (is_slice_take_cap indaddr_s uint64T (u64val <$> ds.(impl_s.indAddrs)) (ds.(impl_s.numInd)) with "Hindaddrs")
            as "H".
          {
            unfold roundUpDiv, MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *. len.
          }
          by replace (int.nat (U64 (Z.of_nat ds.(impl_s.numInd)))) with (ds.(impl_s.numInd)) by word.
        }
    }
    iAssert (is_crash_lock inodeN inodeN k #lref (∃ σ, inode_linv l σ addr ∗ P σ) True) as "#Hcrash_lock".
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
    rewrite app_length;
    unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
  + apply bool_decide_eq_true in Hdir.
    repeat rewrite take_length in H1.
    admit.
  + apply bool_decide_eq_false in Hdir.
    repeat rewrite take_length in H1.
Admitted.

Definition slice_subslice A n m s := slice_skip (slice_take s A m) A n.

Definition is_alloced_blocks_slice σ s (direct_s indirect_s indblks_s : Slice.t)
           numInd (dirAddrs indAddrs : list u64) (indBlkAddrsList: list (list u64)) : iProp Σ :=
      is_slice direct_s uint64T 1 (take (length σ.(inode.blocks)) dirAddrs) ∗
      is_slice indirect_s uint64T 1 (take (numInd) indAddrs) ∗
      is_slice indblks_s uint64T 1 (concat indBlkAddrsList ++ replicate (int.nat (indirectNumBlocks - (length (concat indBlkAddrsList) `mod` indirectNumBlocks))) (U64 0)) ∗
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
        ds indirect_s (indBlk: Block) (indBlkAddrs : list u64) (index: nat) (d : loc) (a : u64):
  {{{
    "%Hwf" ∷ ⌜inode.wf σ⌝ ∗
    "%Hsize" ∷ ⌜length σ.(inode.blocks) <= MaxBlocks⌝ ∗
    "%HindexMax" ∷ ⌜(index < ds.(impl_s.numInd))⌝ ∗
    "%Hlen" ∷ ⌜Z.of_nat (length(ds.(impl_s.indAddrs))) = int.val maxIndirect ∧ ds.(impl_s.numInd) <= maxIndirect⌝ ∗
    "#d" ∷ readonly (l ↦[Inode.S :: "d"] #d) ∗
    "%Haddr" ∷ ⌜Some a = (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs)) !! index⌝ ∗
    "indirect" ∷ l ↦[Inode.S :: "indirect"] (slice_val indirect_s) ∗
    "Hindirect" ∷ is_slice indirect_s uint64T 1 (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs)) ∗
    "HindBlkAddrs" ∷ is_indirect a indBlkAddrs indBlk (ind_blocks_at_index σ index)
  }}}
     readIndirect #d #a
  {{{ indBlkAddrs_s, RET slice_val indBlkAddrs_s;
    "HindBlkIndirect" ∷ is_indirect a indBlkAddrs indBlk (ind_blocks_at_index σ index) ∗
    "HindBlkAddrs" ∷ is_slice indBlkAddrs_s uint64T 1
                      (indBlkAddrs ++ replicate (int.nat indirectNumBlocks - (length indBlkAddrs)) (U64 0)) ∗
    "indirect" ∷ l ↦[Inode.S :: "indirect"] (slice_val indirect_s) ∗
    "Hindirect" ∷ is_slice indirect_s uint64T 1 (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs))
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

  wp_apply (wp_new_dec with "Hs"); first by eauto.
  iIntros (dec) "Hdec".
  wp_pures.

  wp_apply (wp_Dec__GetInts_complete with "Hdec").
  {
    (* rewrite app_length replicate_length /indirectNumBlocks. *)
    unfold ind_blocks_at_index, MaxBlocks, maxIndirect, maxDirect, indirectNumBlocks in *.
    destruct HindBlockLen as [HindBlockLen HindBlkAddrsLen].
    auto.
  }
  iIntros (indBlkAddrsPadding_s) "[_ HindBlks]".

  iApply "Hϕ"; iFrame; auto.
Qed.

Theorem wp_Inode__UsedBlocks {l γ P addr σ} :
  {{{ pre_inode l P σ addr }}}
    Inode__UsedBlocks #l
    {{{ (s direct_s indirect_s indblks_s:Slice.t)
          numInd (dirAddrs indAddrs: list u64) (indBlkAddrsList: list (list u64)) (indBlocks: list Block),
        RET (slice_val s);
        ⌜list_to_set (take (length σ.(inode.blocks)) dirAddrs
                   ++ (take (numInd) indAddrs)
                   ++ (concat indBlkAddrsList))
        = σ.(inode.addrs)⌝ ∗
      is_alloced_blocks_slice σ s direct_s indirect_s indblks_s numInd dirAddrs indAddrs indBlkAddrsList ∗
      (is_alloced_blocks_slice σ s direct_s indirect_s indblks_s numInd dirAddrs indAddrs indBlkAddrsList -∗
                               pre_inode l P σ addr) }}}.
Proof.
  iIntros (Φ) "Hinode HΦ"; iNamed "Hinode".
  wp_call.
  iNamed "Hlockinv".
  iNamed "Hvolatile"; iNamed "Hdurable"; iNamed "Hfacts"; iNamed "Hhdr"; iNamed "Hdata".
  destruct Hlen as [HdirLen [HindirLen HszMax]].
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

  wp_apply (wp_forSlicePrefix
              (fun done todo =>
               ∃ s usedBlksList,
                 "%" ∷ ⌜ done ++ todo = (take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs)) ⌝ ∗
                 "%" ∷ ⌜ done = usedBlksList ⌝ ∗
                 "Hl0" ∷ (l0 ↦[slice.T uint64T] (slice_val s)) ∗
                 "HusedSlice" ∷ is_slice s uint64T 1 usedBlksList
      )%I
  with "[] [Hl0 Hdirect_small Hs]").
  { iIntros (i a done todo _).
    iModIntro.
    iIntros (lϕ) "Hinv HΦ"; iNamed "Hinv".
    wp_pures.
    wp_load.
    iDestruct (is_slice_sz with "HusedSlice") as %HusedSlicelen.
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
                 "indirect" ∷ (l ↦[Inode.S :: "indirect"] (slice_val indirect_s)) ∗
                 "HusedSlice" ∷ is_slice s uint64T 1 (usedBlksList ++ usedIndBlks)
      )%I
  with "[] [Hl0 Hindirect_small indirect HusedSlice]").
  { iIntros (i a done todo _).
    iModIntro.
    iIntros (lϕ) "Hinv HΦ"; iNamed "Hinv".
    wp_pures.
    wp_load.

    iDestruct (is_slice_sz with "HusedSlice") as %HusedSlicelen.
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

  iNamed "Hro_state".
  wp_apply (wp_forSlicePrefix
              (fun done todo =>
               ∃ s,
                 "%" ∷ ⌜ done ++ todo = (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs)) ⌝ ∗
                 "Hl0" ∷ (l0 ↦[slice.T uint64T] (slice_val s)) ∗
                 "indirect" ∷ (l ↦[Inode.S :: "indirect"] (slice_val indirect_s)) ∗
                 "Hindirect" ∷ is_slice indirect_s uint64T 1 (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs)) ∗
                 "HusedSlice" ∷
                 (let indBlkAddrsConcat := (concat (take (length done) ds.(impl_s.indBlkAddrsList))) in
                  is_slice s uint64T 1
                           (usedBlksList ++ indBlkAddrsConcat
                                         ++ (replicate (length indBlkAddrsConcat - (length indBlkAddrsConcat `mod` int.nat indirectNumBlocks))
                                                       (U64 0)))) ∗
                 "HindBlks" ∷ [∗ list] i↦a ∈ done ++ todo, ∃ indBlkAddrs indBlk,
                                                ⌜ ds.(impl_s.indBlkAddrsList) !! i = Some indBlkAddrs ⌝ ∗
                                                is_indirect a indBlkAddrs indBlk (ind_blocks_at_index σ i)
      )%I
  with "[] [Hl0 Hindirect_small HusedSlice Hindirect indirect]").
  { iIntros (i a done todo _).
    iModIntro.
    iIntros (lϕ) "Hinv HΦ"; iNamed "Hinv".
    wp_pures.
    wp_loadField.
    iApply big_sepL_app in "HindBlks".
    iDestruct "HindBlks" as "[HindBlksDone HindBlksTodo]".
    iDestruct (big_sepL_cons with "HindBlksTodo") as "[Ha HindBlksTodo]".
    iEval (rewrite -plus_n_O) in "Ha".
    iDestruct "Ha" as (indBlkAddrs indBlk) "[%HindBlkAddrsLookup Ha]".
    wp_apply (wp_readIndirect ds indirect_s indBlk indBlkAddrs (length done) d a with "[Ha Hindirect indirect]").
    {
      iFrame.
      repeat (iSplitR; [iPureIntro; eauto|]).
      { assert (length (done ++ a :: todo) = length (take ds.(impl_s.numInd) ds.(impl_s.indAddrs))) as tmp by (rewrite H3; auto).
        rewrite app_length take_length cons_length min_l in tmp; lia.
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
    iSplitL "Hs'".
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
  iNamed "Hvolatile"; iNamed "Hdurable"; iNamed "Hfacts"; iNamed "Hhdr"; iNamed "Hdata".
  destruct Hlen as [HdirLen [HindirLen HszMax]].
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
      destruct (list_lookup_lt _ ds.(impl_s.dirAddrs) (int.nat off)) as [a Hlookup].
      { rewrite /maxDirect. word. }
      iDestruct (is_slice_split with "Hdirect") as "[Hdirect_small Hdirect]".
      wp_apply (wp_SliceGet _ _ _ _ _ (take (length (σ.(inode.blocks))) ds.(impl_s.dirAddrs)) _ a with "[Hdirect_small]").
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
      assert (ds.(impl_s.numInd) <= maxIndirect) as HnumIndMax.
      {
        unfold roundUpDiv, MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *. lia.
      }
      assert (((int.val off - 500) `div` 512) <= ((length σ.(inode.blocks) - 500) `div` 512)) as Hoff. {
        apply Z_div_le; lia.
      }

      assert (int.val index < ds.(impl_s.numInd)) as HindexMax. {
        unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
        unfold roundUpDiv, MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *. lia.
      }
      destruct (list_lookup_lt _ (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs)) (int.nat index)) as [a Hlookup].
      {
        unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
        rewrite firstn_length Hindex.
        rewrite Min.min_l; word.
      }

      (* Now we actually step through program the *)
      wp_loadField.
      iDestruct (is_slice_split with "Hindirect") as "[Hindirect_small Hindirect]".
      wp_apply (wp_SliceGet _ _ _ _ 1 (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs)) _ a with "[Hindirect_small]"); iFrame; auto.

      iIntros "Hindirect_small".
      iDestruct (is_slice_split with "[$Hindirect_small $Hindirect]") as "Hindirect".
      iDestruct "HdataIndirect" as (indBlocks) "[%HindBlocksLen HdataIndirect]".
      assert (∃ indBlock, indBlocks !! int.nat index = Some indBlock) as [indBlk HlookupIndBlock].
      {
        apply lookup_lt_is_Some_2.
        rewrite HindBlocksLen.
        apply (lookup_lt_Some _ _ _ Hlookup).
      }
      iDestruct (big_sepL2_lookup_acc _ (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs)) _ (int.nat index) a with "HdataIndirect")
        as "[Hb HdataIndirect]"; eauto.

      wp_loadField.
      iDestruct "Hb" as (indBlkAddrs) "[%HaddrLookup HaddrIndirect]".
      wp_apply (wp_readIndirect ds indirect_s indBlk indBlkAddrs (int.nat index) d a
                  with "[indirect Hindirect HaddrIndirect]").
      {
        iFrame. repeat iSplit; eauto.
        iPureIntro; len.
      }
      iIntros (indBlkAddrs_s) "H". iNamed "H". iNamed "HindBlkIndirect".

      wp_let.
      wp_apply wp_indOff.
      { iPureIntro; auto. }
      iIntros (offset) "%Hoffset".

      (* More facts about offset *)
      assert ((int.val off - 500) `div` 512 * 512 = (512 * (int.val off - 500) `div` 512)) as HMulComm by lia.

      assert ((int.val off - 500) `div` 512 * 512  <= ((512 * (int.val off - 500)) `div` 512)) as HdivMulLe by lia.

      assert (int.val index * indirectNumBlocks <= int.val off -maxDirect ∧
              int.val off -maxDirect < (int.val index * indirectNumBlocks) + indirectNumBlocks)
        as [HoffLBound HoffUBound] by word.

      assert (int.val offset < length indBlkAddrs) as HoffsetInBounds.
      {
        unfold ind_blocks_at_index in Hlen.
        rewrite Hlen.
        rewrite Hoffset.
        unfold maxDirect, indirectNumBlocks in *.
        assert ((512 * int.val index) + int.val offset = int.val off - 500) by word.
        assert (int.val offset = (int.val off - 500) - (512 * int.val index)) as HoffsetVal by word.
        destruct (dec_ge (length σ.(inode.blocks)) ((500 + int.nat index * 512) + 512)) as [HlenGe | HlenNotGe].
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
        rewrite -HlookupInodeBlk.
        rewrite -> lookup_take by word.
        f_equal; word. }

      (* Continue through the program *)
      iDestruct (is_slice_split with "HindBlkAddrs") as "[HindBlkAddrs_small HindBlkAddrs]".

      assert ((indBlkAddrs ++ replicate (int.nat indirectNumBlocks - length indBlkAddrs) (U64 0)) !! int.nat offset = Some blkaddr) as HlookupBlkIndPadded. {
        rewrite -(lookup_app_l indBlkAddrs
                               (replicate (int.nat indirectNumBlocks - length indBlkAddrs) (U64 0)))
       in HlookupBlkInd; auto; try word.
      }
      wp_apply (wp_SliceGet _ _ _ _ 1 (indBlkAddrs++_) _ blkaddr with "[HindBlkAddrs_small]"); iFrame; auto.

      iIntros "HindBlkAddrs_small".
      iDestruct (is_slice_split with "[$HindBlkAddrs_small $HindBlkAddrs]") as "HindBlkAddrs".
      iDestruct (big_sepL2_lookup_acc _ _ _ _ _ with "Hdata") as "[Hb' Hdata]"; eauto.

      wp_apply (wp_Read with "Hb'"); iIntros (s) "[Hb' Hs]".
      wp_let.

      iSpecialize ("Hdata" with "Hb'").
      iAssert (∃ indBlkAddrs,
                  ⌜ds.(impl_s.indBlkAddrsList) !! int.nat index = Some indBlkAddrs⌝ ∗
                  is_indirect a indBlkAddrs indBlk (ind_blocks_at_index σ (int.nat index)))%I
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

      wp_apply (crash_lock.release_spec with "His_locked"); auto.
      (*wp_apply (release_spec with "[$Hlock $His_locked HP Hhdr addr
             size direct indirect Hdirect Hindirect HdataDirect HdataIndirect]").
      { iExists _; iFrame.
        iExists addrs.
        iExists direct_s, indirect_s, ds.(impl_s.dirAddrs), ds.(impl_s.indAddrs), sz, ds.(impl_s.numInd), ds.(impl_s.hdr). iFrame "∗ %".
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
  iNamed "Hvolatile"; iNamed "Hdurable"; iNamed "Hfacts"; iNamed "Hhdr"; iNamed "Hdata".
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
    iExists direct_s, indirect_s, ds.(impl_s.dirAddrs), ds.(impl_s.indAddrs), sz, ds.(impl_s.numInd), ds.(impl_s.hdr). iFrame "∗ %".
  }*)
  wp_pures.
  iApply ("HΦ" with "[$]").
Admitted.

Theorem wp_padInts {Stk E} enc (n: u64) (encoded : list encodable) (off: Z):
  {{{
    ⌜ int.val 0 ≤ int.val n ∧ off >= 8*(int.val n) ⌝ ∗
    is_enc enc 4096 encoded off
  }}}
    padInts enc #n @Stk ; E
  {{{ RET #()
;
    is_enc enc 4096 (encoded ++ (EncUInt64 <$> replicate (int.nat n) (U64 0))) (off-(8*int.val n))
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
                       "Henc" ∷ is_enc enc 4096 (encoded ++ (EncUInt64 <$> (replicate (int.nat i) (U64 0))))
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
      iExactEq "Henc".
      rewrite /named.
      f_equal; word.
  }
  {
    iSplitL "Henc"; iFrame; auto.
    iSplitR "Henc".
    - iPureIntro. word.
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
  (length(allocedDirAddrs) <= int.nat maxDirect ∧
   (Z.of_nat (length(allocedIndAddrs))) = numInd ∧
   sz <= MaxBlocks ∧
   numInd <= maxIndirect)
  ->
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
    "%Hencoded" ∷ ⌜block_encodes hdr ([EncUInt64 sz] ++ (EncUInt64 <$> allocedDirAddrs) ++ (EncUInt64 <$> (replicate (int.nat (maxDirect - length allocedDirAddrs)) (U64 0)))
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
  wp_apply wp_new_enc; iIntros (enc) "Henc".
  wp_pures.
  wp_loadField.
  iDestruct (is_slice_sz with "Hdirect") as %HDirlen.
  iDestruct (is_slice_sz with "Hindirect") as %HIndlen.
  autorewrite with len in HDirlen.
  autorewrite with len in HIndlen.
  destruct Hbound as [HallocedDirAddrsLen [HallocedIndAddrsLen [Hszmax HnumInd]]].

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
              8 * int.val (U64 (500 - int.val direct_s.(Slice.sz))))
    with 88 by word.

  wp_pures.
  wp_loadField.

  iDestruct (is_slice_split with "Hindirect") as "[Hindirect Hcapind]".
  wp_apply (wp_Enc__PutInts with "[$Henc $Hindirect]").
  { rewrite HallocedIndAddrsLen. word. }
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
