From RecordUpdate Require Import RecordSet.
From Perennial.goose_lang Require Import crash_modality.

From Goose.github_com.mit_pdos.perennial_examples Require Import indirect_inode.

From Perennial.program_proof.examples Require Import alloc_crash_proof indirect_inode_proof.
From Perennial.goose_lang.lib Require Import lock.crash_lock.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import typed_slice.
From Perennial.Helpers Require Import List.
From Perennial.program_proof Require Import marshal_proof disk_lib.

Hint Unfold inode.wf MaxBlocks indirectNumBlocks maxDirect maxIndirect: word.
Hint Unfold inode.wf MaxBlocks indirectNumBlocks maxDirect maxIndirect: auto.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Section goose.
Context `{!heapG Σ}.
Context `{!crashG Σ}.
Context `{!stagedG Σ}.
Context `{!allocG Σ}.

Context (inodeN allocN: namespace).

Implicit Types (σ: inode.t).
Implicit Types (l:loc) (γ:gname) (P: inode.t → iProp Σ).

Definition reserve_fupd E (Palloc: alloc.t → iProp Σ) : iProp Σ :=
  ∀ (σ σ': alloc.t) ma,
    ⌜match ma with
     | Some a => a ∈ alloc.free σ ∧ σ' = <[a:=block_reserved]> σ
     | None => σ' = σ ∧ alloc.free σ = ∅
     end⌝ -∗
  ▷ Palloc σ ={E}=∗ ▷ Palloc σ'.

(* free really means unreserve (we don't have a way to unallocate something
marked used) *)
Definition free_fupd E (Palloc: alloc.t → iProp Σ) (a:u64) : iProp Σ :=
  ∀ (σ: alloc.t),
    ⌜σ !! a = Some block_reserved⌝ -∗
  ▷ Palloc σ ={E}=∗ ▷ Palloc (<[a:=block_free]> σ).

(* This is useless because you need to do this together with some other action. *)
Definition use_fupd E (Palloc: alloc.t → iProp Σ) (a: u64): iProp Σ :=
  (∀ σ : alloc.t,
      ⌜σ !! a = Some block_reserved⌝ -∗
      ▷ Palloc σ ={E}=∗ ▷ Palloc (<[a:=block_used]> σ)).

Let Ψ (a: u64) := (∃ b, int.val a d↦ b)%I.

Theorem wp_appendDirect {l σ addr} (a: u64) b:
  {{{
    "Ha" ∷ int.val a d↦ b ∗
    "Hinv" ∷ inode_linv l σ addr
  }}}
  Inode__appendDirect #l #a
  {{{ (ok: bool), RET #ok; if ok then
      (∀ σ', ⌜σ' = set inode.blocks (λ bs, bs ++ [b]) (set inode.addrs ({[a]} ∪.) σ)⌝ -∗
                         "%Hsize" ∷ ⌜length σ.(inode.blocks) < maxDirect⌝
                         ∗ "Hinv" ∷ inode_linv l σ' addr)
      else ⌜ length σ.(inode.blocks) >= maxDirect ⌝ ∗ "Ha" ∷ int.val a d↦ b
  }}}.
Proof.
  iIntros (Φ) "Hpre". iNamed "Hpre". iNamed "Hinv".
  iNamed "Hdurable".
  iIntros "HΦ".

  (* A bunch of facts and prep stuff *)
  unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
  destruct Hlen as [HdirLen [HindirLen [HszMax HnumIndBlocks]]].
  iDestruct (is_slice_sz with "Hdirect") as %HlenDir.

  change ((set inode.blocks
            (λ bs : list Block, bs ++ [b])
            (set inode.addrs (union {[a]}) σ))
              .(inode.blocks)) with (σ.(inode.blocks) ++ [b]) in *.
  destruct HdirAddrs as [daddrs HdirAddrs].
  destruct HindAddrs as [iaddrs HindAddrs].
  assert (ds.(impl_s.numInd) <= 10) as HnumIndMax.
  {
    unfold MaxBlocks, roundUpDiv, indirectNumBlocks, maxDirect, indirectNumBlocks, maxIndirect in *.
    destruct (bool_decide (Z.of_nat (length σ.(inode.blocks)) <= 500)) eqn:H; rewrite HnumInd.
    + apply bool_decide_eq_true in H. rewrite Max.max_l; word.
    + apply bool_decide_eq_false in H. apply Znot_le_gt in H.
      rewrite Max.max_r; word.
  }
  assert (ds.(impl_s.numInd) = length iaddrs) as HiaddrsLen.
  {
    rewrite HindAddrs in HindirLen.
    rewrite app_length replicate_length in HindirLen.
    replace (Z.of_nat (length iaddrs + (int.nat (U64 10) - ds.(impl_s.numInd)))) with (length iaddrs + (10 - ds.(impl_s.numInd))) in HindirLen; try word.
  }
  assert (iaddrs = take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs)) as Hiaddrs.
  { rewrite HiaddrsLen HindAddrs. rewrite take_app; auto. }

  wp_call.
  wp_loadField.
  wp_if_destruct.
  (* Fits within maxDirect *)
  {
    replace (int.val (U64 (Z.of_nat (length σ.(inode.blocks))))) with (Z.of_nat (length σ.(inode.blocks))) in Heqb0 by word.
    assert (length (σ.(inode.blocks)) <= 500) as Hsz by word.
    assert (Z.of_nat ds.(impl_s.numInd) = 0) as HnumInd0.
    {
      rewrite HnumInd.
      unfold roundUpDiv, MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *; try word.
    }

    wp_loadField.
    wp_apply (wp_SliceAppend (V:=u64) with "[$Hdirect]").
    iIntros (direct_s') "Hdirect".
    Transparent slice.T.
    wp_storeField.
    wp_loadField.
    wp_storeField.
    wp_apply (wp_Inode__mkHdr l
      (length σ.(inode.blocks) + 1)
      ds.(impl_s.numInd)
      (take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs) ++ [a])
      (take
        ds.(impl_s.numInd)
        ds.(impl_s.indAddrs))
      direct_s' indirect_s with "[direct indirect size Hdirect Hindirect]").
    {
      repeat (split; len; simpl; try word).
    }
    {
      iFrame.
      replace (word.add (U64 (Z.of_nat (length σ.(inode.blocks)))) (U64 1))
      with (U64 (Z.of_nat (length σ.(inode.blocks)) + 1)); auto; word.
    }
    iIntros (s b') "(Hb & %Hencoded' &?&?&?&?&?)"; iNamed.
    wp_let.
    wp_loadField.
    wp_apply (wp_Write with "[Hhdr Hb]").
    { iExists ds.(impl_s.hdr); iFrame. }

    iIntros "[Hhdr Hb]".
    wp_pures.
    iApply "HΦ".
    iIntros.
    iFrame.
    iSplitR; auto.
    rewrite a0; simpl.
    iExists direct_s', indirect_s,
    (impl_s.mk
       b'
       ds.(impl_s.numInd)
       (take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs)
                                            ++ [a]
                                            ++ (drop (length σ'.(inode.blocks)) ds.(impl_s.dirAddrs)))
       ds.(impl_s.indAddrs)
       ds.(impl_s.indBlkAddrsList)
       ds.(impl_s.indBlocks)).
    unfold is_inode_durable_with.
    rewrite a0; simpl.
    rewrite Min.min_l in HdirAddrs; [ | word].

    assert ((length daddrs) = (length σ.(inode.blocks))%nat) as HdaddrsLen.
    {
      assert (length ds.(impl_s.dirAddrs) = length (daddrs ++ replicate (500 - length σ.(inode.blocks)) (U64 0))).
      {
        rewrite HdirAddrs. auto.
      }
      rewrite app_length replicate_length in H. assert (length ds.(impl_s.dirAddrs) = 500%nat) by word. rewrite H0 in H.
      word.
    }

    assert (daddrs = take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs)) as Hdaddrs.
    {
      rewrite HdirAddrs. rewrite -HdaddrsLen.
      rewrite take_app. auto.
    }

    assert (drop (length σ.(inode.blocks) + 1) ds.(impl_s.dirAddrs) = replicate (500%nat - (length σ.(inode.blocks) + 1)) (U64 0)) as HdirAddrsEnd.
    {
      change (int.nat (U64 500)) with 500%nat in *.
      rewrite HdirAddrs.
      replace (replicate (500%nat - length σ.(inode.blocks)) (U64 0)) with ((U64 0) :: (replicate (500%nat - (length σ.(inode.blocks) + 1)) (U64 0))).
      2: {
        replace (500%nat - length σ.(inode.blocks))%nat with (S (500%nat - (length σ.(inode.blocks) + 1%nat))%nat) by word.
        simpl; auto.
      }
      rewrite cons_middle app_assoc.
      rewrite -HdaddrsLen.
      assert (length (daddrs ++ [(U64 0)]) = (length daddrs + 1)%nat).
      { len. simpl. auto. }
      by rewrite -H drop_app.
    }

    (* prove the postcondition holds *)
    iFrame.

    (* Handle "Hdurable" first *)
    iSplitR "Hdirect size".
    {
      (* Hwf *)
      iSplitR.
      { iPureIntro. unfold inode.wf. simpl. rewrite app_length; simpl. word. }

      (* Haddrs_set *)
      iSplitR.
      {
        iPureIntro; simpl.
        rewrite app_length; simpl.
        rewrite cons_middle.
        replace (take (length σ.(inode.blocks) + 1)
                      (take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs) ++ [a]
                            ++ drop ((length σ.(inode.blocks) + 1)) ds.(impl_s.dirAddrs)))
          with (take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs) ++ [a]).
        2: {
          rewrite app_assoc.
          assert ((length σ.(inode.blocks) + 1)%nat = length ((take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs) ++ [a]))) as H.
          { rewrite app_length. rewrite take_length Min.min_l; simpl; word. }
          rewrite H.
          rewrite (take_app (take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs) ++ [a])); auto.
        }
        assert (((take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs) ++ [a])
                   ++ take ds.(impl_s.numInd) ds.(impl_s.indAddrs)
                   ++ foldl (λ acc ls : list u64, acc ++ ls) [] ds.(impl_s.indBlkAddrsList))
                  ≡ₚ
                  a :: (take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs)
                   ++ take ds.(impl_s.numInd) ds.(impl_s.indAddrs)
                   ++ foldl (λ acc ls : list u64, acc ++ ls) [] ds.(impl_s.indBlkAddrsList)))
          as Hperm.
        { by rewrite -app_assoc -cons_middle -Permutation_middle. }
        rewrite Hperm.
        rewrite list_to_set_cons.
        rewrite Haddrs_set. auto.
      }

      (* HdirAddrs *)
      iSplitR.
      {
        iPureIntro. eauto.
        assert (ds.(impl_s.numInd) = 0%nat) by word; rewrite HnumInd0 H in Hencoded'.
        rewrite take_0 nil_length in Hencoded'.
        unfold MaxBlocks, indirectNumBlocks, maxDirect, maxIndirect in *.
        change (10 - 0%nat) with 10 in *.
        rewrite fmap_nil app_nil_l in Hencoded'.
        change ((set inode.blocks
              (λ bs : list Block, bs ++ [b])
              (set inode.addrs (union {[a]}) σ))
                .(inode.blocks)) with (σ.(inode.blocks) ++ [b]).
        exists (daddrs ++ [a]).
        rewrite app_length; simpl.
        rewrite HdirAddrsEnd.
        rewrite cons_middle app_assoc.
        rewrite HdirAddrs.
        rewrite -HdaddrsLen take_app.
        rewrite Min.min_l; auto; word.
      }

      (* HindAddrs *)
      iSplitR.
      { iPureIntro. exists iaddrs. auto. }

      (* Hencoded *)
      iSplitR.
      {
        iPureIntro.
        rewrite Hencoded'.
        unfold maxDirect in *.
        repeat rewrite app_length.
        change (length [_]) with 1%nat.
        rewrite HdirAddrsEnd -Hiaddrs /maxIndirect -HiaddrsLen.
        replace (int.nat (U64 (10 - Z.of_nat ds.(impl_s.numInd))))
          with ((int.nat (U64 10) - ds.(impl_s.numInd))%nat) by word.
        rewrite HindAddrs.
        replace
          (int.nat (U64 (500 - Z.of_nat (length (take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs)) + 1)))%nat)
          with ((500 - (length σ.(inode.blocks) + 1))%nat); auto.
        2: {
          rewrite take_length. rewrite Min.min_l; word.
        }
        replace
          (EncUInt64 <$> iaddrs ++ replicate (int.nat (U64 10) - ds.(impl_s.numInd)) (U64 0))
          with ((EncUInt64 <$> iaddrs) ++ (EncUInt64 <$> replicate (int.nat (U64 10) - ds.(impl_s.numInd)) (U64 0)));
        [ | by rewrite fmap_app].
        replace
        (EncUInt64 <$> (take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs) ++ [a] ++
                             (replicate (500 - (length σ.(inode.blocks) + 1)) (U64 0))))
          with ((EncUInt64 <$> take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs) ++ [a])
                     ++ (EncUInt64 <$> replicate (500 - (length σ.(inode.blocks) + 1)) (U64 0))).
        2: { rewrite app_assoc -fmap_app. auto. }
        repeat rewrite app_assoc.
        replace (U64 (Z.of_nat (length σ.(inode.blocks)) + 1)) with
            (U64 (Z.of_nat (length σ.(inode.blocks) + 1%nat))) by word.
        reflexivity.
      }

      (* Hlen *)
      iSplitR.
      { iPureIntro.
        unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
        rewrite HdirLen.
        repeat (split; auto); len; simpl; try word.
        rewrite Min.min_l; [len | word].
      }

      (* HnumInd *)
      iSplitR.
      {
        iPureIntro. rewrite HnumInd.
        unfold maxDirect, indirectNumBlocks in *.
        rewrite app_length; simpl. repeat rewrite max_l; word.
      }

      (* Hdirect *)
      iSplitL "HdataDirect Ha".
      {
        rewrite /maxDirect -Hdaddrs.
        assert ((int.nat (U64 500) `min` length σ.(inode.blocks))%nat =
                (length σ.(inode.blocks))) by word.
        assert ((int.nat (U64 500) `min` length (σ.(inode.blocks) ++ [b]))%nat =
                 (length (σ.(inode.blocks) ++ [b]))%nat) by (len; simpl; word).
        rewrite H0.
        assert (length (daddrs ++ [a]) = length (σ.(inode.blocks) ++ [b])) by (len; simpl; word).
        replace (daddrs ++ a :: drop (length (σ.(inode.blocks) ++ [b])) ds.(impl_s.dirAddrs)) with
            ((daddrs ++ [a]) ++ drop (length (σ.(inode.blocks) ++ [b])) ds.(impl_s.dirAddrs))
        by (rewrite -app_assoc -cons_middle; auto).
        rewrite -H1 take_app. rewrite H1 firstn_all.
        iApply (big_sepL2_app with "[HdataDirect]"); simpl; auto.
        { rewrite Min.min_r; [ | word].
          rewrite -HdaddrsLen HdirAddrs take_app. rewrite HdaddrsLen firstn_all. auto.
        }
      }

      (* Hindirect *)
      {
        assert (ds.(impl_s.numInd) = 0%nat) by word; rewrite H.
        rewrite take_0.
        symmetry in HnumIndBlocks.
        rewrite H in HnumIndBlocks.
        rewrite (nil_length_inv _ HnumIndBlocks).
        repeat rewrite big_sepL2_nil; auto.
      }
    }
    (* Greater than maxDirect already, return false *)
    {
      iSplitL "size".
      (* size *)
      + len. simpl.
        assert ((Z.of_nat (length σ.(inode.blocks)) + 1) = Z.of_nat (length σ.(inode.blocks) + 1)) by word.
        rewrite H.
        auto.
      (* Hdirect *)
      + rewrite -Hdaddrs.
        assert (length (daddrs ++ [a]) = length (σ.(inode.blocks) ++ [b])) by (len; simpl; word).
        replace (daddrs ++ a :: drop (length (σ.(inode.blocks) ++ [b])) ds.(impl_s.dirAddrs)) with
            ((daddrs ++ [a]) ++ drop (length (σ.(inode.blocks) ++ [b])) ds.(impl_s.dirAddrs))
        by (rewrite -app_assoc -cons_middle; auto).
        rewrite -H take_app; auto.
    }
  }
  (* cannot fit in direct blocks, return false *)
  {
    iApply "HΦ".
    iFrame.

    iPureIntro.
    apply Znot_lt_ge in Heqb0.
    replace (int.val (U64 (Z.of_nat (length σ.(inode.blocks))))) with (Z.of_nat (length σ.(inode.blocks))) in Heqb0; word.
  }
Qed.

Theorem wp_writeIndirect {l σ addr d lref} ds direct_s indirect_s
        (indA: u64) (indBlkAddrs: list u64)
        (index offset : nat) (a: u64) (b: Block) indblkaddrs_s :
  {{{
       "%Hsize" ∷ ⌜length σ.(inode.blocks) >= maxDirect ∧ length σ.(inode.blocks) < MaxBlocks ∧
        (*Assert that there is still room in the last indirect block*)
        ((length σ.(inode.blocks) - maxDirect) `div` indirectNumBlocks < int.val indirect_s.(Slice.sz))
       ⌝ ∗
       "%Hlookup" ∷ ⌜(take ds.(impl_s.numInd) ds.(impl_s.indAddrs)) !! index = Some indA
                  ∧ ds.(impl_s.indBlkAddrsList) !! index = Some indBlkAddrs
                  ∧ ∃ indBlock, ds.(impl_s.indBlocks) !! index = Some indBlock⌝ ∗
       "%Hlen" ∷ ⌜length indBlkAddrs < int.nat indirectNumBlocks⌝ ∗
       "Ha" ∷ int.val a d↦ b ∗
       "Haddr_s" ∷ is_slice indblkaddrs_s uint64T 1
       (indBlkAddrs ++ [a] ++ replicate (int.nat indirectNumBlocks - (length (indBlkAddrs) + 1)) (U64 0)) ∗
       "Hro_state" ∷ inode_state l d lref ∗
       "Hinv" ∷ inode_linv_with l σ addr direct_s indirect_s ds
  }}}
  Inode__writeIndirect #l #indA (slice_val indblkaddrs_s)
  {{{ RET #();
      ∀ σ' ds',
          (⌜σ' = set inode.blocks (λ bs, bs ++ [b])
                  (set inode.addrs ({[a]} ∪.) σ)⌝
         ∗ (∀ hdr,
               (int.val addr d↦ hdr) -∗
          ⌜∃ indBlkAddrs, ds' = set impl_s.indBlkAddrsList
            (λ ls, <[int.nat index:= (indBlkAddrs ++ [a] ++ replicate (int.nat indirectNumBlocks - (length (indBlkAddrs) + 1)) (U64 0))]> ls)
                      (set impl_s.hdr (λ _, hdr) ds)⌝))
      -∗ "Hinv" ∷ inode_linv_with l σ' addr direct_s indirect_s ds'
  }}}.
Proof.
  iIntros (Φ) "Hpre". iNamed "Hpre".
  iIntros "HΦ".

  (* A bunch of facts and prep stuff. Factor this out!!! *)
  iNamed "Hinv".
  iNamed "Hro_state".
  iNamed "Hdurable".
  unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
  destruct Hlen0 as [HdirLen [HindirLen [HszMax HnumIndBlocks]]].
  (*destruct Hsize as [HsizeMin HsizeMax HnumIndSize HmodPos].*)
  destruct Hsize as [HsizeMin [HsizeMax HmodPos]].
  destruct Hlookup as [HlookupIndA [HlookupIndBlkAddrs [indBlock HlookupIndBlk]]].
  iDestruct (is_slice_sz with "Hindirect") as %HlenInd.

  change ((set inode.blocks
            (λ bs : list Block, bs ++ [b])
            (set inode.addrs (union {[a]}) σ))
              .(inode.blocks)) with (σ.(inode.blocks) ++ [b]) in *.
  destruct HdirAddrs as [daddrs HdirAddrs].
  destruct HindAddrs as [iaddrs HindAddrs].
  assert (ds.(impl_s.numInd) <= 10) as HnumIndMax.
  {
    unfold MaxBlocks, roundUpDiv, indirectNumBlocks, maxDirect, indirectNumBlocks, maxIndirect in *.
    destruct (bool_decide (Z.of_nat (length σ.(inode.blocks)) <= 500)) eqn:H; rewrite HnumInd.
    + apply bool_decide_eq_true in H. rewrite Max.max_l; word.
    + apply bool_decide_eq_false in H. apply Znot_le_gt in H.
      rewrite Max.max_r; word.
  }
assert (ds.(impl_s.numInd) = length iaddrs) as HiaddrsLen.
  {
    rewrite HindAddrs in HindirLen.
    rewrite app_length replicate_length in HindirLen.
    replace (Z.of_nat (length iaddrs + (int.nat (U64 10) - ds.(impl_s.numInd)))) with (length iaddrs + (10 - ds.(impl_s.numInd))) in HindirLen; try word.
  }
  assert (iaddrs = take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs)) as Hiaddrs.
  { rewrite HiaddrsLen HindAddrs. rewrite take_app; auto. }

  wp_call.
  (*PrepIndirect*)
  wp_call.
  wp_apply wp_new_enc.
  iIntros (enc) "[Henc %HencSz]".
  wp_let.
  iDestruct (is_slice_split with "Haddr_s") as "[Haddr_s_small Haddr_s]".
  wp_apply (wp_Enc__PutInts _ _ enc _ indblkaddrs_s 1
       (indBlkAddrs ++ [a] ++ replicate (int.nat indirectNumBlocks - (length (indBlkAddrs) + 1)) (U64 0)) 4096
              with "[Henc Haddr_s_small]").
    { repeat rewrite app_length /indirectNumBlocks. rewrite replicate_length. simpl. word. }
    { iSplitL "Henc"; iFrame; auto. }
    rewrite app_nil_l.

    iIntros "[Henc Haddr_s_small]".
    iDestruct (is_slice_split with "[$Haddr_s_small $Haddr_s]") as "Haddr_s".
    wp_pures.
    wp_apply (wp_Enc__Finish with "Henc").
    iIntros (s) "[Hs %]".
    wp_pures.
    iDestruct (big_sepL2_lookup_acc _ (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs))
                                    ds.(impl_s.indBlocks) index indA indBlock
                 with "[HdataIndirect]") as "[Hb HdataIndirect]"; eauto.
    assert (Z.to_nat (4096 - 8 * length (indBlkAddrs ++ [a] ++ replicate (int.nat indirectNumBlocks - (length indBlkAddrs + 1)) (U64 0)))
            = 0%nat) as Hrem0.
    {
      repeat rewrite app_length /indirectNumBlocks. rewrite replicate_length. simpl. word.
    }
    rewrite Hrem0 replicate_0 app_nil_r.
    wp_apply (wp_Write _ _ indA s 1
            (list_to_block (encode (EncUInt64 <$>
            indBlkAddrs ++ [a] ++ replicate (int.nat indirectNumBlocks - (length indBlkAddrs + 1)) (U64 0))))
            _ with "[Hs Hb]").
    {
      iDestruct "Hb" as (indBlkAddrs0) "[%HlookupIndBlkAddrs0 HisIndirect]"; iNamed "HisIndirect".
      iExists indBlock; iFrame.
      rewrite list_to_block_to_vals; auto.
      rewrite (length_encode_fmap_uniform 8).
      + repeat rewrite app_length. rewrite replicate_length. simpl; word.
      + intros. by rewrite -encode_singleton encode_singleton_length.
    }

    iIntros "[HindA Hs]".
    wp_pures.
    wp_loadField.
    wp_storeField.
    wp_apply (wp_Inode__mkHdr
                l
                (length σ.(inode.blocks) + 1)
                ds.(impl_s.numInd)
                (take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs))
                (take ds.(impl_s.numInd) ds.(impl_s.indAddrs))
                direct_s indirect_s
                with "[direct indirect size Hdirect Hindirect]").
    {
      unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
      repeat (split; len; simpl; try word).
    }
    {
      replace (word.add (U64 (Z.of_nat (length σ.(inode.blocks)))) (U64 1)) with
            (U64 (Z.of_nat (length σ.(inode.blocks)) + 1)) by word.
      iFrame.
    }

    iIntros (hdr_slice hdr) "[Hs' H]"; iNamed "H".
    wp_let.
    wp_loadField.
    wp_apply (wp_Write with "[Hs' Hhdr]").
    { iExists ds.(impl_s.hdr); iFrame. }

    iIntros "[Hhdr Hhdr_slice_small]".
    iApply "HΦ".
    iFrame.
    iIntros (σ' ds') "[%Hσ' Hds']".
    iPoseProof ("Hds'" $! hdr with "Hhdr") as "%Hds'".
    destruct Hds' as [indBlkAddrs' Hds'].

    (*Prove postcondition holds*)
    rewrite Hσ' Hds'; simpl.
    iSplitR "size Hdirect Hindirect"; iFrame.
    {
      iSplitR.
      { iPureIntro. unfold inode.wf. simpl. rewrite app_length; simpl. word. }

      (* Haddrs_set *)
      iSplitR.
      {
        iPureIntro; simpl.
        rewrite app_length; simpl.
        (*Need to show that list within a list contains element and is a permutation... *)
        (*this is going to be very annoying*)
        rewrite app_assoc.
        (*Check list_to_set_app.*)
        admit.
      }

      (* HdirAddrs *)
      iSplitR.
      {
        iPureIntro. simpl. exists daddrs.
        unfold MaxBlocks, indirectNumBlocks, maxDirect, maxIndirect in *.
        rewrite min_r in HdirAddrs.
        + rewrite min_r; auto.
          rewrite app_length; simpl. word.
        + simpl. word.
      }

      (* HindAddrs *)
      iSplitR.
      { iPureIntro. simpl. exists iaddrs. auto. }

      (* Hencoded *)
      iSplitR.
      {
        iPureIntro.
        change ((set impl_s.indBlkAddrsList _
                     (set impl_s.hdr (λ _ : Block, hdr) ds)).(impl_s.hdr)) with
            hdr.
        change ((set impl_s.indBlkAddrsList _
                     (set impl_s.hdr (λ _ : Block, hdr) ds)).(impl_s.dirAddrs)) with
            ds.(impl_s.dirAddrs).
        change ((set impl_s.indBlkAddrsList _
                     (set impl_s.hdr (λ _ : Block, hdr) ds)).(impl_s.numInd)) with
            ds.(impl_s.numInd).
        change ((set impl_s.indBlkAddrsList _
                     (set impl_s.hdr (λ _ : Block, hdr) ds)).(impl_s.indAddrs)) with
            ds.(impl_s.indAddrs).
        change ((set inode.blocks (λ bs : list Block, bs ++ [b]) (set inode.addrs (union {[a]}) σ)).(inode.blocks))
          with (σ.(inode.blocks) ++ [b]).
        rewrite app_length. change (length [_]) with 1%nat.
        rewrite Hencoded0.
        rewrite take_length; rewrite min_r; [|word].
        rewrite /maxDirect -HdirLen replicate_0 fmap_nil app_nil_l.
        replace (EncUInt64 <$> ds.(impl_s.indAddrs)) with
            ((EncUInt64 <$> take ds.(impl_s.numInd) ds.(impl_s.indAddrs))
               ++ (EncUInt64 <$> replicate (int.nat (maxIndirect - length (take ds.(impl_s.numInd) ds.(impl_s.indAddrs)))) (U64 0))).
        2: {
          rewrite -Hiaddrs /maxIndirect HindAddrs HiaddrsLen fmap_app.
          replace
            (int.nat (U64 (10 - Z.of_nat (length iaddrs))))
            with ((int.nat (U64 10) - length iaddrs)%nat) by word.
          auto.
        }
        replace (U64 (Z.of_nat (length σ.(inode.blocks) + 1))) with
            (U64 (Z.of_nat (length σ.(inode.blocks)) + 1)) by word.
        repeat rewrite -app_assoc.
        rewrite take_ge; auto; word.
      }

      (* Hlen *)
      iSplitR.
      { iPureIntro.
        unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
        repeat (split; auto); len; simpl; try word.
        len. simpl. word.
      }

      (* HnumInd *)
      iSplitR.
      {
        iPureIntro. rewrite HnumInd.
        unfold roundUpDiv, maxDirect, indirectNumBlocks in *.
        rewrite app_length; simpl.
        repeat rewrite max_r; try word.
        admit.
      }

      (* Hdirect *)
      iSplitL "HdataDirect".
      {
        simpl. rewrite /maxDirect.
        repeat rewrite min_l.
        + assert (take (int.nat 500) σ.(inode.blocks) = take (int.nat 500) (σ.(inode.blocks) ++ [b])).
          { rewrite take_app_le; auto; word. }
            by rewrite H0.
        + rewrite app_length; simpl. word.
        + simpl. word.
      }

      (* Hindirect *)
      {
        simpl. admit.
      }
    }
  rewrite app_length. simpl. iSplitL "size".
  + by replace (U64 (Z.of_nat (length σ.(inode.blocks)) + 1)) with
          (U64 (Z.of_nat (length σ.(inode.blocks) + 1))) by word.
  + repeat rewrite take_ge; auto;
      replace (length ds.(impl_s.dirAddrs)) with 500%nat; word.

Admitted.

Theorem wp_appendIndirect {l σ addr d lref direct_s indirect_s ds} (a: u64) b:
  {{{
    "%Hsize" ∷ ⌜length σ.(inode.blocks) >= maxDirect ∧ length σ.(inode.blocks) < MaxBlocks⌝ ∗
    "Hro_state" ∷ inode_state l d lref ∗
    "Hinv" ∷ inode_linv_with l σ addr direct_s indirect_s ds ∗
    "Ha" ∷ int.val a d↦ b
  }}}
  Inode__appendIndirect #l #a
  {{{ (ok: bool), RET #ok;
      if ok then
        (∀ σ' ds' index offset,
            (⌜σ' = set inode.blocks (λ bs, bs ++ [b]) (set inode.addrs ({[a]} ∪.) σ) ∧
            index = (length σ.(inode.blocks) - maxDirect) `div` indirectNumBlocks ∧
            offset = (length σ.(inode.blocks) - maxDirect) `mod` indirectNumBlocks⌝ ∗
           (∀ hdr, int.val addr d↦ hdr -∗
            ⌜∃ indBlkAddrs, ds' = set impl_s.indBlkAddrsList
            (λ ls, <[int.nat index:= (indBlkAddrs ++ [a] ++ replicate (int.nat indirectNumBlocks - (length (indBlkAddrs) + 1)) (U64 0))]> ls)
                      (set impl_s.hdr (λ _, hdr) ds)⌝))
        -∗ "Hinv" ∷ inode_linv_with l σ' addr direct_s indirect_s ds')
      else
        "Hinv" ∷ inode_linv_with l σ addr direct_s indirect_s ds ∗
        "Ha" ∷ int.val a d↦ b ∗
        "Hsize" ∷ ⌜ (roundUpDiv ((length σ.(inode.blocks)) - maxDirect) indirectNumBlocks >= int.val indirect_s.(Slice.sz)) ⌝
  }}}.
Proof.
  iIntros (Φ) "Hpre". iNamed "Hpre".
  iIntros "HΦ".

  (* A bunch of facts and prep stuff *)
  iNamed "Hinv".
  iNamed "Hro_state".
  iNamed "Hdurable".
  unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
  destruct Hlen as [HdirLen [HindirLen [HszMax HnumIndBlocks]]].
  destruct Hsize as [HszMin HszMaxAppend].
  iDestruct (is_slice_sz with "Hindirect") as %HlenInd.

  change ((set inode.blocks
            (λ bs : list Block, bs ++ [b])
            (set inode.addrs (union {[a]}) σ))
              .(inode.blocks)) with (σ.(inode.blocks) ++ [b]) in *.
  destruct HdirAddrs as [daddrs HdirAddrs].
  destruct HindAddrs as [iaddrs HindAddrs].
  assert (ds.(impl_s.numInd) <= 10) as HnumIndMax.
  {
    unfold MaxBlocks, roundUpDiv, indirectNumBlocks, maxDirect, indirectNumBlocks, maxIndirect in *.
    destruct (bool_decide (Z.of_nat (length σ.(inode.blocks)) <= 500)) eqn:H; rewrite HnumInd.
    + apply bool_decide_eq_true in H. rewrite Max.max_l; word.
    + apply bool_decide_eq_false in H. apply Znot_le_gt in H.
      rewrite Max.max_r; word.
  }
  assert (ds.(impl_s.numInd) = length iaddrs) as HiaddrsLen.
  {
    rewrite HindAddrs in HindirLen.
    rewrite app_length replicate_length in HindirLen.
    replace (Z.of_nat (length iaddrs + (int.nat (U64 10) - ds.(impl_s.numInd)))) with (length iaddrs + (10 - ds.(impl_s.numInd))) in HindirLen; try word.
  }
  assert (iaddrs = take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs)) as Hiaddrs.
  { rewrite HiaddrsLen HindAddrs. rewrite take_app; auto. }

  wp_call.
  wp_loadField.
  wp_apply wp_slice_len.
  wp_loadField.
  wp_apply (wp_indNum); [ iPureIntro; word | ].

  iIntros (indNum) "%HindNum".
  unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
  wp_if_destruct.
  (* Does not fit in allocated indBlocks *)
  {
    iApply "HΦ".
    iFrame.
    repeat (iSplitR; iPureIntro; [repeat (split; eauto)|]).
    rewrite /list.untype fmap_length -Hiaddrs in HlenInd.
    assert (Z.of_nat (length iaddrs) = int.val indirect_s.(Slice.sz)) by word.
    rewrite -H -HiaddrsLen.
    rewrite HnumInd /roundUpDiv; word.
  }

  (*Fits! Don't need to allocate another block, phew*)
  {
    wp_loadField.
    wp_apply (wp_indNum); [word|].
    iIntros (index) "%Hindex".

    (* Here are a bunch of facts *)
    (* TODO these are replicated from READ *)
    assert (int.val index < ds.(impl_s.numInd)) as HindexMax. {
      rewrite /list.untype fmap_length take_length Min.min_l in HlenInd; word.
    }
    destruct (list_lookup_lt _ (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs)) (int.nat index)) as [indA Hlookup].
    {
      unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
      rewrite firstn_length.
      rewrite Min.min_l; word.
    }
    destruct (list_lookup_lt _ ds.(impl_s.indBlocks) (int.nat index)) as [indBlk HlookupBlk].
    {
      unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
      word.
    }

    wp_loadField.
    iDestruct (is_slice_split with "Hindirect") as "[Hindirect_small Hindirect]".
    wp_apply (wp_SliceGet _ _ _ _ 1 (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs)) _ indA with "[Hindirect_small]"); iFrame; auto.

    iIntros "Hindirect_small".
    iDestruct (is_slice_split with "[$Hindirect_small $Hindirect]") as "Hindirect".
    iDestruct (big_sepL2_lookup_acc _ (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs)) _ (int.nat index) indA with "HdataIndirect") as "[Hb HdataIndirect]"; eauto.

    wp_pures.
    wp_loadField.
    iDestruct "Hb" as (indBlkAddrs) "[%HaddrLookup HaddrIndirect]".
    wp_apply (wp_readIndirect ds indirect_s indBlk indBlkAddrs (int.nat index) d indA
                with "[indirect Hindirect HaddrIndirect]").
    {
      iFrame. repeat iSplit; eauto. word.
    }
    iIntros (indblkaddrs_s) "H". iNamed "H". iNamed "HindBlkIndirect".
    destruct HindBlockLen as [HindBlockLen HindBlkAddrsLen].
    wp_let.
    wp_loadField.
    wp_apply wp_indOff.
    { iPureIntro; unfold maxDirect; auto. word. }
    iIntros (offset) "%Hoffset".

    iDestruct (is_slice_split with "HindBlkAddrs") as "[HindBlkAddrs_small HindBlkAddrs_cap]".
    wp_apply (wp_SliceSet with "[$HindBlkAddrs_small]").
    {

      iSplit; auto.
      iPureIntro.
      apply lookup_lt_is_Some_2.
      unfold maxDirect, indirectNumBlocks in *.
      rewrite fmap_length HindBlockLen.
      assert (int.val offset < 512).
      {
        rewrite Hoffset. by apply Z_mod_lt.
      }
      word.
    }
    iIntros "HindBlkAddrs_small".
    wp_pures.
    iDestruct (is_slice_split with "[$HindBlkAddrs_small $HindBlkAddrs_cap]") as "HindBlkAddrs".

    wp_apply (wp_writeIndirect ds direct_s indirect_s indA indBlkAddrs
                (int.nat index) (int.nat offset) a b indblkaddrs_s
              with "[-HΦ]").
    {
      iFrame; eauto.
      iSplitR; [iPureIntro; repeat split; simpl; eauto|].
      {
        unfold maxDirect, indirectNumBlocks in *.
        rewrite HindNum in Heqb0.
        pose (Znot_le_gt _ _ Heqb0) as HindNumGt.
        replace (int.val (length σ.(inode.blocks))) with (Z.of_nat (length σ.(inode.blocks))) in * by word.
        word.
      }

      iSplitR; [iPureIntro; split; eauto|].
      iSplitR; [iPureIntro; eauto|].
      (* Show that there is still room in this indirect block *)
      {
        rewrite Hlen /ind_blocks_at_index subslice_to_end;
        rewrite Hindex; unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
        + rewrite drop_length; word.
        + word.
      }

      iSplitL "HindBlkAddrs"; auto.
      {
        rewrite /is_slice /list.untype.
        rewrite -list_fmap_insert.
        assert (<[int.nat offset:=a]>
                (indBlkAddrs ++ replicate (int.nat indirectNumBlocks - length indBlkAddrs) (U64 0))
                =  indBlkAddrs ++ [a] ++ replicate (int.nat indirectNumBlocks - (length indBlkAddrs + 1)) (U64 0)).
        {
          assert ((length indBlkAddrs + 0)%nat = int.nat offset).
          {
            rewrite Hoffset Hlen /ind_blocks_at_index Hindex /maxDirect /indirectNumBlocks.
            rewrite subslice_to_end; [rewrite drop_length|]; word.
          }
          rewrite -H.
          rewrite insert_app_r.
          replace (replicate (int.nat indirectNumBlocks - length indBlkAddrs) (U64 0))
                 with
                   ([U64 0] ++ replicate (int.nat indirectNumBlocks - (length indBlkAddrs + 1)) (U64 0)).
          2: {
            simpl. rewrite -replicate_S.
            replace (S (int.nat (U64 indirectNumBlocks) - (length indBlkAddrs + 1)))  with
                 (int.nat (U64 indirectNumBlocks) - length indBlkAddrs)%nat by word; auto.
          }
          rewrite insert_app_l; auto.
        }
        rewrite H.
        auto.
      }
      iSplitR; unfold inode_state; eauto.
      repeat (iSplitR; [iPureIntro; simpl; eauto|]).

      (* HdataIndirect *)
      {
        iAssert (∃ indBlkAddrs,
                  ⌜ds.(impl_s.indBlkAddrsList) !! int.nat index = Some indBlkAddrs⌝ ∗
                  is_indirect indA indBlkAddrs indBlk (ind_blocks_at_index σ (int.nat index)))%I
        with "[diskAddr Hdata]" as "HaddrIndirect".
        {
          iExists indBlkAddrs.
          unfold is_indirect.
          iFrame. iSplit; auto.
        }
        by iSpecialize ("HdataIndirect" with "HaddrIndirect").
      }
    }

    iIntros "H".
    wp_pures.
    iApply "HΦ"; eauto.
    iIntros (σ' ds' index0 offset0) "[%H Hds']".
    destruct H as [Hσ' [Hindex0 Hoffset0]].
    iApply ("H" $! σ' ds').
    iSplit; [iPureIntro; eauto|].
    rewrite /maxDirect /indirectNumBlocks in Hindex, Hoffset.
    assert (int.nat index = int.nat index0).
    {
      replace ((int.val (length σ.(inode.blocks)) - 500) `div` 512) with ((length σ.(inode.blocks) - 500) `div` 512) in Hindex by word.
      rewrite -Hindex in Hindex0. word.
    }
    assert (int.nat offset = int.nat offset0).
    {
      replace ((int.val (length σ.(inode.blocks)) - 500) `mod` 512) with ((length σ.(inode.blocks) - 500) `mod` 512) in Hoffset by word.
      rewrite -Hoffset in Hoffset0; word.
    }
    replace (int.nat (U64 (Z.of_nat (int.nat index)))) with (int.nat index) by word.
    rewrite H. auto.
  }
Qed.

Theorem wpc_Inode__Append {k E2}  (*  *)
        {l k' P addr}
        (* allocator stuff *)
        {Palloc γalloc domain n}
        (alloc_ref: loc) q (b_s: Slice.t) (b0: Block) :
  (S (S k) < n)%nat →
  (S (S k) < k')%nat →
  nroot.@"readonly" ## allocN →
  nroot.@"readonly" ## inodeN →
  inodeN ## allocN →
  ∀ Φ Φc,
      "Hinode" ∷ is_inode inodeN l (LVL k') P addr ∗ (* XXX why did I need to put inodeN here? *)
      "Hbdata" ∷ is_block b_s q b0 ∗
      "#Halloc" ∷ is_allocator Palloc Ψ allocN alloc_ref domain γalloc n ∗
      "#Halloc_fupd" ∷ □ reserve_fupd (⊤ ∖ ↑allocN) Palloc ∗
      "#Hfree_fupd" ∷ □ (∀ a, free_fupd (⊤ ∖ ↑allocN) Palloc a) ∗
      "Hfupd" ∷ (Φc ∧ ▷ (Φ #false ∧ ∀ σ σ' addr',
        ⌜σ' = set inode.blocks (λ bs, bs ++ [b0])
                              (set inode.addrs ({[addr']} ∪.) σ)⌝ -∗
        ⌜inode.wf σ⌝ -∗
        ∀ s,
        ⌜s !! addr' = Some block_reserved⌝ -∗
         ▷ P σ ∗ ▷ Palloc s ={⊤ ∖ ↑allocN ∖ ↑inodeN}=∗
         ▷ P σ' ∗ ▷ Palloc (<[addr' := block_used]> s) ∗ (Φc ∧ Φ #true))) -∗
  WPC Inode__Append #l (slice_val b_s) #alloc_ref @ NotStuck; LVL (S (S k)); ⊤; E2 {{ Φ }} {{ Φc }}.
Proof.
  iIntros (????? Φ Φc) "Hpre"; iNamed "Hpre".
  iNamed "Hinode". iNamed "Hro_state".
Admitted.
End goose.

(* to preserve backwards-compatibility *)
Ltac Zify.zify_post_hook ::= idtac.

