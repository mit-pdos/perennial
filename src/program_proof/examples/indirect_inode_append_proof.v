From RecordUpdate Require Import RecordSet.
From Perennial.goose_lang Require Import crash_modality.

From Goose.github_com.mit_pdos.perennial_examples Require Import indirect_inode.

From Perennial.program_proof.examples Require Import alloc_crash_proof indirect_inode_proof.
From Perennial.goose_lang.lib Require Import lock.crash_lock.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import typed_slice.
From Perennial.Helpers Require Import List.
From Perennial.program_proof Require Import marshal_block disk_lib.

Hint Unfold inode.wf MaxBlocks indirectNumBlocks maxDirect maxIndirect: word.
Hint Unfold inode.wf MaxBlocks indirectNumBlocks maxDirect maxIndirect: auto.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Remove Hints fractional.into_sep_fractional : typeclass_instances.

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
  iNamed "Hvolatile"; iNamed "Hdurable"; iNamed "Hfacts"; iNamed "Hhdr"; iNamed "Hdata".
  iIntros "HΦ".

  (* A bunch of facts and prep stuff *)
  unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
  destruct Hlen as [HdirLen [HindirLen HszMax]].
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
    rewrite H; simpl.
    iExists direct_s', indirect_s,
    (impl_s.mk
       b'
       ds.(impl_s.numInd)
       (take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs)
                                            ++ [a]
                                            ++ (drop (length σ'.(inode.blocks)) ds.(impl_s.dirAddrs)))
       ds.(impl_s.indAddrs)
       ds.(impl_s.indBlkAddrsList)).
    unfold is_inode_durable_with.
    rewrite H; simpl.
    rewrite Min.min_l in HdirAddrs; [ | word].

    assert ((length daddrs) = (length σ.(inode.blocks))%nat) as HdaddrsLen.
    {
      assert (length ds.(impl_s.dirAddrs) = length (daddrs ++ replicate (500 - length σ.(inode.blocks)) (U64 0))) as Hleneq.
      {
        rewrite HdirAddrs. auto.
      }
      rewrite app_length replicate_length in Hleneq. assert (length ds.(impl_s.dirAddrs) = 500%nat) by word.
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
      replace (length daddrs + 1)%nat with (length (daddrs ++ [(U64 0)])); last first.
      { len. }
      by rewrite drop_app.
    }

    (* prove the postcondition holds *)
    iFrame.
    unfold is_inode_durable_data.

    (* Handle "Hdurable" first *)
    iSplitR "Hdirect size".
    {
      (* Hfacts *)
      iSplitR.
      {
        unfold is_inode_durable_facts.

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
            assert ((length σ.(inode.blocks) + 1)%nat = length ((take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs) ++ [a]))) as Hlen.
            { rewrite app_length. rewrite take_length Min.min_l; simpl; word. }
            rewrite Hlen.
            rewrite (take_app (take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs) ++ [a])); auto.
          }
          assert (((take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs) ++ [a])
                    ++ take ds.(impl_s.numInd) ds.(impl_s.indAddrs)
                    ++ concat ds.(impl_s.indBlkAddrsList)
                    ≡ₚ
                    a :: (take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs)
                    ++ take ds.(impl_s.numInd) ds.(impl_s.indAddrs)
                   ++ concat ds.(impl_s.indBlkAddrsList))))
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
          assert (ds.(impl_s.numInd) = 0%nat) as H0 by word; rewrite HnumInd0 H0 in Hencoded'.
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

        (* Hlen *)
        iSplitR.
        { iPureIntro.
          unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
          rewrite HdirLen.
          repeat (split; auto); len; simpl; [ | rewrite app_length; simpl; word].
          rewrite -Hdaddrs HdirAddrs.
          len.
        }

        (* HnumInd *)
        {
          iPureIntro. rewrite HnumInd.
          unfold maxDirect, indirectNumBlocks in *.
          rewrite app_length; simpl. repeat rewrite max_l; word.
        }
      }

      (* Hencoded *)
      iSplitR.
      {
        iPureIntro.
        eapply block_encodes_eq; eauto.
        unfold maxDirect in *.
        rewrite !app_length.
        change (length [_]) with 1%nat.
        rewrite HdirAddrsEnd /maxIndirect.
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
        rewrite -!app_assoc.
        replace (U64 (Z.of_nat (length σ.(inode.blocks)) + 1)) with
            (U64 (Z.of_nat (length σ.(inode.blocks) + 1%nat))) by word.
        repeat f_equal.
        - rewrite take_app_le //; len.
          rewrite take_ge //; len.
        - len.
      }

        (* Hdirect *)
        iSplitL "HdataDirect Ha".
        {
          rewrite /maxDirect -Hdaddrs.
          assert ((int.nat (U64 500) `min` length σ.(inode.blocks))%nat =
                  (length σ.(inode.blocks))) by word.
          assert ((int.nat (U64 500) `min` length (σ.(inode.blocks) ++ [b]))%nat =
                  (length (σ.(inode.blocks) ++ [b]))%nat) as tmp by (len; simpl; word).
          rewrite tmp.
          assert (length (daddrs ++ [a]) = length (σ.(inode.blocks) ++ [b])) as tmp2 by (len; simpl; word).
          replace (daddrs ++ a :: drop (length (σ.(inode.blocks) ++ [b])) ds.(impl_s.dirAddrs)) with
              ((daddrs ++ [a]) ++ drop (length (σ.(inode.blocks) ++ [b])) ds.(impl_s.dirAddrs))
          by (rewrite -app_assoc -cons_middle; auto).
          rewrite -tmp2 take_app. rewrite tmp2 firstn_all.
          iApply (big_sepL2_app with "[HdataDirect]"); simpl; auto.
          { rewrite Min.min_r; [ | word].
            rewrite -HdaddrsLen HdirAddrs take_app. rewrite HdaddrsLen firstn_all. auto.
          }
        }

      (* Hindirect *)
      {
        assert (ds.(impl_s.numInd) = 0%nat) as tmp by word; rewrite tmp.
        rewrite take_0.
        repeat rewrite big_sepL2_nil; auto.
      }
    }
    (* Greater than maxDirect already, return false *)
    {
      iSplitL "size".
      (* size *)
      + len. simpl.
        assert ((Z.of_nat (length σ.(inode.blocks)) + 1) = Z.of_nat (length σ.(inode.blocks) + 1)) as tmp by word.
        rewrite tmp.
        auto.
      (* Hdirect *)
      + rewrite -Hdaddrs.
        assert (length (daddrs ++ [a]) = length (σ.(inode.blocks) ++ [b])) as tmp by (len; simpl; word).
        replace (daddrs ++ a :: drop (length (σ.(inode.blocks) ++ [b])) ds.(impl_s.dirAddrs)) with
            ((daddrs ++ [a]) ++ drop (length (σ.(inode.blocks) ++ [b])) ds.(impl_s.dirAddrs))
        by (rewrite -app_assoc -cons_middle; auto).
        rewrite -tmp take_app; auto.
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

Theorem wp_writeIndirect {l σ d lref} (addr: u64) ds direct_s indirect_s
        (indA: u64) (indBlkAddrs: list u64) (indBlock: Block)
        (index: nat) (offset : nat) (a: u64) (b: Block) indblkaddrs_s :
  {{{
       (* parts of necessary inode_linv *)
       "Hvolatile" ∷ is_inode_volatile_with l σ addr direct_s indirect_s ds ∗
       "Hfacts" ∷ is_inode_durable_facts σ addr ds ∗
       "Hhdr" ∷ is_inode_durable_hdr σ addr ds ∗

       (* we only need one fact here, not entire list/Hdata from inode_linv *)
       "HindirectData" ∷ is_indirect indA indBlkAddrs indBlock (ind_blocks_at_index σ index) ∗

       (* Specific to writeIndirect *)
       "%Hsize" ∷ ⌜length σ.(inode.blocks) >= maxDirect ∧ length σ.(inode.blocks) < MaxBlocks ∧
        (*there is still room in the last indirect block*)
       (length σ.(inode.blocks) - maxDirect) `div` indirectNumBlocks < ds.(impl_s.numInd)⌝ ∗
       "%Hindex" ∷ ⌜
        Z.of_nat index = (length σ.(inode.blocks) - maxDirect) `div` indirectNumBlocks ∧
        (*index is the last existing block*)
        ind_blocks_at_index σ index = (drop (int.nat maxDirect + index * int.nat indirectNumBlocks) σ.(inode.blocks))
       ⌝ ∗
       "%Hlookup" ∷ ⌜(take ds.(impl_s.numInd) ds.(impl_s.indAddrs)) !! index = Some indA
                  ∧ ds.(impl_s.indBlkAddrsList) !! index = Some indBlkAddrs⌝ ∗
       "%Hlen" ∷ ⌜length indBlkAddrs < int.nat indirectNumBlocks⌝ ∗
       "Hro_state" ∷ inode_state l d lref ∗
       "Ha" ∷ int.val a d↦ b ∗
       "Haddr_s" ∷ is_slice indblkaddrs_s uint64T 1
       (indBlkAddrs ++ [a] ++ replicate (int.nat indirectNumBlocks - (length (indBlkAddrs) + 1)) (U64 0))
  }}}
  Inode__writeIndirect #l #indA (slice_val indblkaddrs_s)
  {{{ RET #();
      ∃ hdr, ∀ σ' ds',
         ((⌜σ' = set inode.blocks (λ bs, bs ++ [b])
                  (set inode.addrs ({[a]} ∪.) σ) ∧
           ds' = set impl_s.indBlkAddrsList
            (λ ls, <[index := (indBlkAddrs ++ [a])]> ls)
                      (set impl_s.hdr (λ _, hdr) ds)⌝)
        -∗ (
       "Hvolatile" ∷ is_inode_volatile_with l σ' addr direct_s indirect_s ds' ∗
       "Hhdr" ∷ is_inode_durable_hdr σ' addr ds') ∗
       "HindirectData" ∷ ∃ indBlock', is_indirect indA (indBlkAddrs ++ [a]) indBlock' (ind_blocks_at_index σ' index)
    )
  }}}.
Proof.
  iIntros (Φ) "Hpre". iNamed "Hpre".
  iIntros "HΦ".

  (* A bunch of facts and prep stuff. Factor this out!!! *)
  iNamed "Hro_state"; iNamed "Hvolatile"; iNamed "Hfacts"; iNamed "Hhdr".

  unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
  destruct Hlen0 as [HdirLen [HindirLen HnumIndBlocks]].
  destruct Hsize as [HsizeMin [HsizeMax HstillRoom]].
  destruct Hindex as [Hindex HindexLastBlock].
  destruct Hlookup as [HlookupIndA HlookupIndBlkAddrs].
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

  assert (Z.to_nat (4096 - 8 * length (indBlkAddrs ++ [a] ++ replicate (int.nat indirectNumBlocks - (length indBlkAddrs + 1)) (U64 0)))
          = 0%nat) as Hrem0.
  {
    repeat rewrite app_length /indirectNumBlocks. rewrite replicate_length. simpl. word.
  }

  wp_call.
  (*PrepIndirect*)
  wp_call.
  wp_apply wp_new_enc.
  iIntros (enc) "Henc".
  wp_let.
  iDestruct (is_slice_split with "Haddr_s") as "[Haddr_s_small Haddr_s]".
  wp_apply (wp_Enc__PutInts with "[$Henc $Haddr_s_small]").
    { len. }
    rewrite app_nil_l.

    iIntros "[Henc Haddr_s_small]".
    iDestruct (is_slice_split with "[$Haddr_s_small $Haddr_s]") as "Haddr_s".
    wp_pures.
    wp_apply (wp_Enc__Finish with "Henc").
    iIntros (s b') "[%Hencoded' Hs]".
    wp_pures.
    iNamed "HindirectData".
    wp_apply (wp_Write _ _ indA s 1
            _ with "[Hs diskAddr]").
    {
      iExists indBlock; iFrame.
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
    iExists hdr.
    iIntros (σ' ds').

    (*Prove postcondition holds*)
    iIntros "[%Hσ' %Hds']".
    rewrite Hσ' Hds'.
    iFrame.
    iSplitL "size Hdirect".
    {
      iSplitL.
      {
        rewrite app_length; simpl.
        replace (U64 (Z.of_nat (length σ.(inode.blocks) + 1))) with (U64 ((Z.of_nat (length σ.(inode.blocks))) + 1)) by word.
        repeat rewrite take_ge; try word.
        iFrame.
      }

      (*Hencoded*)
      {
        iPureIntro.
        eapply block_encodes_eq; eauto.
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
        rewrite app_length.
        change (length [b]) with 1%nat.
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
    }

    (* HindirectData *)
    iExists b'.
    iFrame; auto.
    iSplitR; iFrame; auto.
    {
      iPureIntro.
      len; simpl; word.
    }
    (*Hencoded indBlk*)
    iSplitR; [iPureIntro; simpl; auto|].
    {
      eapply block_encodes_eq; eauto.
      rewrite !fmap_app app_assoc /indirectNumBlocks app_length; simpl.
      f_equal.
    }
    (*Hlen indBlk*)
    iSplitR; [iPureIntro; len; simpl; auto|].
    {
      unfold ind_blocks_at_index in *. len.
      simpl.
      rewrite subslice_to_end in Hlen0; [|unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *; word].
      rewrite drop_length in Hlen0.
      rewrite subslice_to_end; unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
      + len. simpl. rewrite Hlen0.
        replace (Z.of_nat (int.nat (U64 500))) with 500 by word.
        replace (Z.of_nat (int.nat (U64 512))) with 512 by word.
        replace (int.nat (U64 (500 + Z.of_nat ds.(impl_s.numInd) * 512)))
          with (500 + ds.(impl_s.numInd) * 512)%nat by word.
        word.
      + len.
    }
    {
      unfold ind_blocks_at_index; simpl.
      repeat rewrite subslice_to_end; unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
      + replace (drop (int.nat (500 + index * 512)) (σ.(inode.blocks) ++ [b])) with
            ((drop (int.nat (500 + index * 512)) σ.(inode.blocks)) ++ [b]).
        -- iApply (big_sepL2_app with "Hdata"). simpl. eauto.
        -- rewrite drop_app_le; [auto|word].
      + len.
      + word.
    }
Qed.

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
        ∃ hdr,
        (∀ σ' ds' index offset indBlkAddrs,
            (⌜σ' = set inode.blocks (λ bs, bs ++ [b]) (set inode.addrs ({[a]} ∪.) σ) ∧
            index = (length σ.(inode.blocks) - maxDirect) `div` indirectNumBlocks ∧
            offset = (length σ.(inode.blocks) - maxDirect) `mod` indirectNumBlocks ∧
            ds.(impl_s.indBlkAddrsList) !! (int.nat index) = Some indBlkAddrs⌝ ∗
            ⌜ds' = set impl_s.indBlkAddrsList
                              (λ ls, <[int.nat index:= (indBlkAddrs ++ [a])]> ls)
                              (set impl_s.hdr (λ _, hdr) ds)⌝)
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
  iNamed "Hdurable"; iNamed "Hvolatile"; iNamed "Hfacts"; iNamed "Hhdr"; iNamed "Hdata".
  unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
  destruct Hlen as [HdirLen [HindirLen HszMax]].
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
    rewrite -Hiaddrs in HlenInd.
    assert (Z.of_nat (length iaddrs) = int.val indirect_s.(Slice.sz)) by word.
    rewrite -H -HiaddrsLen.
    rewrite HnumInd /roundUpDiv; word.
  }

  (*Fits! Don't need to allocate another block, phew*)
  {
    wp_loadField.
    wp_apply (wp_indNum); [iPureIntro; by len|].
    iIntros (index) "%Hindex".

    assert (indNum = index) as HindNumIndex by word.

    (* Here are a bunch of facts *)
    (* TODO these are replicated from READ *)
    assert (int.val index < ds.(impl_s.numInd)) as HindexMax. {
      rewrite take_length Min.min_l in HlenInd; word.
    }
    destruct (list_lookup_lt _ (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs)) (int.nat index)) as [indA Hlookup].
    {
      unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *. rewrite firstn_length.
      rewrite Min.min_l; word.
    }
    assert (int.nat index < 10) as HindexMax10.
    {
      pose proof (lookup_lt_Some (take ds.(impl_s.numInd) ds.(impl_s.indAddrs)) _ indA Hlookup) as tmp.
      rewrite take_length in tmp.
      word.
    }

    wp_loadField.
    iDestruct (is_slice_split with "Hindirect") as "[Hindirect_small Hindirect]".
    wp_apply (wp_SliceGet _ _ _ _ 1 (take (ds.(impl_s.numInd)) ds.(impl_s.indAddrs)) _ indA with "[Hindirect_small]"); iFrame; auto.

    iIntros "Hindirect_small".
    iDestruct (is_slice_split with "[$Hindirect_small $Hindirect]") as "Hindirect".
    assert (take ds.(impl_s.numInd) ds.(impl_s.indAddrs) =
                ((take (int.nat index) (take ds.(impl_s.numInd) ds.(impl_s.indAddrs)))
                                     ++ indA ::
                                     (drop (S (int.nat index)) (take ds.(impl_s.numInd) ds.(impl_s.indAddrs)))))
      as HsplitIndA by (rewrite take_drop_middle; auto).
    iDestruct "HdataIndirect" as (indBlocks) "[%HindBlocksLen HdataIndirect]".
    assert (∃ indBlock, indBlocks !! int.nat index = Some indBlock) as [indBlk HlookupIndBlock].
    {
      apply lookup_lt_is_Some_2.
      rewrite HindBlocksLen.
      apply (lookup_lt_Some _ _ _ Hlookup).
    }
    assert (indBlocks =
                ((take (int.nat index) indBlocks)
                   ++ indBlk :: (drop (S (int.nat index)) indBlocks)))
           as HsplitIndBlk by (rewrite take_drop_middle; auto).
    iEval (rewrite HsplitIndA) in "HdataIndirect".
    rewrite HsplitIndBlk.
    iApply big_sepL2_app_inv in "HdataIndirect".
    {
      repeat rewrite take_length.
      rewrite min_l; len.
    }
    change (indA :: (drop (S (int.nat index)) (take ds.(impl_s.numInd) ds.(impl_s.indAddrs))))
      with ([indA] ++ (drop (S (int.nat index)) (take ds.(impl_s.numInd) ds.(impl_s.indAddrs)))).
    change (indBlk :: (drop (S (int.nat index)) indBlocks)) with ([indBlk] ++ (drop (S (int.nat index)) indBlocks)).
    iDestruct "HdataIndirect" as "[HdataIndirectFront HdataIndirectBack]".
    iApply big_sepL2_app_inv in "HdataIndirectBack"; simpl; auto.
    iDestruct "HdataIndirectBack" as "[[Hb _] HdataIndirectBack]".
    replace (take (int.nat index) (take ds.(impl_s.numInd) ds.(impl_s.indAddrs)))
      with (take (int.nat index) ds.(impl_s.indAddrs)) by (rewrite take_take min_l; [auto|word]).
    iEval (rewrite -plus_n_O) in "Hb".
    replace (length (take (int.nat index) ds.(impl_s.indAddrs))) with (int.nat index).
    2: {
      rewrite take_length min_l; auto; word.
    }

    wp_pures.
    wp_loadField.
    iDestruct "Hb" as (indBlkAddrs) "[%HaddrLookup HaddrIndirect]".
    wp_apply (wp_readIndirect ds indirect_s indBlk indBlkAddrs (int.nat index) d indA
                with "[indirect HaddrIndirect]").
    {
      iFrame. repeat iSplit; eauto. iPureIntro; len.
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

    assert ((length σ.(inode.blocks) - maxDirect) `div` indirectNumBlocks < ds.(impl_s.numInd)) as HstillSpace.
    {
      unfold maxDirect, indirectNumBlocks in *.
      rewrite HindNum in Heqb0.
      pose (Znot_le_gt _ _ Heqb0) as HindNumGt.
      replace (int.val (length σ.(inode.blocks))) with (Z.of_nat (length σ.(inode.blocks))) in * by word.
      word.
    }
    assert (ind_blocks_at_index σ (int.nat index) = drop (int.nat maxDirect + int.nat index * int.nat indirectNumBlocks) σ.(inode.blocks))
      as HindBlksAtIndex.
    {
        unfold ind_blocks_at_index; rewrite subslice_to_end;
        unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
        + by replace (int.nat (U64 500) + int.nat index * int.nat (U64 512))%nat
            with (int.nat (U64 (500 + Z.of_nat (int.nat index) * 512))) by word.
        + rewrite Hindex. word.
    }

    wp_apply (wp_writeIndirect addr ds direct_s indirect_s indA indBlkAddrs indBlk
                (int.nat index) (int.nat offset) a b indblkaddrs_s
              with "[-HΦ HdataDirect HdataIndirectFront HdataIndirectBack]").
    {
      unfold inode_state.
      iFrame; eauto.
      iSplitR; [iPureIntro; repeat split; simpl; eauto|].
      iSplitR; [iPureIntro; eauto|].
      iSplitR; [iPureIntro; repeat split; eauto|].
      iSplitR; [iPureIntro; repeat split; eauto|].
      iSplitR; [iPureIntro; repeat split; eauto|].
      (* Index facts *)
      {
        unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
        replace (int.val (U64 (Z.of_nat (length σ.(inode.blocks)))) - 500)
          with (Z.of_nat (length σ.(inode.blocks)) - 500) in Hindex by word.
        word.
      }

      iSplitR; eauto.
      (* Hlen *)
      iSplitR.
      { iPureIntro.
        rewrite Hlen HindBlksAtIndex drop_length.
        unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
        replace (int.nat (U64 500) + int.nat index * int.nat (U64 512))%nat
          with (Z.to_nat (500 + int.val index * 512)) by word.
        replace (Z.of_nat (int.nat (U64 512))) with 512 by word.
        rewrite Hindex.
        replace (int.val (U64 (Z.of_nat (length σ.(inode.blocks))))) with (Z.of_nat (length σ.(inode.blocks))) by word.
        word.
      }

      iSplitR; eauto.

      (* is_slice indBlkAddrs *)
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
    }

    iIntros "H".
    wp_pures.
    iApply ("HΦ"); eauto.
    iDestruct "H" as (hdr) "H".
    iExists hdr.
    iIntros (σ' ds' index0 offset0 indBlkAddrs0) "[%H %Hds']".
    destruct H as [Hσ' [Hindex0 [Hoffset0 HindBlkAddrs0]]].
    rewrite /maxDirect /indirectNumBlocks in Hindex, Hoffset.
    assert (int.nat index = int.nat index0) as tmp1.
    {
      replace ((int.val (length σ.(inode.blocks)) - 500) `div` 512) with ((length σ.(inode.blocks) - 500) `div` 512) in Hindex by word.
      rewrite -Hindex in Hindex0. word.
    }
    assert (int.nat offset = int.nat offset0) as tmp2.
    {
      replace ((int.val (length σ.(inode.blocks)) - 500) `mod` 512) with ((length σ.(inode.blocks) - 500) `mod` 512) in Hoffset by word.
      rewrite -Hoffset in Hoffset0; word.
    }
    assert (indBlkAddrs0 = indBlkAddrs) as tmp3.
    {
      rewrite -tmp1 in HindBlkAddrs0. rewrite HaddrLookup in HindBlkAddrs0.
      inversion HindBlkAddrs0; auto.
    }
    assert (σ' = set inode.blocks (λ bs : list Block, bs ++ [b]) (set inode.addrs (union {[a]}) σ)
           ∧ ds' =
             set impl_s.indBlkAddrsList
               (λ ls : list (list u64), <[(int.nat index):=indBlkAddrs ++ [a]]> ls)
               (set impl_s.hdr (λ _ : Block, hdr) ds)) as Harg.
    {
      split; auto.
      replace (int.nat (int.nat index)) with (int.nat index) by word.
      rewrite tmp1 -tmp3; auto.
    }

    iSpecialize ("H" $! σ' ds' Harg).
    iDestruct "H" as "[[Hvolatile Hhdr] HindirectData]".
    repeat iNamed "Hvolatile".
    repeat iNamed "Hhdr".
    iFrame.
    rewrite Hσ' Hds'.

    unfold is_inode_durable_facts.
    iSplitR.
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
        rewrite -Haddrs_set.
        assert ((take (length σ.(inode.blocks)) ds.(impl_s.dirAddrs)) = ds.(impl_s.dirAddrs)
                ∧ (take (length σ.(inode.blocks) + 1) ds.(impl_s.dirAddrs)) = ds.(impl_s.dirAddrs)) as [Htake HtakeP1].
        {
          repeat rewrite take_ge ; auto; lia.
        }
        rewrite Htake HtakeP1.
        rewrite [a in _ = a]union_comm_L.
        repeat rewrite list_to_set_app_L.
        repeat rewrite -union_assoc_L.
        repeat f_equiv.
        assert (int.val index < length (ds.(impl_s.indBlkAddrsList))) as HindexExists.
        {
          pose proof (lookup_lt_Some ds.(impl_s.indBlkAddrsList) (int.nat index) _ HaddrLookup).
          word.
        }
        rewrite -[a in _ = list_to_set (concat a) ∪ _](list_insert_id _ (int.nat index) indBlkAddrs); auto.
        rewrite concat_insert_app; rewrite -tmp1; [|word].
        rewrite [a in _ = list_to_set a ∪ _]concat_insert_app; [|word].
        repeat rewrite list_to_set_app_L.
        repeat rewrite -union_assoc_L.
        rewrite tmp3.
        f_equiv.
        f_equiv.
        rewrite union_empty_l_L union_comm_L.
        f_equiv.
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

      (* Hlen *)
      iSplitR.
      { iPureIntro.
        unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
        repeat (split; auto); len; simpl; try word.
        len.
      }

      (* HnumInd *)
      {
        iPureIntro. rewrite HnumInd.
        unfold roundUpDiv, maxDirect, indirectNumBlocks in *.
        rewrite app_length; simpl.
        repeat rewrite max_r; try word.
      }
    }

    (* Hencoded *)
    iSplitR.
    {
      iPureIntro.
      rewrite Hds' Hσ' in Hencoded1.
      change ((set impl_s.indBlkAddrsList _
                    (set impl_s.hdr (λ _ : Block, hdr) ds)).(impl_s.hdr)) with
          hdr in *.
      change ((set impl_s.indBlkAddrsList _
                    (set impl_s.hdr (λ _ : Block, hdr) ds)).(impl_s.dirAddrs)) with
          ds.(impl_s.dirAddrs) in *.
      change ((set impl_s.indBlkAddrsList _
                    (set impl_s.hdr (λ _ : Block, hdr) ds)).(impl_s.numInd)) with
          ds.(impl_s.numInd) in *.
      change ((set impl_s.indBlkAddrsList _
                    (set impl_s.hdr (λ _ : Block, hdr) ds)).(impl_s.indAddrs)) with
          ds.(impl_s.indAddrs) in *.
      change ((set inode.blocks (λ bs : list Block, bs ++ [b]) (set inode.addrs (union {[a]}) σ)).(inode.blocks))
        with (σ.(inode.blocks) ++ [b]) in *.
      auto.
    }

    (* Hdirect *)
    iSplitL "HdataDirect".
    {
      simpl. rewrite /maxDirect.
      repeat rewrite min_l.
      + assert (take (int.nat 500) σ.(inode.blocks) = take (int.nat 500) (σ.(inode.blocks) ++ [b])) as tmp.
        { rewrite take_app_le; auto; word. }
          by rewrite tmp .
      + rewrite app_length; simpl. word.
      + simpl. word.
    }

    (* Hindirect *)
    {
      simpl.
      iDestruct "HindirectData" as (indBlk') "HindirectData".
      iNamed "HindirectData".
      rewrite HsplitIndA.
      iEval (rewrite -HsplitIndA) in "HdataIndirectBack".
      iExists ((take (int.nat index) indBlocks) ++ indBlk' :: (drop (S (int.nat index)) indBlocks)).

      iSplitR; [iPureIntro; len|].
      + rewrite HindBlocksLen; repeat rewrite min_l; try word.
        -- rewrite take_length. rewrite min_l; auto. word.
      + iApply (big_sepL2_app with "[HdataIndirectFront]").
        -- rewrite -tmp1.
           rewrite take_take min_l; [|word].
           unfold ind_blocks_at_index; simpl.
           iApply (big_sepL2_mono with "HdataIndirectFront").
           iIntros (k y1 y2 HlookupY1 HlookupY2) "H".
           assert (k < int.nat index)%nat as HkBound.
           {
             replace (int.nat index) with (length (take (int.nat index) indBlocks)).
             + eapply (lookup_lt_Some (take (int.nat index) indBlocks) _ y2 HlookupY2).
             + rewrite take_length min_l; auto. word.
           }
           iDestruct "H" as (indBlkAddrs') "[%HlookupIndBlkAddrs' H]".
           iExists indBlkAddrs'.
           iSplitR; [iPureIntro; auto|].
           ++ assert ((take (int.nat index) ds.(impl_s.indBlkAddrsList)) !! k = Some indBlkAddrs') as H by
                   (rewrite lookup_take; auto).
              rewrite -(lookup_take (<[int.nat index := indBlkAddrs0 ++ [a]]> ds.(impl_s.indBlkAddrsList)) (int.nat index) k); [|word].
              rewrite take_insert; auto.
           ++ replace (subslice (int.nat (maxDirect + k * indirectNumBlocks))
                               (int.nat (maxDirect + k * indirectNumBlocks) + int.nat indirectNumBlocks)
                               (σ.(inode.blocks) ++ [b]))
                     with (subslice (int.nat (maxDirect + k * indirectNumBlocks))
                               (int.nat (maxDirect + k * indirectNumBlocks) + int.nat indirectNumBlocks)
                               (σ.(inode.blocks))); auto.
              eapply subslice_before_app_eq.
              unfold maxDirect, indirectNumBlocks.
              replace (int.nat (U64 (500 + Z.of_nat k * 512)) + int.nat (U64 512))%nat with
                  (500 + k * 512 + 512)%nat by word.
              assert (500 + Z.of_nat k * 512 + 512 ≤ Z.of_nat (length σ.(inode.blocks))) as tmp.
              {
                eapply (Z.le_trans (500 + k * 512 + 512) (500 + (int.val index -1) * 512 + 512) (length σ.(inode.blocks))); [word|].
                rewrite Hindex.
                replace (int.val (U64 (Z.of_nat (length σ.(inode.blocks))))) with (Z.of_nat (length σ.(inode.blocks))) by word.
                lia.
              }
              word.
        -- change (indA :: (drop (S (int.nat index)) (take ds.(impl_s.numInd) ds.(impl_s.indAddrs))))
               with ([indA] ++ (drop (S (int.nat index)) (take ds.(impl_s.numInd) ds.(impl_s.indAddrs)))).
           change (indBlk' :: (drop (S (int.nat index)) indBlocks)) with ([indBlk'] ++ (drop (S (int.nat index)) indBlocks)).

           iApply (big_sepL2_app with "[diskAddr Hdata]");
           replace (length (take (int.nat index) (take ds.(impl_s.numInd) ds.(impl_s.indAddrs))))
             with (int.nat index) by
               (rewrite take_length;
                rewrite min_l; [auto|word]).
           {
             rewrite big_sepL2_singleton.
             iExists (indBlkAddrs ++ [a]).
             iSplitR; simpl.
             + iPureIntro. rewrite -plus_n_O. rewrite -tmp1 tmp3.
               apply (list_lookup_insert (ds.(impl_s.indBlkAddrsList)) (int.nat index) (indBlkAddrs ++ [a])).
               apply lookup_lt_is_Some. eauto.
             + iFrame.
               rewrite -plus_n_O; auto.
           }
           (* Hdata *)
           rewrite -tmp1; simpl.
           rewrite -HindNumIndex.
           assert (int.val indNum + 1 = ds.(impl_s.numInd)) as HindNumSucc.
           {
             rewrite HindNum. rewrite HnumInd.
             rewrite max_r; [|word].
             rewrite -roundUpDiv_lt_succ; try word.
             unfold indirectNumBlocks, maxIndirect, maxDirect, roundUpDiv in *.
             lia.
           }
           repeat rewrite drop_ge.
           { by iApply big_sepL2_nil. }
           { rewrite HindBlocksLen take_length min_l; lia. }
           { rewrite take_length min_l; lia. }
    }
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

