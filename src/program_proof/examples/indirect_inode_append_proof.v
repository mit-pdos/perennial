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
  unfold MaxBlocks, maxDirect, maxIndirect, indirectNumBlocks in *.
  iIntros "HΦ".
  wp_call.
  wp_loadField.
  wp_if_destruct.
  (* Fits within maxDirect *)
  {
    destruct Hlen as [HdirLen [HindirLen [HszMax [HnumInd1 [HnumInd2 HnumIndBlocks]]]]].
    iDestruct (is_slice_sz with "Hdirect") as %HlenDir.
    replace (int.val (U64 (Z.of_nat (length σ.(inode.blocks))))) with (Z.of_nat (length σ.(inode.blocks))) in Heqb0 by word.
    assert (length (σ.(inode.blocks)) <= 500) as Hsz by word.
    pose (HnumInd2 Hsz) as HnumInd.

    wp_loadField.
    wp_apply (wp_SliceAppend (V:=u64) with "[$Hdirect]").
    {
      iPureIntro.
      rewrite /list.untype fmap_take /fmap_length in HlenDir.
      rewrite take_length Min.min_l in HlenDir; try word.
      rewrite fmap_length. word.
    }
    iIntros (direct_s') "Hdirect".
    Transparent slice.T.
    wp_storeField.
    wp_loadField.
    wp_storeField.
    Check wp_Inode__mkHdr.
    wp_apply (wp_Inode__mkHdr l
      (length σ.(inode.blocks) + 1)
      numInd
      (take (length σ.(inode.blocks)) dirAddrs ++ [a])
      (take numInd indAddrs)
      direct_s' indirect_s with "[direct indirect size Hdirect Hindirect]").
    {
      rewrite /MaxBlocks /maxDirect /maxIndirect /indirectNumBlocks.
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
    { iExists hdr; iFrame. }

    iIntros "[Hhdr Hb]".
    wp_pures.
    iApply "HΦ".
    iIntros.
    iFrame.
    iSplitR; auto.
    rewrite a0; simpl.
    iExists b', direct_s', indirect_s,
    numInd, (take (length σ.(inode.blocks)) dirAddrs ++ [a] ++ (drop (length σ'.(inode.blocks)) dirAddrs)),
    indAddrs, indBlkAddrsList, indBlocks.

    unfold is_inode_durable_with.
    rewrite a0.
    change ((set inode.blocks
              (λ bs : list Block, bs ++ [b])
              (set inode.addrs (union {[a]}) σ))
                .(inode.blocks)) with (σ.(inode.blocks) ++ [b]) in *.
    destruct HdirAddrs as [daddrs HdirAddrs].
    destruct HindAddrs as [iaddrs HindAddrs].
    assert (numInd = length iaddrs) as HiaddrsLen.
    {
      rewrite HindAddrs in HindirLen.
      rewrite app_length replicate_length in HindirLen.
      word.
    }
    assert (iaddrs = take (numInd) indAddrs) as Hiaddrs.
    {
      rewrite HiaddrsLen HindAddrs. rewrite take_app; auto.
    }
    rewrite Min.min_l in HdirAddrs; try word.

    assert ((length daddrs) = (length σ.(inode.blocks))%nat) as HdaddrsLen.
    {
      assert (length dirAddrs = length (daddrs ++ replicate (500 - length σ.(inode.blocks)) (U64 0))).
      {
        rewrite HdirAddrs. auto.
      }
      rewrite app_length replicate_length in H. assert (length dirAddrs = 500%nat) by word. rewrite H0 in H.
      word.
    }

    assert (daddrs = take (length σ.(inode.blocks)) dirAddrs) as Hdaddrs.
    {
      rewrite HdirAddrs. rewrite -HdaddrsLen.
      rewrite take_app. auto.
    }

    assert (drop (length σ.(inode.blocks) + 1) dirAddrs = replicate (500%nat - (length σ.(inode.blocks) + 1)) (U64 0)) as HdirAddrsEnd.
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
                      (take (length σ.(inode.blocks)) dirAddrs ++ [a]
                            ++ drop ((length σ.(inode.blocks) + 1)) dirAddrs))
          with (take (length σ.(inode.blocks)) dirAddrs ++ [a]).
        2: {
          rewrite app_assoc.
          assert ((length σ.(inode.blocks) + 1)%nat = length ((take (length σ.(inode.blocks)) dirAddrs ++ [a]))) as H.
          { rewrite app_length. rewrite take_length Min.min_l; simpl; word. }
          rewrite H.
          rewrite (take_app (take (length σ.(inode.blocks)) dirAddrs ++ [a])); auto.
        }
        assert (((take (length σ.(inode.blocks)) dirAddrs ++ [a])
                   ++ take numInd indAddrs
                   ++ foldl (λ acc ls : list u64, acc ++ ls) [] indBlkAddrsList)
                  ≡ₚ
                  a :: (take (length σ.(inode.blocks)) dirAddrs
                   ++ take numInd indAddrs
                   ++ foldl (λ acc ls : list u64, acc ++ ls) [] indBlkAddrsList))
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
        rewrite (HnumInd2 Hsz) in Hencoded'.
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
        replace (int.nat (U64 (10 - Z.of_nat numInd))) with ((int.nat (U64 10) - numInd)%nat) by word.
        rewrite HindAddrs.
        replace
          (int.nat (U64 (500 - Z.of_nat (length (take (length σ.(inode.blocks)) dirAddrs) + 1)))%nat)
          with ((500 - (length σ.(inode.blocks) + 1))%nat); auto.
        2: {
          rewrite take_length. rewrite Min.min_l; word.
        }
        replace
          (EncUInt64 <$> iaddrs ++ replicate (int.nat (U64 10) - numInd) (U64 0))
          with ((EncUInt64 <$> iaddrs) ++ (EncUInt64 <$> replicate (int.nat (U64 10) - numInd) (U64 0)));
        [ | by rewrite fmap_app].
        replace
        (EncUInt64 <$> (take (length σ.(inode.blocks)) dirAddrs ++ [a] ++
                             (replicate (500 - (length σ.(inode.blocks) + 1)) (U64 0))))
          with ((EncUInt64 <$> take (length σ.(inode.blocks)) dirAddrs ++ [a])
                     ++ (EncUInt64 <$> replicate (500 - (length σ.(inode.blocks) + 1)) (U64 0))).
        2: { rewrite app_assoc -fmap_app. auto. }
        repeat rewrite app_assoc.
        replace (U64 (Z.of_nat (length σ.(inode.blocks)) + 1)) with
            (U64 (Z.of_nat (length σ.(inode.blocks) + 1%nat))) by word.
        reflexivity.
      }

      (* Hlen *)
      iSplitR.
      { iPureIntro. repeat (split; auto); len; simpl; word. }

      (* Hdirect *)
      iSplitL "HdataDirect Ha".
      {
        rewrite app_assoc /maxDirect.
        assert ((int.nat (U64 500) `min` length σ.(inode.blocks))%nat =
                (length σ.(inode.blocks))) by word.
        assert ((int.nat (U64 500) `min` length (σ.(inode.blocks) ++ [b]))%nat =
                 (length (σ.(inode.blocks) ++ [b]))%nat) by (len; simpl; word).
        rewrite H0.
        assert (length (daddrs ++ [a]) = length (σ.(inode.blocks) ++ [b])) by (len; simpl; word).
        rewrite H HdirAddrs -HdaddrsLen take_app firstn_all -H1 take_app.
        iApply (big_sepL2_app with "[HdataDirect]"); simpl; auto.
        { rewrite HdaddrsLen. rewrite firstn_all. auto. }
      }

      (* Hindirect *)
      {
        rewrite HnumInd.
        rewrite take_0.
        symmetry in HnumIndBlocks.
        rewrite HnumInd in HnumIndBlocks.
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
      + rewrite app_assoc.
        assert (length (take (length σ.(inode.blocks)) dirAddrs ++ [a]) = length (σ.(inode.blocks) ++ [b])) by (len; simpl; word).
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

Theorem wp_writeIndirect {l σ addr} (indA a: u64) (indBlk b: Block) (addrs : list u64) addr_s:
  {{{
       "%Hsize" ∷ ⌜length σ.(inode.blocks) >= maxDirect⌝ ∗
       "%Haddrs" ∷ ⌜∃ ls, addrs = ls ++ [a]⌝ ∗
       "Haddr_s" ∷ is_slice addr_s uint64T 1 addrs ∗
       "Ha" ∷ int.val a d↦ b ∗
       "HindA" ∷ int.val indA d↦ indBlk ∗
       "Hinv" ∷ inode_linv l σ addr
  }}}
  Inode__writeIndirect #l #a (slice_val addr_s)
  {{{ RET #();
      ∀ σ',
        ⌜σ' = set inode.blocks (λ bs, bs ++ [b]) (set inode.addrs ({[a]} ∪.) σ)⌝ -∗
                  ("Hinv" ∷ inode_linv l σ' addr
                          ∗ "HIndA" ∷ int.val indA d↦ indBlk)
  }}}.
Proof.
Admitted.

Theorem wp_appendIndirect {l σ addr} (a: u64) b:
  {{{
    "%Hsize" ∷ ⌜length σ.(inode.blocks) >= maxDirect⌝ ∗
    "Hinv" ∷ inode_linv l σ addr ∗
    "Ha" ∷ int.val a d↦ b
  }}}
  Inode__appendDirect #l #a
  {{{ (ok: bool), RET #ok;
      if ok then
      (∀ σ',
          ⌜σ' = set inode.blocks (λ bs, bs ++ [b]) (set inode.addrs ({[a]} ∪.) σ)⌝ -∗
                  "Hinv" ∷ inode_linv l σ' addr  ∗
                  "Hsize" ∷ ∃ indirect_s,
                      l ↦[Inode.S :: "indirect"] (slice_val indirect_s) -∗
                        ⌜ (Z.add (((length σ.(inode.blocks)) - maxDirect) `div` indirectNumBlocks) 1) < int.val indirect_s.(Slice.sz) ⌝)
      else
        "Hinv" ∷ inode_linv l σ addr ∗
        "Ha" ∷ int.val a d↦ b ∗
        "Hsize" ∷  ∃ indirect_s,
          l ↦[Inode.S :: "indirect"] (slice_val indirect_s) -∗
            ⌜ (Z.add (((length σ.(inode.blocks)) - maxDirect) `div` indirectNumBlocks) 1) >= int.val indirect_s.(Slice.sz) ⌝
  }}}.
Proof.
Admitted.

Theorem wpc_Inode__Append {k E2}
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
