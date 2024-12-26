From Goose.github_com.session Require Import maxTS.
From Perennial.program_proof Require Import std_proof. 
From Perennial.goose_lang.ffi.grove_ffi Require Export impl.
From Perennial.program_logic Require Export atomic.
From Perennial.program_proof Require Export proof_prelude.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.goose_lang.lib Require Import struct.struct into_val.
From RecordUpdate Require Import RecordSet.
From Perennial.goose_lang Require Import prelude.

Local Lemma Z_scope_test : (0%Z) + (0%Z) = 0%Z.
Proof. done. Qed.

Section heap.
  
  Context `{hG: !heapGS Σ}.

  Definition coqMax (x: w64) (y: w64) :=
    if uint.Z x >? uint.Z y then x else y. 

  Fixpoint maxTSCoq (t1: list w64) (t2: list w64) : list w64 :=
    match t1 with
    | [] => []
    | cons hd1 tl1 => match t2 with
                      | [] => [] 
                      | cons hd2 tl2 => if (uint.Z hd1) >? (uint.Z hd2) then
                                          (cons hd1 (maxTSCoq tl1 tl2)) else (cons hd2 (maxTSCoq tl1 tl2))
                      end
    end.

  Lemma max_equiv (x: w64) (y: w64) :
    {{{
          True
    }}}
      maxTwoInts #x #y 
      {{{
            r , RET #r;
            ⌜r = coqMax x y⌝
      }}}.
  Proof.
    iIntros (Φ) "H H1".
    unfold maxTwoInts. wp_pures.
    wp_if_destruct.
    - iModIntro. iApply "H1". iPureIntro.
      unfold coqMax. apply Z.gtb_lt in Heqb.
      rewrite Heqb. auto.
    - iModIntro. iApply "H1". iPureIntro.
      unfold coqMax.
      assert (uint.Z y >= uint.Z x) by word.
      assert (uint.Z x >? uint.Z y = false) by word.
      rewrite H0.
      auto.
  Qed.

  Lemma getMaxTsEquiv (x: Slice.t) (xs: list w64) (y: Slice.t) (ys: list w64) :
    {{{
          own_slice x uint64T (DfracOwn 1) xs ∗
            own_slice y uint64T (DfracOwn 1) ys ∗
            ⌜length xs = length ys⌝ ∗ ⌜length xs < 2^64⌝
    }}}
      maxTS x y 
      {{{
            (s': Slice.t), RET slice_val s'; 
            own_slice s' uint64T (DfracOwn 1) (maxTSCoq xs ys) ∗ 
              own_slice x uint64T (DfracOwn 1) xs ∗
              own_slice y uint64T (DfracOwn 1) ys 
      }}}.
  Proof.
    iIntros (Φ) "(H & H1 & %H3 & %H4) H2".
    unfold maxTS.
    wp_pures. wp_apply wp_ref_to; auto.
    iIntros (index) "index". wp_pures.
    wp_pures. wp_apply wp_slice_len.
    wp_apply wp_ref_to; auto.
    iIntros (len) "len". wp_pures.
    wp_bind (NewSlice uint64T (slice.len x)).
    wp_apply wp_slice_len.
    wp_apply wp_new_slice; auto.
    iIntros (s') "s'". 
    wp_apply wp_ref_to; auto.
    iIntros (slice) "slice". wp_pures.
    Check own_slice.
    wp_apply (wp_forBreak_cond
                (λ continue, ∃ (i: w64) (l: list w64),
                    own_slice x uint64T (DfracOwn 1) xs ∗
                      own_slice y uint64T (DfracOwn 1) ys ∗
                      own_slice s' uint64T (DfracOwn 1) l ∗ 
                      index ↦[uint64T] #i ∗
                      len ↦[uint64T] #(length xs) ∗
                      slice ↦[slice.T uint64T] s' ∗ 
                      ⌜continue = false -> uint.nat i = (length xs)⌝ ∗ ⌜(length l) = (length xs)⌝ ∗
                                                                                       ⌜forall (i': nat),
                   i' < uint.nat i <= length xs ->
                   forall (x y: w64), xs !! i' = Some x ->
                                      ys !! i' = Some y ->
                                      l !! i' = Some (coqMax x y)⌝ ∗
                                                  ⌜uint.Z i <= (uint.Z (length xs))⌝ 
                )%I
               with "[] [H H1 index len s' slice]").
    - iIntros (?). iModIntro. iIntros "H1 H2".
      iNamed "H1". iDestruct "H1" as "(H1 & H3 & H4 & H5 & H6 & H7 & H8 & %H9 & %H10 & %H11)".
      wp_pures. wp_load. wp_load. wp_if_destruct.
      + wp_pures. wp_load.
        wp_bind (maxTwoInts _ _)%E.
        iDestruct (own_slice_sz with "H1") as %Hsz.
        iDestruct (own_slice_sz with "H4") as %Hsz2.
        iDestruct "H1" as "[Hx Hxc]".
        iDestruct "H3" as "[Hy Hyc]".
        iDestruct "H4" as "[Hs Hsc]".
        assert (uint.nat i < length xs)%nat by word. rewrite H3 in H. eapply list_lookup_lt in H. destruct H.
        assert (uint.nat i < length xs)%nat by word. eapply list_lookup_lt in H0. destruct H0.
        wp_apply (wp_SliceGet with "[$Hy]").
        * iPureIntro. apply H.
        * iIntros "Hy". wp_load. wp_apply (wp_SliceGet with "[$Hx]").
          -- iPureIntro. apply H0.
          -- iIntros "Hx".
             wp_apply (max_equiv). iIntros (r) "%H12".
             wp_load. wp_load.
             wp_apply (wp_SliceSet with "[$Hs]").
             ++ iFrame. iPureIntro.
                eapply lookup_lt_is_Some_2.
                word.
             ++ iIntros "H11". wp_pures. wp_load. wp_store. iModIntro.
                iApply "H2". iExists (w64_word_instance.(word.add) i (W64 1)).
                iExists (<[uint.nat i:=r]> l)%E. iFrame. iSplit.
                ** unfold own_slice_small. auto.
                ** iSplitR.
                   { iPureIntro. destruct H9. apply length_insert. }
                   { intros. iSplit; try word.
                     - iPureIntro. intros. destruct H9. (* there are two cases either i = i' or i = i *)
                       destruct (decide (i' = uint.nat i)).
                       + subst.
                         rewrite list_lookup_insert_Some.
                         left. split; auto.
                         split; try word.
                         rewrite H0 in H2.
                         rewrite H in H5.
                         injection H2 as ?.
                         injection H5 as ?.
                         subst.
                         auto.
                       + destruct H1.
                         rewrite Z.lt_le_pred in H1.
                         assert ((Z.pred (uint.nat (w64_word_instance.(word.add) i (W64 1)))) = uint.nat i) by word.
                         assert(uint.nat i ≠ i') by word.
                         apply (list_lookup_insert_ne l (uint.nat i) (i') r) in H8.
                         rewrite H8. 
                         eapply H10; try word; try auto.
                   }
      + iModIntro. iApply "H2". iExists i. iExists l. iFrame. iPureIntro. split.
        * intros. 
          word. 
        * auto. 
    - assert (zero_val uint64T = #(W64 0)). { unfold zero_val. simpl. auto. }
      rewrite H. iExists (W64 0).
      iExists (replicate (uint.nat x.(Slice.sz)) (W64 0))%V.
      iDestruct (own_slice_sz with "H") as %Hsz.
      iFrame. iSplitR "len".
      + unfold own_slice. rewrite untype_replicate. simpl. iFrame.
      + iSplitL "len".
        * rewrite Hsz. assert (#(W64 (uint.nat x.(Slice.sz))) = #x.(Slice.sz)). {
            f_equal. rewrite w64_to_nat_id. auto. } rewrite H0. iFrame.
        * iPureIntro. split.
          -- intros.  inversion H0.
          -- rewrite length_replicate. split; auto. intros. split; word.
    - iIntros "H". wp_pures. iNamed "H". iDestruct "H" as "(H1 & H3 & H4 & H5 & H6 & H7 & %H8 & %H9 & %H10)".
      wp_load. iModIntro. iApply "H2". iFrame.
      assert (false = false) by auto.
      apply H8 in H.
      assert (maxTSCoq xs ys = l). {
        generalize dependent ys. generalize dependent l. generalize dependent i.
        induction xs.
        + intros. inversion H9. apply nil_length_inv in H1. rewrite H1. auto.
        + induction ys.
          * intros. inversion H3.
          * intros. simpl. destruct (decide (uint.Z a >? uint.Z a0 = true)).
            -- rewrite e. simpl.
               rewrite length_cons in H9.
               assert (0%nat < uint.nat i <= length (a :: xs)). {
                 rewrite length_cons. rewrite H. rewrite length_cons. word. }
               destruct H10.
               eapply H1 in H0; try word; try eassumption; try auto.
               unfold coqMax in H0. rewrite e in H0.
               rewrite <- head_lookup in H0. rewrite head_Some in H0. destruct H0.
               rewrite H0. f_equal. eapply IHxs; try word; try eassumption; try auto.
               ++ rewrite length_cons in H4. word.
               ++ intros. rewrite length_cons in H. assert (uint.nat (uint.nat i - 1) = length xs) by word.
                  eapply H6.
               ++ rewrite H. rewrite length_cons. assert (S (length xs) - 1 = length xs) by word.
                  rewrite H5. rewrite length_cons in H4. assert (length xs < 2 ^ 64) by word. word.
               ++ rewrite H0 in H9. rewrite length_cons in H9. inversion H9. word.
               ++ split.
                  ** intros. assert (l !! (S i')%nat = x0 !! i'). {
                       rewrite H0. rewrite lookup_cons.
                       auto.
                     }
                     rewrite <- H10. apply H1; try word.
                     { assert (uint.nat i <= length (a :: xs)) by word.
                       assert (i' < uint.nat (W64 (uint.nat i - 1))) by word.
                       assert (S i' < uint.nat (W64 (uint.nat i - 1)) + 1) by word.
                       rewrite length_cons in H4.
                       assert (length xs < 2 ^ 64) by word. word.
                     }
                     { rewrite lookup_cons. auto. }
                     { rewrite lookup_cons. auto. }
                  ** rewrite H. rewrite length_cons. word.
            -- assert (ne: (uint.Z a >? uint.Z a0) = false) by word. rewrite ne. simpl.
               rewrite length_cons in H9.
               assert (0%nat < uint.nat i <= length (a :: xs)). {
                 rewrite length_cons. rewrite H. rewrite length_cons. word. }
               destruct H10.
               eapply H1 in H0; try word; try eassumption; try auto.
               unfold coqMax in H0. rewrite ne in H0.
               rewrite <- head_lookup in H0. rewrite head_Some in H0. destruct H0.
               rewrite H0. f_equal. eapply IHxs; try word; try eassumption; try auto.
               ++ rewrite length_cons in H4. word.
               ++ intros. rewrite length_cons in H. assert (uint.nat (uint.nat i - 1) = length xs) by word.
                  eapply H6.
               ++ rewrite H. rewrite length_cons. assert (S (length xs) - 1 = length xs) by word.
                  rewrite H5. rewrite length_cons in H4. assert (length xs < 2 ^ 64) by word. word.
               ++ rewrite H0 in H9. rewrite length_cons in H9. inversion H9. word.
               ++ split.
                  ** intros. assert (l !! (S i')%nat = x0 !! i'). {
                       rewrite H0. rewrite lookup_cons.
                       auto.
                     }
                     rewrite <- H10. apply H1; try word.
                     { assert (uint.nat i <= length (a :: xs)) by word.
                       assert (i' < uint.nat (W64 (uint.nat i - 1))) by word.
                       assert (S i' < uint.nat (W64 (uint.nat i - 1)) + 1) by word.
                       rewrite length_cons in H4.
                       assert (length xs < 2 ^ 64) by word. word.
                     }
                     { rewrite lookup_cons. auto. }
                     { rewrite lookup_cons. auto. }
                  ** rewrite H. rewrite length_cons. word.
      }
      rewrite H0. iFrame.
  Qed. 
  
End heap.
