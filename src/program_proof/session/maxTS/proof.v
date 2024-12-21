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
                      | [] => [] (* this shouldn't happen*)
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

  (* own_slice_small_agree *)
  Lemma getMaxTsEquiv (x: Slice.t) (xs: list w64) (y: Slice.t) (ys: list w64) :
    {{{
          own_slice x uint64T (DfracOwn 1) xs ∗
            own_slice y uint64T (DfracOwn 1) ys ∗
            ⌜length xs = length ys⌝ ∗
                           ⌜length xs < 2^64⌝
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
                      own_slice s' uint64T (DfracOwn 1) l ∗ (* how do we know the length of l on entry? *)
                      index ↦[uint64T] #i ∗
                      len ↦[uint64T] #(length xs) ∗
                      slice ↦[slice.T uint64T] s' ∗ (* this is wrong *)
                      (* Something that says
                         one is greater than the other
                       *)
                      ⌜continue = false -> uint.nat i = (length xs)⌝ ∗
                                                           ⌜(length l) = (length xs)⌝ ∗
                                                                           ⌜∀ (i': nat),
                                                                             i' < uint.nat i <= length xs ->
                                                                           forall (x y z: w64), l !! i' = Some x ->
                                                                                          xs !! i' = Some y ->
                                                                                          ys !! i' = Some z ->
                                                                                          x = (coqMax y z)⌝
                )%I
               with "[] [H H1 index len s' slice]").
    - iIntros (?). iModIntro. iIntros "H1 H2".
      iNamed "H1". iDestruct "H1" as "(H1 & H3 & H4 & H5 & H6 & H7 & H8 & %H9)".
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
             wp_apply (max_equiv). iIntros (r) "%H10".
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
                   { iPureIntro. destruct H9. rewrite <- H1. apply length_insert. }
                   { iPureIntro. intros.
                     -  destruct H9. (* there are two cases either i = i' or i = i *)
                        destruct (decide (i' = uint.nat i)).
                        + subst. 
                          rewrite list_lookup_insert_Some in H2.
                          destruct H2.
                         * destruct H2. destruct H9. rewrite <- H9.
                           rewrite H in H6. injection H6 as ?. rewrite H6. 
                           rewrite H0 in H5. injection H5 as ?. rewrite H5. auto. 
                         * destruct H2. assert (uint.nat i = uint.nat i) by word. unfold not in H2.
                           apply H2 in H10. inversion H10.
                       + destruct H1.
                         rewrite Z.lt_le_pred in H1.
                         assert ((Z.pred (uint.nat (w64_word_instance.(word.add) i (W64 1)))) = uint.nat i) by word.
                         rewrite H11 in H1.
                         assert (i' < length l)%nat by word.
                         assert (i' < uint.nat i <= length xs) by word.
                         assert(uint.nat i ≠ i') by word.
                         apply (list_lookup_insert_ne l (uint.nat i) (i') r) in H14.
                         rewrite H14 in H2. 
                         eapply H8 in H2; auto.
                         * apply H2.
                         * eassumption.
                         * auto.
                   }
      + iModIntro. iApply "H2". iExists i. iExists l. iFrame. iPureIntro. split.
        * intros. word. (* look at old proof to see how we did this? *)
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
          -- rewrite length_replicate. split; auto. intros.
             word.
    - iIntros "H". wp_pures. iNamed "H". iDestruct "H" as "(H1 & H3 & H4 & H5 & H6 & H7 & %H8 & %H9 & %H10)".
      wp_load. iModIntro. iApply "H2". iFrame.
      assert (false = false) by auto.
      apply H8 in H.
      assert (maxTSCoq xs ys = l). {
        generalize dependent ys. generalize dependent l.
        induction xs.
        + intros. inversion H9. apply nil_length_inv in H1. rewrite H1. auto.
        + induction ys.
          * intros. inversion H3.
          * intros. simpl. destruct (decide (uint.Z a >? uint.Z a0 = true)).
            -- assert (0 < uint.nat i <= length (a :: xs)) by word.
            -- admit.
      }
      rewrite H. iFrame.
  Qed.
  
End heap.
