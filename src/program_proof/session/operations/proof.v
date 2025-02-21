From Goose.github_com.session Require Import server.
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

Module operation.
  Section operation.

    Record t :=
      mk {
          operationType: w64 ;
          versionVector: list w64 ;
          data: w64 ;
        }.

    Search "IntoVal".

    Search "Lit".
    
    #[global] Instance into_val : IntoVal t.
    Proof.
    Admitted. 
    (* refine {| into_val.to_val := (λ (x:t),
                                     ∃ (l: Slice.t),
                                       struct.mk_f Operation [
                                           "OperationType" ::= #(LitInt x.(operationType)) ;
                                                               "VersionVector" ::= own_slice l uint64T (DfracOwn 1) x.(versionVector) ;
                                                                                 "Data" ::= #x.(l)
                                   ])%V ;
             |}.
      intros. simpl. by destruct v0. *)

    #[global] Instance into_val_for_type : IntoValForType t (struct.t Operation).
    Proof. constructor; auto. Admitted.

  End operation.

  Section heap.
    Context `{hG: !heapGS Σ}.

    Definition own_operation (o: loc) (op: operation.t) : iProp Σ :=
      ∃ v_l, o ↦[Operation :: "OperationType"] #op.(operationType) ∗
             o ↦[Operation :: "VersionVector"] (slice_val v_l) ∗
             
             own_slice v_l uint64T (DfracOwn 1) op.(versionVector) ∗
             o ↦[Operation :: "Data"] #op.(data).

    Fixpoint coqEqualSlices (s1: list w64) (s2: list w64) :=
      match s1 with
      | [] => true
      | cons h1 t1 => match s2 with
                      | [] => true
                      | cons h2 t2 => if (negb ((uint.Z h1) =? (uint.Z h2)))
                                      then false else (coqEqualSlices t1 t2)
                      end
      end.

    
    Lemma wp_equal_slices (x: Slice.t) (xs: list w64) (y: Slice.t) (ys: list w64) :
      {{{
            own_slice x uint64T (DfracOwn 1) xs ∗
            own_slice y uint64T (DfracOwn 1) ys ∗
            ⌜length xs = length ys⌝ ∗
            ⌜length xs < 2^64⌝
      }}}
        equalSlices x y 
        {{{
              r , RET #r;
              ⌜r = coqEqualSlices xs ys⌝ ∗ 
              own_slice x uint64T (DfracOwn 1) xs ∗
              own_slice y uint64T (DfracOwn 1) ys ∗
              ⌜length xs = length ys⌝ ∗
              ⌜length xs < 2^64⌝
        }}}.
    Proof.
      iIntros (Φ) "(H1 & H2) H3".
      unfold equalSlices.
      wp_pures.
      wp_apply wp_ref_to; auto.
      iIntros (output) "H4". wp_pures.
      wp_apply wp_ref_to; auto.
      iIntros (index) "H5". wp_pures.
      wp_apply wp_slice_len.
      wp_apply wp_ref_to; auto.
      iIntros (l) "H6". wp_pures.
      wp_apply (wp_forBreak_cond
                  (λ continue,
                     ∃ (b: bool) (i: w64),
                       "Hx" ∷ own_slice x uint64T (DfracOwn 1) xs ∗
                       "Hy" ∷ own_slice y uint64T (DfracOwn 1) ys ∗
                       output ↦[boolT] #b ∗
                       index ↦[uint64T] #i ∗
                       l ↦[uint64T] #(length xs) ∗
                       ⌜length xs = length ys⌝ ∗
                       ⌜length xs < 2^64⌝ ∗
                       ⌜∀ (x y: w64),
                     uint.nat i <= length xs ->
                     xs !! (uint.nat i) = Some x ->
                     ys !! (uint.nat i) = Some y ->
                     (uint.Z x) =? (uint.Z y) = true ->
                     b = true⌝ ∗                   
                     ⌜∀ (i': nat),
                     ∀ (x y: w64),
                     i' < uint.nat i <= length xs ->
                     xs !! i' = Some x ->
                     ys !! i' = Some y ->
                     (uint.Z x) =? (uint.Z y) = false
                     -> b = false⌝ ∗  
                     ⌜uint.Z i <= (uint.Z (length xs))⌝ ∗ 
                     ⌜continue = true -> 
                     b = true⌝ ∗
                     ⌜continue = false ->
                     (exists x y, xs !! (uint.nat i) = Some x /\
                                  ys !! (uint.nat i) = Some y /\
                                  ((uint.Z x) =? (uint.Z y)) = false /\ b = false)
                     \/ ((uint.Z i) = uint.Z (W64 (length xs)) /\ b = true)⌝ 
                  )%I
                 with "[] [H1 H4 H2 H5 H6]").
      - iIntros (?).
        iModIntro. iIntros "H1 H2".
        iNamed "H1".
        iDestruct "H1" as "(H3 & H4 & H5 & %H6 & %H7)".
        destruct H7 as (H7 & H8 & H9 & H10 & H11 & H12).
        wp_pures. wp_load. wp_load. wp_if_destruct.
        + wp_pures. wp_load.
          assert ((uint.nat i < length xs)%nat) by word.
          apply list_lookup_lt in H. destruct H.
          iDestruct "Hx" as "[Hx Hxc]".
          iDestruct "Hy" as "[Hy Hyc]".
          wp_apply (wp_SliceGet with "[$Hx]").
          * iPureIntro. apply H.
          * iIntros "Hx". wp_pures.
            wp_load. assert ((uint.nat i < length ys)%nat) by word.
            eapply list_lookup_lt in H0. destruct H0.
            wp_apply (wp_SliceGet with "[$Hy]").
            { iPureIntro. apply H0. }
            iIntros "Hy". wp_pures. case_bool_decide.
            { wp_pures. wp_load. wp_store. iModIntro. iApply "H2". iExists b.
              iExists (w64_word_instance.(word.add) i (W64 1)).
              iFrame. iPureIntro. split; try word.
              split; try word. split.
              - intros. eapply H11; auto.
              - split.
                + intros. destruct (decide (i' = uint.nat i)).
                  * inversion H1. rewrite e in H3. rewrite e in H4.
                    rewrite H in H3. rewrite H0 in H4. injection H3 as ?.
                    injection H4 as ?. word.
                  * assert (i' < uint.Z (w64_word_instance.(word.add) i (W64 1))) by lia.  assert (i' <= uint.nat i). { apply Zlt_succ_le. replace (Z.succ (uint.nat i)) with (uint.Z (w64_word_instance.(word.add) i (W64 1))) by word. auto. }
                    assert (i' < uint.nat i <= length xs) by word.
                    eapply H9; try eassumption.
                + split; try word. split; auto. intros. inversion H2.
            }
            { wp_pures. wp_store. iModIntro. iApply "H2". iExists false. iExists i.
              iFrame. iPureIntro. split; auto. split; auto. split.
              - intros. rewrite H in H3. rewrite H0 in H4. injection H3 as ?.
                injection H4 as ?. unfold not in H1.
                assert (x2 = y0) by word. rewrite H13 in H3. rewrite <- H4 in H3.
                rewrite H3 in H1. assert (#x1 = #x1) by word. apply H1 in H14.
                inversion H14.
              - split; auto. split; auto. split; auto. left.
                exists x0. exists x1. split; auto. split; auto.
                split; auto. destruct (decide (x0 = x1)).
                + rewrite e in H1. assert (#x1 = #x1) by auto. unfold not in H1. apply H1 in H3. inversion H3.
                + word.
            }
        + iModIntro. iApply "H2". iExists b. iExists i. iFrame. iPureIntro.
          split; auto. split; auto. split; auto. split; auto. split; auto.
          split; auto. right.
          * split; try word. auto.
      - iDestruct (own_slice_sz with "H1") as %Hsz.
        iDestruct "H2" as "[(H7 & H8) (H9 & H10)]". iDestruct "H1" as "[H11 H12]".
        iExists true. iExists (W64 0).
        rewrite Hsz.
        assert (#(W64 (uint.nat x.(Slice.sz))) = #x.(Slice.sz)). {
          f_equal. rewrite w64_to_nat_id. auto. }
        rewrite H.
        iFrame. iPureIntro. split; try intros; try word.
        split; try intros; try word.
      - iIntros "H".
        iNamed "H". iDestruct "H" as "(H1 & H2 & H8 & %H5 & %H6)".
        destruct H6 as (H6 & H7 & H8 & H9 & H10 & H11).
        wp_pures. wp_load. iModIntro. iApply "H3". iFrame. iPureIntro. split; auto.
        + unfold coqEqualSlices. assert (uint.nat i <= length xs) by word. clear H9. 
          generalize dependent ys. generalize dependent i.
          induction xs.
          * intros. destruct H11.
            { auto. }
            { destruct H0. destruct H0. destruct H0. inversion H0. }
            { destruct H0. auto. }
          * intros. simpl. induction ys.
            { inversion H5. }
            { destruct (decide ((uint.Z a =? uint.Z a0) = true)).
              - rewrite e. simpl.
                destruct (decide (uint.nat i = 0%nat)).
                + eapply IHxs.
                  * rewrite length_cons in H6. word.
                  * assert (uint.nat 0 <= length xs) by word.
                    apply H0.
                  * auto.
                  * intros. eapply H7.
                    { rewrite length_cons. rewrite e0. word. }
                    { rewrite e0. simpl. auto. }
                    { rewrite e0. simpl. auto. }
                    { auto. }
                  * word.
                  * intros; auto. destruct H11; auto.
                    { destruct H1. destruct H1. rewrite e0 in H1.
                      destruct H1. destruct H2. simpl in H1.
                      simpl in H2. destruct H3.
                      injection H1 as ?. injection H2 as ?. word.
                    }
                    { right. destruct H1. rewrite length_cons in H1.
                      assert (uint.nat i = uint.nat (W64 (S (length xs)))) by word.
                      rewrite e0 in H3.
                      rewrite length_cons in H6.
                      replace (uint.nat (W64 (S (length xs)))) with
                        (S (length xs))%nat in H3 by word.
                      word.
                    }
                + eapply IHxs.
                  * rewrite length_cons in H6. word.
                  * rewrite length_cons in H.
                    assert (uint.nat (uint.nat i - 1) <= length xs) by word.
                    apply H0.
                  * auto.
                  * intros. eapply H7.
                    { rewrite length_cons. word. }
                    { rewrite lookup_cons.
                      assert ((S (uint.nat (W64 (uint.nat i - 1))) = uint.nat i)%nat) by word.
                      rewrite <- H4. apply H1. }
                    { rewrite lookup_cons.
                      assert ((S (uint.nat (W64 (uint.nat i - 1))) = uint.nat i)%nat) by word.
                      rewrite <- H4. apply H2. }
                    { auto. }
                  * intros. eapply H8.
                    { assert ((S i')%nat < uint.nat i ≤ length (a :: xs))
                        by word. apply H4.
                    }
                    { rewrite lookup_cons. simpl. eassumption. }
                    { rewrite lookup_cons. simpl. eassumption. }
                    { auto. }
                  * intros. destruct H11; auto.
                    { left. destruct H1.  destruct H1. destruct H1.
                      destruct H2. exists x0. exists x1.
                      split.
                      - replace (uint.nat (W64 (uint.nat i - 1))) with (Init.Nat.pred (uint.nat i)) by word.
                        rewrite lookup_cons_ne_0 in H1; try word.
                        auto.
                      - split.
                        + replace (uint.nat (W64 (uint.nat i - 1))) with (Init.Nat.pred (uint.nat i)) by word.
                          rewrite lookup_cons_ne_0 in H2; try word.
                          auto.
                        + auto.
                    }
                    { right. rewrite length_cons in H1. destruct H1.
                      split; try word. auto.
                    }
              - assert ((uint.Z a =? uint.Z a0) = false) by word.
                rewrite H0. simpl. destruct H11; auto.
                + destruct H1.  destruct H1. destruct H1. destruct H2.  destruct H3. auto.
                + destruct H1.
                  eapply H8.
                  * rewrite length_cons in H1.
                    rewrite length_cons in H6.
                    assert (uint.nat i = S (length xs)) by word.
                    assert (0%nat < uint.nat i <= length (a :: xs)). { rewrite length_cons. word. } apply H4.
                  * simpl. auto.
                  * simpl. auto.
                  * auto.
            } 
    Qed.

    Definition coq_equalOperation o1 o2 :=
      (andb (andb (uint.Z o1.(operation.operationType) =? uint.Z o2.(operation.operationType))
               (coqEqualSlices o1.(operation.versionVector) o2.(operation.versionVector)))
         ((uint.Z o1.(operation.data) =? uint.Z o2.(operation.data)))).

    Lemma wp_equalOperation l1 o1 l2 o2 :
      {{{
            own_operation l1 o1 ∗ own_operation l2 o2 
      }}}
        equalOperations #l1 #l2
        {{{
              r , RET #r;
              ⌜r = coq_equalOperation o1 o2⌝ ∗
              own_operation l1 o1 ∗  own_operation l2 o2 
        }}}.
    Proof.  
      iIntros (Φ) "(H1 & H2) H3".
      unfold equalOperations.
      wp_pures.
      unfold own_operation in *.
      iNamed "H1".
      iNamed "H2".
      iDestruct "H1" as "(H1 & H4 & H5 & H6)".
      iDestruct "H2" as "(H2 & H7 & H8 & H9)".
      wp_loadField.
      wp_loadField.
      wp_pures.
      wp_bind (if: #(bool_decide (#o1.(operationType) = #o2.(operationType))) then _ else _)%E. wp_if_destruct.
      - wp_loadField. wp_loadField.
        wp_apply (wp_equal_slices with "[H5 H8]").
        + iFrame. admit.
        + iIntros (r) "(%H10 & H11 & H12 & %H13 & %H14)".
          destruct (decide (r = true)).
          * rewrite e. wp_pures.
            wp_loadField.
            wp_loadField.
            wp_pures. iModIntro. iApply "H3". iFrame. iPureIntro.
            unfold coq_equalOperation. rewrite <- H10. rewrite e.
            assert ((uint.Z o1.(operationType) =? uint.Z o2.(operationType)) = true) by word. rewrite H. simpl. case_bool_decide.
            { inversion H0. rewrite H2. word. }
            { destruct (decide (o1.(data) = o2.(data))).
              - rewrite e0 in H0. assert (#o2.(data) = #o2.(data)) by auto. unfold not in H0. apply H0 in H1.
                inversion H1.
              - symmetry. rewrite Z.eqb_neq. f_equal. unfold not. intros. word.
            } 
          * apply not_true_is_false in n. rewrite n. wp_pures.
            iModIntro. iApply "H3". iFrame. iPureIntro.
            unfold coq_equalOperation. rewrite <- H10. rewrite n.
            assert ((uint.Z o1.(operationType) =? uint.Z o2.(operationType)) = true) by word. rewrite H. simpl. word.
      - wp_pures. iModIntro. iApply "H3". iFrame. iPureIntro.
        unfold coq_equalOperation. word.
    Admitted.
    
    Definition coq_deleteAtIndex (o : list operation.t) index :=
      (take index o) ++ (drop (index + 1) o).

    Lemma wp_deleteAtIndex (ops: Slice.t) (index: w64) (l: list operation.t) :
      {{{
            ⌜0 <= uint.nat index < length l⌝ ∗   
            own_slice ops (struct.t Operation) (DfracOwn 1) (l)
      }}}
        deleteAtIndex ops #index
        {{{
              (ns: Slice.t), RET slice_val (ns);
              own_slice ns (struct.t Operation) (DfracOwn 1) (coq_deleteAtIndex l (uint.nat index)) 
        }}}.
    Proof.
      iIntros (Φ) "(%H & H) H2".
      iDestruct (own_slice_sz with "H") as %Hsz.
      unfold deleteAtIndex.
      wp_pures.
      wp_apply wp_NewSlice_0.
      iIntros (s) "H1".
      wp_apply wp_ref_to; auto.
      iIntros (l1) "H3".
      wp_pures. wp_bind (SliceAppendSlice _ _ _).
      iDestruct (own_slice_wf with "H") as %Hcap.
      wp_apply (wp_SliceTake); try word.
      wp_load.
      iDestruct "H" as "[H H4]".
      iDestruct (slice_small_split with "H") as "H".
      + assert (uint.Z index <= length l) by word.
        eassumption.
      + iDestruct "H" as "[H H5]". wp_apply (wp_SliceAppendSlice with "[H H1]"); auto.
        * iSplitL "H1"; iFrame.
        * iIntros (s') "H". wp_pures. wp_store.
          wp_pures. wp_apply (wp_SliceSkip); try word.
          wp_load.
          wp_apply (wp_SliceAppendSlice with "[H H5 H3]"); auto.
          { iDestruct "H" as "[H H1]". iSplitL "H"; iFrame.
            iDestruct (slice_small_split with "H5") as "[H5 H6]".
            - assert (uint.Z 1 <= length (drop (uint.nat index) l)).
              { rewrite length_drop. word. }
              eassumption.
            - assert ((W64 1) = (w64_word_instance.(word.sub) (w64_word_instance.(word.add) index (W64 1)) (index))) by word. rewrite H0.
              destruct (slice_skip_skip (w64_word_instance.(word.add) index (W64 1)) index ops (struct.t Operation)); try word. rewrite <- H0. iApply "H6".
          }
          iIntros (s'') "H".
          iApply "H2".
          iDestruct "H" as "[H H3]".
          assert ((([] ++ take (uint.nat index) l) ++
                     drop (uint.nat (W64 1)) (drop (uint.nat index) l)) =
                  coq_deleteAtIndex l (uint.nat index)). {
            unfold coq_deleteAtIndex. simpl. rewrite drop_drop.
            replace (uint.nat (W64 1)) with 1%nat by word. auto.
          }
          rewrite H0. auto.
    Qed.

    (*

              Search "length".
            unfold own_slice_small.
            unfold slice_skip.
            (* we need to advance the slice to skip the element we are deleting *)
            Search "own_slice_small".
            iApply own_slice_small_skipn.
            Search "own_slice_small".
       i
      + iDestruct "H" as "[H H1]". iSplitL "H".
        * iFrame.
          * 
          
        

            iAssert (own_slice_small (slice_skip ops (struct.t Operation) index) (struct.t Operation) (DfracOwn (1)) (drop (uint.nat index) l) ∗ own_slice_cap ops (struct.t Operation))%I with "[H2 H1]" as "H5". { iFrame. } 

      wp_pures.
      Search "NewSlice".
      wp_bind (ref_to _)%E.
        wp_apply wp_ref_to.
      Search "ref_to".

      wp_bind (SliceAppendSlice _ _ _).
      wp_apply (wp_SliceSkip); try word.
      unfold own_slice.
      unfold slice.own_slice.
      iDestruct (own_slice_wf with "H") as %Hcap.
      wp_apply (wp_SliceTake); try word.
      Search "SliceAppendSlice".
      (* Why do we want ownership over the prefix? *)
      wp_apply (wp_SliceAppendSlice with "[H]"); auto.
      - iDestruct "H" as "[H H1]".
        iDestruct (slice_small_split with "H") as "H".
        + assert (uint.Z index <= length l) by word.
          eassumption.
        + iDestruct "H" as "[H H2]". iSplitL.
          * iDestruct "H2" as "[H2 H3]".
            (* I want to assert that the right slice doesn't change capacity, how do we do this? *)
            iAssert (own_slice_small (slice_skip ops (struct.t Operation) index) (struct.t Operation) 
                       (DfracOwn (1 /2)) (drop (uint.nat index) l) ∗ own_slice_cap ops (struct.t Operation))%I with "[H2 H1]" as "H4". { iFrame. }
            Search "own_slice_cap".
             iApply own_slice_cap_take in "H3"; try word. iFrame.
          * 
        
      
      Search 
        Search "SliceAppendSlice".
      - iDestruct "H" as "[H H1]".
        Search "slice_small".
        iDestruct (slice_small_split with "H") as "H".
        + assert (uint.Z index <= length l) by word.
          eassumption.
        + (* iMod (inv_alloc _ _ (own_slice_cap ops (struct.t Operation)) with "[H1]") as "Hinv". *)
          iDestruct "H" as "[H H2]". iSplitL.
          * iAssert (own_slice_small (slice_skip ops (struct.t Operation) index) (struct.t Operation) 
                       (DfracOwn 1) (drop (uint.nat index) l) ∗ own_slice_cap ops (struct.t Operation))%I with "[H2 H1]" as "H3". { iFrame. }
            iApply own_slice_cap_take in "H3"; try word. iFrame. (* I think we need ghost state for this *)

     *)

            
            
            
