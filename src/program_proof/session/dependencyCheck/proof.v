From Goose.github_com.session Require Import comparison.
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

Module Server.

  Record t :=
    mk {
        id: w64 ;
        data: w64 ;
        vectorClock: list w64; 
      }.

End Server.

Module ClientRequest.

  Record t :=
    mk {
        op: w64 ;
        data: w64 ;
        readVector: list w64;
        writeVector: list w64;
      }.

End ClientRequest
.
Module ClientReply.

  Record t :=
    mk {
        succeeded: bool ;
        op : w64 ;
        data : w64
      }.

End ClientReply.

Section heap.
  
  Context `{hG: !heapGS Σ}.

  Fixpoint coqCompareVersionVector (v1: list w64) (v2: list w64) : bool :=
    match v1 with
    | [] => true
    | cons h1 t1 => match v2 with
                    | [] => true
                    | cons h2 t2 => if (uint.Z h1) <? (uint.Z h2) then false else
                                      (coqCompareVersionVector t1 t2)
                    end
                                  
    end.

  (* Rewrite this along with file since comparisons are wrong *)
  Definition coqDependencyCheck (server : Server.t) (request : ClientRequest.t) :=
    match uint.Z (request.(ClientRequest.op)) with
    | 0 => coqCompareVersionVector server.(Server.vectorClock) request.(ClientRequest.readVector)
    | 1 => coqCompareVersionVector server.(Server.vectorClock) request.(ClientRequest.readVector)
    | 2 => coqCompareVersionVector server.(Server.vectorClock) request.(ClientRequest.writeVector)
    | 3 => coqCompareVersionVector server.(Server.vectorClock) request.(ClientRequest.writeVector)
    | _ => coqCompareVersionVector server.(Server.vectorClock) request.(ClientRequest.readVector) && coqCompareVersionVector server.(Server.vectorClock) request.(ClientRequest.writeVector)
    end.

  Search "own_slice".

  Lemma versionVec_equiv (x: Slice.t) (xs: list w64) (y: Slice.t) (ys: list w64) :
    {{{
          own_slice x uint64T (DfracOwn 1) xs ∗
          own_slice y uint64T (DfracOwn 1) ys ∗
          ⌜length xs = length ys⌝ ∗
          ⌜length xs < 2^64⌝
    }}}
       compareVersionVector x y 
      {{{
            r , RET #r;
            ⌜r = coqCompareVersionVector xs ys⌝ ∗ 
            own_slice x uint64T (DfracOwn 1) xs ∗
            own_slice y uint64T (DfracOwn 1) ys ∗
            ⌜length xs = length ys⌝ ∗
            ⌜length xs < 2^64⌝
      }}}.
  Proof.
    iIntros (Φ) "(H1 & H2) H3".
    unfold compareVersionVector.
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
                   (uint.Z x) >=? (uint.Z y) = true ->
                   b = true⌝ ∗                   
                   ⌜∀ (i': nat),
                     ∀ (x y: w64),
                   i' < uint.nat i <= length xs ->
                   xs !! i' = Some x ->
                   ys !! i' = Some y ->
                   (uint.Z x) <? (uint.Z y) = true
                   -> b = false⌝ ∗  
                   ⌜uint.Z i <= (uint.Z (length xs))⌝ ∗ 
                   ⌜continue = true -> 
                   b = true⌝ ∗
                   ⌜continue = false ->
                   (exists x y, xs !! (uint.nat i) = Some x /\
                                ys !! (uint.nat i) = Some y /\
                                (uint.Z x) <? (uint.Z y) = true /\ b = false)
                   \/ ((uint.Z i) = uint.Z (W64 (length xs)) /\ b = true)⌝ 
                )%I
               with "[] [H1 H4 H2 H5 H6]").
    - iIntros (?).
      iModIntro. iIntros "H1 H2".
      iNamed "H1".
      iDestruct "H1" as "(H3 & H4 & H5 & %H6 & %H7)".
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
          { wp_pures. wp_store. iModIntro. iApply "H2". iExists false.
            iExists i. iFrame. iPureIntro. split; auto. intros.
            split; try intros; try destruct H7; try eassumption.
            - split; try intros.
              + rewrite H in H5. rewrite H0 in H7. inversion H5. inversion H7. word.
              + split.
              *  apply Z.lt_le_incl in Heqb0. auto.
              * split; try word. split; try intros; try inversion H4.
              left. exists (x0). exists (x1).
              split; auto. split; auto.
              apply Z.ltb_lt in H1. (* reflection tactic *)
              auto.
          }
          { wp_pures. wp_load. wp_pures.
            wp_store. iModIntro. 
            iApply "H2". iExists b.
            iExists (w64_word_instance.(word.add) i (W64 1)). iFrame.
            iPureIntro. split; auto. split.
            - intros. destruct H7. destruct H3. destruct H4. destruct H5. auto.
            - split.
              + intros. destruct H7. destruct H8. destruct H9.
                destruct H10. destruct H11. destruct H11; auto. 
              + split.
                * intros. destruct H7. assert (i' <= uint.Z (i)). { rewrite word.unsigned_add in H2.
                                                                    word. }
                  destruct (decide (uint.nat i = i')).
                  ** subst. rewrite H0 in H4. rewrite H in H3. inversion H4. inversion H3. word.
                  ** assert (i' < uint.nat i \/ i' = uint.nat i) by word. destruct H10; auto; try word.
                     destruct H8. destruct H11. eapply H11; try eassumption. word.
                * split.
                  ** intros. destruct H7 as (? & ? & ?). word.
                  ** destruct H7 as (? & ? & ? & ? & ? & ?). split; auto. intros. inversion H9.
          } 
      + iModIntro. iApply "H2". iExists b. iExists i. iFrame. iPureIntro.
        split; auto. intros. apply Znot_lt_ge in Heqb0.
        split; try destruct H7; auto. split; intros; try inversion H1.
        * destruct H0. destruct H5 as (? & ? & ? & ?). apply H8; auto.
        * split.
          { intros. destruct H0.  destruct H5.  eapply H5; try eassumption. }
          { intros. destruct H0. destruct H1.  destruct H2. 
            split; try word. intros. split; try intros; try inversion H4. 
            right. split; try word. destruct H3. auto. }
    - iDestruct (own_slice_sz with "H1") as %Hsz.
      (* I'm not sure why doing it like this perserves H1 *)
      iDestruct "H2" as "[(H7 & H8) (H9 & H10)]". iDestruct "H1" as "[H11 H12]".
      iExists true. iExists (W64 0).
      rewrite Hsz.
      assert (#(W64 (uint.nat x.(Slice.sz))) = #x.(Slice.sz)). {
        f_equal. rewrite w64_to_nat_id. auto. }
      rewrite H.
      iFrame. iPureIntro. split; try intros; try word. split; try intros; try word. 
    - iIntros "H".
      iNamed "H". iDestruct "H" as "(H1 & H2 & H8 & %H5 & %H6)".
      wp_pures. wp_load. iModIntro. iApply "H3". iFrame. iPureIntro. 
      (* destruct H6 as (? & ? & ? & ? & ? & ?). *) 
      generalize dependent ys. generalize dependent i. 
      induction xs.
      + intros. destruct H6 as (? & ? & ? & ? & ? & ?).
        destruct H4; auto.
        * destruct H4 as  (? & ? & ? & ?).  inversion H4.
        * assert (ys = []). { rewrite length_nil in H5. symmetry in H5. apply nil_length_inv in H5.
                              auto. }
          rewrite H6. cbn in *. destruct H4. auto.
      + induction ys.
        * intros. inversion H5.
        * simpl. destruct (uint.Z a <? uint.Z a0) as [] eqn:E.
          ** intros. destruct H6. destruct H0. destruct H1.
             assert (uint.nat i >= 0) by word. destruct H2.
             destruct H4. destruct H6; auto.
             { destruct H6 as (? & ? & ? & ? & ? & ?). auto. }
             { destruct (decide (i = 0)); try word. assert (0 < uint.nat i) by word.
               split; auto.
               apply (H1 0%nat a a0); auto. word.
             } 
          ** intros. split; try auto; try word. apply (IHxs ((uint.nat i - 1)) ys);
               try word. destruct H6 as (? & ? & ? & ? & ? & ?). 
             split; try word. split.
             { intros. destruct (decide (i = 0)); subst.
               - destruct H4; try auto.
                 + destruct H4 as (? & ? & ? & ? & ?).
                   assert ((uint.Z a >=? uint.Z a0) = true) by word.
                   assert (uint.nat (W64 0) = 0%nat) by word.
                   rewrite H13 in H4. rewrite H13 in H10. 
                   simpl in *. inversion H4. inversion H10. word.
                 + destruct H4. auto.
               - destruct H4; try auto.
                 + destruct H4 as (? & ? & ? & ? & ?). eapply H0; try word; try auto; try eassumption.
                   apply lookup_cons_Some in H4. destruct H4; try word.
                   apply lookup_cons_Some in H10. destruct H10; try word.
                   destruct H4. destruct H10. assert
                     (uint.nat (W64 (uint.nat i - 1)) = (uint.nat i - 1)%nat) by word.
                   rewrite H14 in H7. rewrite H14 in H8. rewrite H12 in H7. rewrite H8 in H13.
                   inversion H7. inversion H13. subst. word.
                 + destruct H4; auto.
             }
             {  split.
                - intros. destruct H4; auto.
                  + destruct H4. destruct H4. destruct H4. destruct H10.
                    eapply (H1 (i' + 1)%nat); try word.
                    * apply lookup_cons_Some. right. split; auto; try word.
                      assert ((i' + 1 - 1)%nat = i') by word. rewrite H12. eassumption.
                    * apply lookup_cons_Some. right. split; auto; try word.
                      assert ((i' + 1 - 1)%nat = i') by word. rewrite H12. eassumption.
                    * word.
                  + destruct H4.  assert (i = S(length xs)) by word. eapply (H1 (i' + 1)%nat);
                      try word.
                    * apply lookup_cons_Some. right. split; auto; try word.
                      assert ((i' + 1 - 1)%nat = i') by word. rewrite H12. eassumption.
                    * apply lookup_cons_Some. right. split; auto; try word.
                      assert ((i' + 1 - 1)%nat = i') by word. rewrite H12. eassumption.
                    * word.
                - split.
                  + assert (uint.Z i = uint.Z (W64 (S (length xs))) \/ uint.nat i < (S (length xs))) by word. destruct H6.
                    * rewrite H6. word.
                    * destruct H4; auto; try word.
                      destruct H4 as (? & ? & ? & ? & ?).
                        destruct H8. destruct (decide (i = 0)). (* reasoning about overflow *) 
                        ** rewrite e in H4. rewrite e in H7. assert (uint.nat (W64 0) = 0%nat)
                                                              by word. rewrite H10 in H4.
                          rewrite H10 in H7. simpl in *. inversion H4. inversion H7. word.
                        ** assert (uint.Z i > 0) by word. word.
                  + split; try intros; try inversion H6. destruct H4; auto.
                    * destruct H4 as (? & ? & ? & ? & ? & ?). left.
                      exists x0. exists x1. destruct (decide (i = 0)).
                      { rewrite e in H4. rewrite e in H7.
                        assert ((uint.nat (W64 0)) = 0%nat) by word. rewrite H10 in H4.
                        rewrite H10 in H7. simpl in *. inversion H4. inversion H7. word.
                      }
                      { split; try rewrite lookup_cons_ne_0 in H4; try rewrite lookup_cons_ne_0 in H7;
                                                                     try replace
                                                             (uint.nat (W64 (uint.nat i - 1)))
                          with (Init.Nat.pred (uint.nat i)) by word; try eassumption; try word.
                        split; auto.
                      }
                    * right. destruct H4. split; try word; auto.
             }
  Qed.

  Lemma equiv id serverData vectorClock opData clientData readVector writeVector
                  (vc: Slice.t) (rv: Slice.t) (wv: Slice.t)
    (s: Server.t) (c: ClientRequest.t) :
    {{{
          ⌜s.(Server.id) = id⌝ ∗
          ⌜s.(Server.data) = serverData⌝ ∗
          ⌜s.(Server.vectorClock) = vectorClock⌝ ∗
          ⌜c.(ClientRequest.op) = opData⌝ ∗
          ⌜c.(ClientRequest.data) = clientData⌝ ∗
          ⌜c.(ClientRequest.readVector) = readVector⌝ ∗
          ⌜c.(ClientRequest.writeVector) = writeVector⌝ ∗
          own_slice vc uint64T (DfracOwn 1) vectorClock ∗
          own_slice rv uint64T (DfracOwn 1) readVector ∗
          own_slice wv uint64T (DfracOwn 1) writeVector ∗
          ⌜length vectorClock = length readVector⌝ ∗
          ⌜length vectorClock = length writeVector⌝ ∗
          ⌜length vectorClock < 2^64⌝ ∗
          ⌜0 <= uint.Z opData <= 4⌝ 
    }}}
      dependencyCheck (#id, (#serverData, (vc, #()))) (#opData, (#clientData, (rv, (wv, #()))))
      {{{
            r , RET #r;
            ⌜r = coqDependencyCheck s c⌝ ∗
          own_slice vc uint64T (DfracOwn 1) vectorClock ∗
          own_slice rv uint64T (DfracOwn 1) readVector ∗
          own_slice wv uint64T (DfracOwn 1) writeVector 
      }}}.
  Proof.
    iIntros (Φ) "(%H1 & %H2 & %H3 & %H4 & %H5 & %H6 & %H7 &
H8 & H9 & H10 & H11 & H12 & H13 & %H14) H15".
    unfold dependencyCheck. wp_pures.
    wp_apply wp_ref_of_zero; auto.
    iIntros (l) "H16". wp_pures. wp_if_destruct.
    - wp_pures.
      wp_apply (versionVec_equiv with "[$H8 $H9 $H11 $H13]").
      iIntros (r) "(%H & H1 & H2 & H3 & H4)". rewrite H. wp_pures.
      wp_store. wp_pures. 
      wp_if_destruct; try rewrite Heqb in Heqb0; try inversion Heqb0.
      wp_pures. wp_if_destruct; try rewrite Heqb in Heqb1;
        try inversion Heqb1. wp_pures. wp_if_destruct;
        try rewrite Heqb in Heqb2; try inversion Heqb2.
      wp_pures. wp_if_destruct; rewrite Heqb in Heqb3; try inversion Heqb3.
      wp_pures. wp_load. iModIntro. iApply "H15". iFrame. iPureIntro.
      unfold coqCompareVersionVector. unfold coqDependencyCheck.
      rewrite Heqb. auto.
    - wp_pures. wp_if_destruct.
      + wp_pures.
        wp_apply (versionVec_equiv with "[$H8 $H9 $H11 $H13]").
      iIntros (r) "(%H & H1 & H2 & H3 & H4)". rewrite H. wp_pures.
      wp_store. wp_pures. 
      wp_if_destruct; try rewrite Heqb0 in Heqb1; try inversion Heqb1.
      wp_pures. wp_if_destruct; try rewrite Heqb0 in Heqb2;
        try inversion Heqb2. wp_pures. wp_if_destruct;
        try rewrite Heqb0 in Heqb3; try inversion Heqb3.
      wp_pures. wp_load. iModIntro. iApply "H15". iFrame. iPureIntro.
      unfold coqCompareVersionVector. unfold coqDependencyCheck.
      rewrite Heqb0. auto.
      + wp_pures. wp_if_destruct.
        * wp_pures.
          wp_apply (versionVec_equiv with "[$H8 $H10 $H12 $H13]").
          iIntros (r) "(%H & H1 & H2 & H3 & H4)". rewrite H. wp_pures.
          wp_store. wp_pures. wp_if_destruct; try rewrite Heqb1 in Heqb2; try inversion
                                                                           Heqb2.
          wp_pures. wp_if_destruct; try rewrite Heqb1 in Heqb3; try inversion Heqb3.
          wp_pures. wp_load. iModIntro. iApply "H15". iFrame. iPureIntro.
          unfold coqCompareVersionVector. unfold coqDependencyCheck.
          rewrite Heqb1. auto.
        * wp_pures. wp_if_destruct.
          { wp_apply (versionVec_equiv with "[$H8 $H10 $H12 $H13]").
          iIntros (r) "(%H & H1 & H2 & H3 & H4)". rewrite H. wp_pures.
          wp_store. wp_pures. wp_if_destruct; try rewrite Heqb2 in Heqb3; try inversion
                                                                            Heqb3.
          wp_pures. wp_load. iModIntro. iApply "H15". iFrame. iPureIntro.
          unfold coqCompareVersionVector. unfold coqDependencyCheck. rewrite Heqb2.
          auto. }
          { wp_pures. wp_if_destruct.
            -- wp_pures. wp_bind (if: _ then _ else _)%E. wp_bind
                 (compareVersionVector vc rv)%E.
               wp_apply (versionVec_equiv with "[$H8 $H9 $H11 $H13]").
               iIntros (r) "(%H & H1 & H2 & H3 & H4)". rewrite H. wp_pures.
               destruct
                 (decide (coqCompareVersionVector s.(Server.vectorClock) c.(ClientRequest.readVector) = true )).
               ++ rewrite e. wp_pures.
                  wp_apply (versionVec_equiv with "[$H1 $H10 $H12 $H4]").
                  iIntros (r0) "(%H0 & H1 & H4 & H5 & H6)".
                  wp_store. wp_pures. wp_load. iModIntro. iApply "H15". iFrame.
                    iPureIntro.
                  rewrite H0. unfold coqCompareVersionVector.
                  unfold coqDependencyCheck. rewrite Heqb3. rewrite e. auto.
               ++ apply not_true_is_false in n. rewrite n. wp_pures. wp_store.
                  wp_pures. wp_load. iModIntro. iApply "H15". iFrame. iPureIntro.
                  unfold coqDependencyCheck. rewrite Heqb3. rewrite n.
                  auto.
            -- word.
          }        
  Qed.

  

End heap.
