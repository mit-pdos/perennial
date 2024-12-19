From Goose.github_com.session Require Import sort.
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

  Definition is_sorted (xs: list w64) :=
  ∀ (i j: nat), (i < j)%nat ->
         ∀ (x1 x2: w64), xs !! i = Some x1 ->
                         xs !! j = Some x2 ->
                  uint.Z x1 <= uint.Z x2.

  (* Fixpoint insert (lst: list w64) (element: w64) (i: nat) :=
    match lst with
    | [] => [element]
    | cons h tl => match i with
                   | 0%nat => cons element lst 
                   | S n => cons h (insert tl element n)
                   end
    end. *) 

  Lemma implies_Sorted :
    forall (xs: list w64) (element: w64) (i: w64),
    is_sorted xs ->
    uint.nat i <= length xs ->
    (∀ (i': nat), i' < uint.nat i →
                  ∀ (x: w64), xs !! i' = Some x →
                              uint.Z x < uint.Z element) -> 
    (∀ (j': nat),
          uint.nat i ≤ j' →
          ∀ (y: w64), xs !! j' = Some y →
                      uint.Z element <= uint.Z y) ->
    is_sorted ((take (uint.nat i) xs) ++ (cons element (drop (uint.nat i) xs))).
  (* prove inserting xs at some elemnt of a list produces a new list which has the prefix of the
                                                    previous list ++ element :: tail of the list (take for head of list) (drop for tail)
                                                    instead of insert function
                                                    lemma if i < length of list then inserting element insert_take_drop
                                                  *)
  (* any sublist of sorted list is sorted *)
  (* there is an issue which i is it talking about for the new list or the old list? *)
  Proof.
    unfold is_sorted. intros.
    destruct (decide (j < uint.nat i)).
    - assert (i0 < (uint.nat i - 1)) by word.
      rewrite lookup_app_l in H4.
      + rewrite lookup_app_l in H5.
        * rewrite lookup_take in H4; try word.
          rewrite lookup_take in H5; try word.
          eapply H in H3; try eassumption.
        * rewrite length_take_le; try word.
      + rewrite length_take_le; try word.
    - assert (j >= (uint.nat i - 1)) by word. clear n.
      destruct (decide (j = (uint.nat i)%nat)).
      + clear H6. subst.
        (* H5: element = Some x2 *)
        rewrite lookup_app_l in H4.
        * rewrite lookup_app_r in H5.
          -- rewrite length_take_le in H5; try word.
             assert ((uint.nat i - (uint.nat i))%nat = 0%nat) by word.
             rewrite H6 in H5. rewrite <- head_lookup in H5. simpl in H5.
             injection H5 as ?. rewrite lookup_take in H4; try word. 
             assert (i0 < uint.nat i) by word. rewrite <- H5.
             apply Z.lt_le_incl. eapply H1; try eassumption.
          -- rewrite length_take_le; try word.
        * rewrite length_take_le; try word.
      + destruct (decide (i0%nat = (uint.nat i))).
        * assert (j > uint.nat i) by word. rewrite lookup_app_r in H4.
        -- rewrite lookup_app_r in H5.
           ++ rewrite e in H4. rewrite length_take_le in H4; try word.
              assert ((uint.nat i - uint.nat i)%nat = 0%nat) by word.
              rewrite H8 in H4. rewrite <- head_lookup in H4. simpl in H4.
              injection H4 as ?. rewrite <- H4.
              rewrite lookup_cons_ne_0 in H5; try rewrite length_take_le; try word.
              rewrite lookup_drop in H5. eapply H2.
              ** assert (uint.nat i <= (uint.nat i + Init.Nat.pred (j - length (take (uint.nat i) xs)))%nat) by word. apply H9. 
              ** auto. 
           ++ rewrite length_take_le; try word.
        -- rewrite length_take_le; try word.
        * destruct (decide (i0%nat > (uint.nat i))).
          -- clear n0. clear n.
             rewrite lookup_app_r in H4; try rewrite length_take_le; try word.
             rewrite lookup_app_r in H5; try rewrite length_take_le; try word.
             rewrite lookup_cons_ne_0 in H4; try rewrite length_take_le; try word.
             rewrite lookup_cons_ne_0 in H5; try rewrite length_take_le; try word.
             rewrite lookup_drop in H4. rewrite lookup_drop in H5.
             rewrite length_take_le in H4; try word.
             rewrite length_take_le in H5; try word.
             eapply H.
             ++ assert (Init.Nat.pred (i0 - uint.nat i) <Init.Nat.pred (j - uint.nat i)) by word.
                assert (uint.nat i + Init.Nat.pred (i0 - uint.nat i) <
                          uint.nat i + Init.Nat.pred (j - uint.nat i))%nat by word.
                apply H8.
             ++ auto.
             ++ auto.
          -- assert (i0 < uint.nat i) by word.
             destruct (decide (j = (uint.nat i - 1)%nat)).
             ++ rewrite lookup_app_l in H4; try rewrite length_take_le; try word.
                rewrite lookup_app_l in H5; try rewrite length_take_le; try word.
                rewrite lookup_take in H4; try word.
                rewrite lookup_take in H5; try word.
                eapply H in H3; try eassumption.
             ++ assert (j > uint.nat i) by word.
                rewrite lookup_app_l in H4; try rewrite length_take_le; try word.
                rewrite lookup_app_r in H5; try rewrite length_take_le; try word.
                rewrite lookup_cons_ne_0 in H5; try rewrite length_take_le;
                  try word.
                rewrite lookup_take in H4; try word.
                rewrite lookup_drop in H5. eapply H.
                ** assert (i0 < (uint.nat i + Init.Nat.pred (j - length (take (uint.nat i) xs)))%nat)%nat by word. apply H9.
                ** auto.
                ** auto.
  Qed.
    
  Lemma wp_BinarySearch (s: Slice.t) (xs: list w64) (needle: w64) :
  {{{ own_slice s uint64T (DfracOwn 1) xs ∗ ⌜is_sorted xs⌝ }}}
    BinarySearch s #needle
  {{{ (i: w64) (ok: bool), RET (#i, #ok);
      own_slice s uint64T (DfracOwn 1) xs ∗
      ⌜ok = true → xs !! uint.nat i = Some needle⌝ ∗
      ⌜is_sorted xs⌝ ∗
      ⌜ ∀ (i': nat), i' < uint.nat i →
                   ∀ (x: w64), xs !! i' = Some x →
                               uint.Z x < uint.Z needle⌝ ∗
      ⌜∀ (j': nat),
                   uint.nat i ≤ j' →
                   ∀ (y: w64), xs !! j' = Some y →
                               uint.Z needle <= uint.Z y⌝ ∗
                               ⌜uint.nat i <= length xs⌝
  }}}.
  Proof.
    iIntros (Φ) "H H1". unfold BinarySearch.
    wp_pures.
    wp_apply wp_ref_to; auto.
    iIntros (i_l) "i". wp_pures.
    wp_apply wp_slice_len.
    wp_apply wp_ref_to; auto.
    iIntros (j_l) "j". wp_pures.
    iDestruct "H" as "(H & %H2)".
    iDestruct "H" as "(H & H3)". 
    iDestruct (own_slice_small_sz with "H") as %Hsz.
    wp_apply (wp_forBreak_cond
                (λ continue, ∃ (i j: w64),
                    own_slice s uint64T (DfracOwn 1) xs ∗
                    i_l ↦[uint64T] #i ∗
                    j_l ↦[uint64T] #j ∗
                    ⌜uint.Z i ≤ uint.Z j ≤ Z.of_nat (length xs)⌝ ∗
                    ⌜∀ (i': nat),
                   i' < uint.nat i →
                   ∀ (x: w64), xs !! i' = Some x →
                               uint.Z x < uint.Z needle⌝ ∗
                               ⌜∀ (j': nat),
                   uint.nat j ≤ j' →
                   ∀ (y: w64), xs !! j' = Some y →
                               uint.Z needle <= uint.Z y⌝ ∗
                               ⌜continue = false → i = j⌝ ∗
                               ⌜uint.nat i <= length xs⌝ 
                )%I
               with "[] [H H3 i j]").
    - iIntros (?). iModIntro. iIntros "H1 H2".
      wp_pures. iNamed "H1". iDestruct "H1" as "(H3 & H4 & H5 & %H6 & %H7 & %H8 & %H9)".
      wp_load. wp_load.
      wp_if_destruct.
      + wp_pures.
        wp_load. wp_load. wp_load. wp_pures.
        set (mid := word.add i (word.divu (word.sub j i) (W64 2)) : w64).
        assert (uint.Z mid = (uint.Z i + uint.Z j) / 2) as Hmid_ok.
        { subst mid.
          word. }
        list_elem xs (uint.nat mid) as x_mid.
        iDestruct "H3" as "(H3 & H6)".
        wp_apply (wp_SliceGet with "[$H3]").
        { eauto. }
        iIntros "Hs".
        simpl to_val.
        wp_pures.
        wp_if_destruct.
        * wp_store.
          iModIntro.
          iApply "H2".
          iExists (W64 (uint.Z mid + 1)). 
          iFrame.
          iSplitL.
          { unfold mid. 
            iPureIntro.
            split_and!; try word.
          }
          unfold is_sorted in *.
          iPureIntro. split.
          { intros.
            assert (i' ≤ uint.nat mid)%nat by word.
            destruct (decide ((i' < uint.nat mid)%nat)).
            - apply (H2 i' (uint.nat mid) l x x_mid) in H0; try eassumption.
              word.
            - assert (i' = uint.nat mid) by word. rewrite <- H3 in Hx_mid_lookup.
              rewrite Hx_mid_lookup in H0. injection H0 as ?. word.
          } 
          split.
          { intros. eapply H8; try apply H. auto. }
          { split.
            - intros. inversion H.
            - word. }
        * wp_store.
          iModIntro.
          iApply "H2".
          iExists i.
          iExists mid.
          iFrame.
          iPureIntro.
          split_and!; try word.
          { auto. }
          intros. unfold is_sorted in *. assert (uint.Z needle <= uint.Z x_mid ) by word.
          clear Heqb0. 
          destruct (decide (uint.nat mid = j')).
          { rewrite e in Hx_mid_lookup. rewrite H0 in Hx_mid_lookup. inversion Hx_mid_lookup.
            auto.
          } 
          { assert (uint.nat mid < j')%nat by word. assert (uint.Z x_mid <= uint.Z y). {
              eapply H2.
              - apply H3.
              - auto.
              - auto.
            } etrans; try eassumption.
          }
      + iModIntro.
        iApply "H2".
        iFrame.
        iPureIntro.
        split_and!; try word; auto.
        intros.
        word.
    - iFrame. iPureIntro.
      split; try word.
      split; try word. split.
      + intros. apply lookup_lt_Some in H0. word.
      + word.
    - iIntros "Hpost".
      wp_pures. iNamed "Hpost". iDestruct "Hpost" as "(H2 & H3 & H4 & %H5 & %H6 & %H7 & %H8 & %H9)".
      wp_load. wp_pures. wp_apply wp_slice_len. rewrite Hsz. wp_pures.
      wp_if_destruct.
      + assert (uint.Z i < uint.nat s.(Slice.sz)) by word. rewrite <- Hsz in H.
        assert (uint.nat i < length xs)%nat by word.
        eapply list_lookup_lt in H0.
        wp_load. wp_bind (SliceGet _ _ _)%E.
        wp_load.
        iDestruct "H2" as "(H9 & H10)".
        assert (uint.Z i < uint.nat s.(Slice.sz)) by word.
        rewrite <- Hsz in H1.
        assert (uint.nat i < length xs)%nat by word.
        eapply list_lookup_lt in H3.
        destruct H3.
        wp_apply (wp_SliceGet with "[$H9]").
        * assert (uint.Z i < uint.nat s.(Slice.sz)) by word. iPureIntro. 
          apply H3.
        * iIntros "H". wp_pures. iModIntro. iApply "H1". iFrame. iPureIntro. split.
          -- destruct (decide (#x = #needle)). 
             ++ intros. apply bool_decide_eq_true in H4. inversion H4. rewrite <- H11. auto.
             ++ intros. apply bool_decide_eq_true in H4. inversion H4. rewrite <- H11. auto.
          -- split; auto. split.
             { intros. eapply H6 in H4; eassumption. }
             { intros. destruct H8; auto. split; try word. 
               eapply H7; eassumption. }
      + wp_load. wp_pures. iModIntro. iApply "H1". iFrame. iPureIntro. intros. split; try intros;
          try inversion H. split; auto. split.
        { intros. eapply H6; eassumption. }
        { intros. destruct H8; auto. split; try word. eapply H7; eassumption. }
  Qed.

  (* Lemma wp_insert (s: Slice.t) (xs: list w64) (v: w64) :
    {{{ own_slice s uint64T (DfracOwn 1) xs ∗ ⌜is_sorted xs⌝ }}}
      SortedInsert s #v
      {{{ (ns: Slice.t), RET slice_val (ns);
          (∃ (nxs: list w64), own_slice ns uint64T (DfracOwn 1) nxs ∗
                              ⌜is_sorted nxs⌝)%I
      }}}.
  Proof.
    iIntros (Φ) "(H & %H1) H2". unfold SortedInsert. wp_pures. 
    wp_apply (wp_BinarySearch with "[$H]"); auto.
    iIntros (i ok) "H". wp_pures. wp_if_destruct.
    - iModIntro. iApply "H2". iDestruct "H" as "(H1 & H2 & H3 & %H4 & %H5 & H6)". 
      iFrame. 
    - wp_bind (SliceSkip uint64T s #i). iDestruct "H" as "(H1 & H3 & %H3 & %H4 & %H5)". 
      (* get the length from the slice *)
      iDestruct (own_slice_sz with "H1") as %Hsz.
      wp_apply (wp_SliceSkip with "[H1]"). (* we gave ownership of the slice to the other person *)
      + destruct H5 as (x & y & z & H8 & H9 & H10); auto.
        assert (uint.Z (length xs) = uint.Z s.(Slice.sz)) by word. rewrite <- H.
        apply lookup_lt_Some in H9. word.
      + iModIntro.
        wp_apply wp_SliceTake_full_cap. (* wp_SliceTake. *)
        * (* Say that the capacity at smallest is the length *)
          Search Slice.cap.
        wp_bind (SliceTake s (#i + #(W64 1)))%I.
        wp_pures. 

        assert (i <= length xs) by word.
        
      + wp_bind (SliceTake s (#i + #(W64 1)))%I.
      Search "SliceSkip". wp_bind (SliceTake s #(w64_word_instance.(word.add) i (W64 1))).

      Search SliceAppendSlice. wp_pures.
      wp_apply
        wp_SliceAppendSlice. wp_SliceAppendSlice.


   *)
  

End heap. 
