From Goose.github_com.session Require Import server.
From Perennial.program_proof Require Import std_proof. 
From Perennial.goose_lang.ffi.grove_ffi Require Export impl.
From Perennial.program_logic Require Export atomic.
From Perennial.program_proof Require Export proof_prelude.
From Perennial.program_proof Require Import grove_prelude.
From RecordUpdate Require Import RecordSet.
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang.lib.list Require Import list.
From Perennial.goose_lang.lib Require Import map.impl list.impl list.list_slice slice.typed_slice.

Module Operation.
  
  Lemma struct_ty_operation_unfold :
    struct.t Operation = (slice.T uint64T * (uint64T * unitT))%ht.
  Proof. reflexivity. Qed.

  Record t :=
    mk {
        VersionVector: list u64 ;
        Data:          u64 ;
      }.

End Operation.

Module Message.

  Record t := mk {
        MessageType: u64 ;

        C2S_Client_Id:            u64 ;
	C2S_Client_RequestNumber: u64 ;
	C2S_Client_OperationType: u64 ;
	C2S_Client_Data:          u64 ;
	C2S_Client_VersionVector: list u64 ;

	S2S_Gossip_Sending_ServerId:   u64 ;
	S2S_Gossip_Receiving_ServerId: u64 ;
	S2S_Gossip_Operations:         list Operation.t ;
	S2S_Gossip_Index:              u64 ;

	S2S_Acknowledge_Gossip_Sending_ServerId:   u64 ;
	S2S_Acknowledge_Gossip_Receiving_ServerId: u64 ;
	S2S_Acknowledge_Gossip_Index:              u64 ;

	S2C_Client_OperationType: u64 ;    
	S2C_Client_Data:          u64 ;
	S2C_Client_VersionVector: list u64 ;
	S2C_Client_RequestNumber: u64 ;
	S2C_Client_Number:        u64 ;
      }.

End Message.

Section heap.
  Context `{hG: !heapGS Σ}.

  Definition operation_val (op:Slice.t*u64): val :=
    (slice_val op.1, (#op.2, #()))%V.

  Theorem operation_val_t op : val_ty (operation_val op) (struct.t Operation).
  Proof.
    repeat constructor.
    destruct op. simpl.
    val_ty.
  Qed.

  Hint Resolve operation_val_t : core.

  Global Instance operation_into_val : IntoVal (Slice.t*u64).
  Proof.
    refine {| into_val.to_val := operation_val;
             from_val := λ v, match v with
                              | (slice_v, (#(LitInt d), #()))%V =>
                                  match from_val slice_v with
                                  | Some s => Some (s, d)
                                  | None => None
                                  end
                              | _ => None
                              end;
             IntoVal_def := (IntoVal_def Slice.t, W64 0);
           |}.
    destruct v as [[a []] d]; done. 
  Defined. 

  #[global] Instance into_val_for_type : IntoValForType (Slice.t*u64) (struct.t Operation).
  Proof. constructor; auto. Qed.

  Definition is_operation (opv: Slice.t*u64) (q: dfrac) (op: Operation.t) (opv_len: nat): iProp Σ :=
    ⌜opv.2 = op.(Operation.Data)⌝ ∗
    ⌜opv_len = length (op.(Operation.VersionVector))⌝ ∗
    own_slice_small opv.1 uint64T q op.(Operation.VersionVector)%I.

  Definition operation_slice' (q: dfrac) (op_s: Slice.t) (op: list Operation.t) (n: nat): iProp Σ :=
    ∃ ops , own_slice op_s (struct.t Operation) (DfracOwn 1) (ops) ∗
            [∗ list] _ ↦ opv;o ∈ ops;op , □ (is_operation opv q o n). 

  Definition operation_slice (s: Slice.t) (ls: list Operation.t) (n: nat) : iProp Σ :=
    operation_slice' (DfracOwn 1) s ls n.

  Fixpoint coq_compareVersionVector (v1: list w64) (v2: list w64) : bool :=
  match v1 with
  | [] => true
  | cons h1 t1 => match v2 with
                  | [] => true
                  | cons h2 t2 => if (uint.Z h1) <? (uint.Z h2) then false else
                                    (coq_compareVersionVector t1 t2)
                  end
                    
  end.

  Lemma wp_compareVersionVector (x: Slice.t) (xs: list w64) (y: Slice.t) (ys: list w64) :
    {{{
          own_slice x uint64T (DfracOwn 1) xs ∗
          own_slice y uint64T (DfracOwn 1) ys ∗
          ⌜length xs = length ys⌝ 
    }}}
      compareVersionVector x y 
      {{{
            r , RET #r;
            ⌜r = coq_compareVersionVector xs ys⌝ ∗ 
            own_slice x uint64T (DfracOwn 1) xs ∗
            own_slice y uint64T (DfracOwn 1) ys ∗
            ⌜length xs = length ys⌝ 
      }}}.
  Proof.
  Admitted.

  Fixpoint coq_equalSlices (l1: list u64) (l2: list u64) :=
    match l1 with
    | [] => true
    | cons h1 t1 => match l2 with
                    | [] => true
                    | cons h2 t2 => if (negb ((uint.Z h1) =? (uint.Z h2)))
                                    then false else (coq_equalSlices t1 t2)
                    end
    end.
  
  Lemma aux0_equalSlices (l1 l2: list u64) :
    length l1 = length l2 ->
    coq_equalSlices l1 l2 = true ->
    l1 = l2.
  Proof.
  Admitted.

  Lemma aux1_equalSlices (l1 l2: list u64) :
    length l1 = length l2 ->
    coq_equalSlices l1 l2 = false ->
    l1 ≠ l2.
  Proof.
  Admitted.

  Fixpoint coq_lexicographicCompare (v1 v2: list u64) : bool :=
    match v1 with
    | [] => false 
    | cons h1 t1 => match v2 with
                    | [] => false 
                    | cons h2 t2 => if (uint.Z h1) =? (uint.Z h2) then
                                      (coq_lexicographicCompare t1 t2) else (uint.Z h1) >? (uint.Z h2)
                    end
    end.
  
  Fixpoint coq_lexiographicCompare (v1 v2: list u64) : bool :=
    match v1 with
    | [] => false 
    | cons h1 t1 => match v2 with
                    | [] => false 
                    | cons h2 t2 => if (uint.Z h1) =? (uint.Z h2) then
                                      (coq_lexiographicCompare t1 t2) else (uint.Z h1) >? (uint.Z h2)
                    end
    end.

  Lemma aux0_lexiographicCompare (l1 l2 l3: list u64) :
    coq_lexicographicCompare l2 l1 = true ->
    coq_lexicographicCompare l3 l2 = true ->
    coq_lexicographicCompare l3 l1 = true.
  Proof.
  Admitted.

  Lemma aux1_lexiographicCompare (l1 l2: list u64) :
    length l1 = length l2 -> 
    l1 ≠ l2 ->
    (coq_lexicographicCompare l2 l1 = false <-> coq_lexicographicCompare l1 l2 = true).
  Proof.
  Admitted.

  
  Lemma wp_lexiographicCompare (x: Slice.t) (xs: list u64) (y: Slice.t) (ys: list u64) :
    {{{
          own_slice x uint64T (DfracOwn 1) xs ∗
          own_slice y uint64T (DfracOwn 1) ys ∗
          ⌜length xs = length ys⌝
    }}}
      lexiographicCompare x y 
      {{{
            r , RET #r;
            ⌜r = coq_lexiographicCompare xs ys⌝ ∗ 
            own_slice x uint64T (DfracOwn 1) xs ∗
            own_slice y uint64T (DfracOwn 1) ys ∗
            ⌜length xs = length ys⌝ 
      }}}.
  Proof.
  Admitted.

  Fixpoint coq_oneOffVersionVector (v1: list w64) (v2: list w64) (canApply: bool) : bool :=
    match v1 with
    | [] => true
    | cons h1 t1 => match v2 with
                    | [] => true
                    | cons h2 t2 => if (canApply && (uint.Z h1 + 1 =? uint.Z h2))
                                    then coq_oneOffVersionVector t1 t2 false
                                    else 
                                      if (uint.Z h1 <? uint.Z h2)
                                       then false
                                       else
                                         coq_oneOffVersionVector t1 t2 canApply
                    end
    end.

  Lemma wp_oneOffVersionVector (x: Slice.t) (xs: list u64) (y: Slice.t) (ys: list u64) :
    {{{
          own_slice x uint64T (DfracOwn 1) xs ∗
          own_slice y uint64T (DfracOwn 1) ys ∗
          ⌜length xs = length ys⌝
    }}}
      oneOffVersionVector x y
      {{{ (b: bool) , RET #b ;
          ⌜b = coq_oneOffVersionVector xs ys true⌝ ∗
          own_slice x uint64T (DfracOwn 1) xs ∗
          own_slice y uint64T (DfracOwn 1) ys ∗
          ⌜length xs = length ys⌝ 
      }}}.
  Proof.
    iIntros (Φ) "(Hx & Hy & %H) H2".
    iDestruct (own_slice_sz with "Hx") as %Hsz.
    rewrite /oneOffVersionVector.
    wp_apply wp_ref_to; auto.
    iIntros (output) "H3".
    wp_apply wp_ref_to; auto.
    iIntros (canApply) "H4".
    wp_apply wp_ref_to; auto.
    iIntros (index) "H5".
    wp_pures.
    wp_apply (wp_slice_len).
    wp_apply wp_ref_to; auto.
    iIntros (l) "H6".
    wp_pures.
    wp_apply (wp_forBreak_cond
                (λ continue, ∃ (b1 b2: bool) (i: w64),
                    "Hx" ∷ own_slice x uint64T (DfracOwn 1) xs ∗
                    "Hy" ∷ own_slice y uint64T (DfracOwn 1) ys ∗
                    output ↦[boolT] #b1 ∗
                    canApply ↦[boolT] #b2 ∗
                    index ↦[uint64T] #i ∗
                    l ↦[uint64T] #(length xs) ∗
                    ⌜uint.nat i <= length xs⌝ ∗
                    ⌜continue = false -> (b1 = false /\ uint.nat i ≠ length xs) \/ (uint.nat i = (length xs) /\ b1 = true)⌝ ∗
                    ⌜∀ (j: nat), j < (uint.nat i) -> ∀ (x y: w64),
                   xs !! j = Some x ->
                   ys !! j = Some y ->
                   (S (uint.nat x) = uint.nat y) -> b2 = false⌝ ∗
                   ⌜∀ (j: nat), j < uint.nat i -> ∀ (x y: w64), 
                   xs !! j = Some x ->
                   ys !! j = Some y ->
                   S (uint.nat x) < uint.nat y
                   -> b1 = false⌝ ∗
                   ⌜∀ (j: nat), j < uint.nat i -> ∀ (x y: w64),
                   xs !! j = Some x ->
                   ys !! j = Some y ->
                   (uint.nat x >= uint.nat y \/ (b2 = true /\ (S (uint.nat x) = uint.nat y)))
                   -> b1 = true⌝ ∗
                   ⌜b2 = true -> ∀ (j: nat) , j < (uint.nat i) -> ∀ (x y: w64), 
                   xs !! j = Some x ->
                   ys !! j = Some y ->
                   (S (uint.nat x) ≠ uint.nat y)⌝ ∗
                   ⌜length xs = uint.nat i-> b1 = true /\ b2 = true⌝ ∗
                   ⌜∀ (x y: w64),
                   xs !! (uint.nat i) = Some x ->
                   ys !! (uint.nat i) = Some y ->
                   uint.nat x >= uint.nat y ->
                   b1 = true⌝ ∗ 
                   ⌜∀ (j: nat),
                   j < uint.nat i ->
                   ∀ (x y: w64),
                   xs !! j = Some x ->
                   ys !! j = Some y ->
                   (b2 = false /\ (uint.nat x) < uint.nat y) \/ S (uint.nat x) < uint.nat y ->
                   b1 = false⌝ ∗
                   ⌜b2 = false ->
                   ∀ (j: nat),
                   j < uint.nat i ->
                   ∀ (x y: w64),
                   xs !! j = Some x ->
                   ys !! j = Some y ->
                   S (uint.nat x) = uint.nat y⌝ ∗
                   ⌜continue = true -> b1 = true⌝ ∗
                   ⌜∀ (j: nat), j < uint.nat i -> ∀ (x y: w64),
                   xs !! j = Some x ->
                   ys !! j = Some y ->
                   (S (uint.nat x) ≠ uint.nat y)
                   -> b2 = true⌝
                )%I (* Should it be there exists *)
               with "[] [Hx Hy H3 H4 H5 H6]").
    - admit. (* iIntros (?). iModIntro. iIntros "H H1".
      iNamed "H". iDestruct "H" as "(output & canApply & index & l & %H1 & %H2 & %H3 & %H4 & %H5 & %H6 & %H7 & %H8 & %H9)".
      iDestruct "Hx" as "[Hxs Hxcap]".
      iDestruct "Hy" as "[Hys Hycap]".
      wp_pures. wp_load. wp_load. wp_if_destruct.
      + assert (uint.nat i < length xs)%nat by word.
        assert (uint.nat i < length ys)%nat by word.
        eapply list_lookup_lt in H0 as [x0 H0].
        eapply list_lookup_lt in H10 as [y0 H10].
        wp_pures. wp_load. wp_bind (if: #b2 then _ else _)%E.
        wp_if_destruct.
        * wp_load.
          wp_apply (wp_SliceGet with "[Hxs]"); iFrame; auto.
          iIntros "Hxs". wp_load. wp_apply (wp_SliceGet with "[Hys]"); iFrame; auto.
          iIntros "Hys". wp_pures. wp_if_destruct.
          { wp_store. wp_load. wp_store. iModIntro. iApply "H1".
            iExists b1. iExists false. iExists (W64 (uint.Z i + 1)).
            iFrame. repeat iSplitL; try word.
            - iPureIntro. intros.
              destruct (decide (j = uint.nat i)).
              + subst. rewrite H0 in H12. rewrite H10 in H13.
                injection H12 as ?. injection H13 as ?. subst.
                assert (S (uint.nat x1) = uint.nat (w64_word_instance.(word.add) x1 (W64 1))) by word.
                rewrite H12 in H14. word.
              + assert (j < uint.nat i) by word. eapply H4.
                * eassumption.
                * eassumption.
                * eassumption.
                * auto.
            - iPureIntro. intros.
              destruct (decide (j = uint.nat i)).
              + subst. rewrite H0 in H12. rewrite H10 in H13.
                injection H12 as ?. injection H13 as ?. subst.
                destruct H14.
                * admit.
                * destruct H12. inversion H12.
              + assert (j < uint.nat i) by word. eapply H5.
                * eassumption.
                * eassumption.
                * eassumption.
                * destruct H14.
                  { left. auto. }
                  { destruct H14. inversion H14. }
            - iPureIntro. intros. destruct H9.
              
              + 
          } 
          { wp_load. wp_apply (wp_SliceGet with "[Hxs]"); iFrame; auto.
            iIntros "Hxs". wp_load. wp_apply (wp_SliceGet with "[Hys]"); iFrame; auto.
            iIntros "Hys". wp_if_destruct.
            - wp_store. wp_load. wp_store. iModIntro. iApply "H1".
              iExists false. iExists true. iExists (W64 (uint.Z i + 1)). iFrame. iSplitL.
              + word.
              + iSplitL.
                * word.
                * iPureIntro. intros.
                  split.
                  -- intros. destruct (decide (j = uint.nat i)).
                     ++ subst. rewrite H0 in H12. rewrite H10 in H13. injection H12 as ?.
                        injection H13 as ?. subst. admit. (* should be provable *)
                     ++ eapply H3.
                        ** assert (j < uint.nat i) by word. eassumption.
                        ** eassumption.
                        ** eassumption.
                        ** eassumption.
                  -- split; auto.
                     split.
                     ++ intros. destruct (decide (j = uint.nat i)).
                        ** subst. rewrite H0 in H12. rewrite H10 in H13. injection H12 as ?.
                           injection H13 as ?. subst. destruct H14.
                           { word. }
                           { destruct H12. admit. }
                        ** assert (j < uint.nat i) by word. 
                           eapply H8 in H0 as H16.
                           { rewrite H16 in H5. 
                             eapply H5; try eassumption. }
                           { eassumption. }
                           (* every admit before this point should be true *)
                           { assert (uint.Z x0 + 1 ≠ uint.Z y0) by admit.
                             word. }
                     ++ split.
                        ** intros. destruct (decide (j = uint.nat i)).
                           { subst. rewrite H0 in H13. rewrite H10 in H14. injection H13 as ?. injection H14 as ?.
                             subst.
                             assert (uint.Z x1 + 1 ≠ uint.Z y1) by admit.
                             word. }
                           { assert (j < uint.nat i) by word. eapply H6; eassumption. }
                        ** split.
                           { intros. apply nil_length_inv in H11.  subst. inversion H0. }
                           { split; auto. intros. eapply H8 in H0.
                             - assert (S uint.nat x0 < uint.nat y0) by admit.

                             
                           
                           
                          
                             
                             - (* This is not inductive, we should be able to reach a contradiction somehow *)
                           (* I don't think we can prove that false = true,
                              prior to (j < uint.nat i) the invariant b1 = true is maintained
                              look at some examples to figure this out
                            *)
                           
                           
                           
                           
          }
        * wp_pures. wp_load. wp_apply (wp_SliceGet with "[Hxs]"); iFrame; auto.
          iIntros "Hxs". wp_load. wp_apply (wp_SliceGet with "[Hys]"); iFrame; auto.
          iIntros "Hys". wp_pures. wp_if_destruct.
          { wp_store. wp_load. wp_store. iModIntro. iApply "H1".
            iExists false. iExists false. iExists (W64 (uint.Z i + 1)). 
            iFrame. iSplitL; auto.
            - admit.
            - admit.
          }
          { wp_load. wp_store. iModIntro. iApply "H1".
            iExists b1. iExists false. iExists (W64 (uint.Z i + 1)). 
            iFrame. iSplitL; auto; admit. (* word. *)
          }
      + iModIntro. iApply "H1".
        iExists b1. iExists b2. iExists i.
        iFrame. iSplitL; auto. iSplitL.
        * word.
        * iPureIntro. auto. *) 
    - iExists true. iExists true. iExists (W64 0). 
      replace (W64 (length xs)) with (x.(Slice.sz)) by word. iFrame.
      iSplitL.
      + word.
      + iSplitL.
        * iPureIntro. word.
        * iPureIntro. split; try word. split; try word. split; try word.
          split; try word. split; try word. split; try word. split; try word.
          split; try word. split; try word.
    - iIntros "(%b1 & %b2 & %i & Hx & Hy & output & canApply & index & l & %H5 & %H6 & %H7 & %H8 & %H9 & %H10 & %H11 & %H12 & %H13 & %H14 & %H15)".
      wp_pures. wp_load.
      + iModIntro. iApply "H2".
        iFrame. iPureIntro. split; auto.
        rewrite /coq_oneOffVersionVector.
        clear Hsz.
        simpl. generalize dependent ys. generalize dependent i.
        induction xs.
        * intros. simpl. simpl in H5. assert (uint.nat i = 0%nat) by word. destruct H11.
          { auto. }
          { auto. }
        * induction ys.
          -- intros. inversion H.
          -- intros. simpl. destruct (decide (uint.Z a + 1 =? uint.Z a0 = true)).
             ++ rewrite e. fold coq_oneOffVersionVector in *.
                clear IHys. clear IHxs.
                generalize dependent ys. generalize dependent i. induction xs.
                ** intros.
                   simpl. simpl in H.
                   assert (length ys = 0%nat) by word.
                   apply nil_length_inv in H0.
                   destruct (decide (uint.nat i = 0%nat)).
                   { subst. eapply H12.
                     - rewrite e0. auto.
                     - rewrite e0. auto.
                     - admit.
                   }
                   { rewrite length_cons in H5. simpl in H5. 
                     assert (uint.nat i = 1%nat) by word.
                     destruct H6; auto.
                     - destruct H1. simpl in H2. admit.
                     - destruct H1. destruct H2; auto.
                   }
                ** intros. induction ys.
                   { intros. inversion H. }
                   { simpl. destruct (decide (uint.Z a1 <? uint.Z a2 = false)).
                     - rewrite e0. simpl. clear IHys. apply (IHxs (uint.nat i - 1)). 
                       + admit.
                       + intros. destruct H6; auto.
                         * left. destruct H1. admit.
                         * right. admit.
                       + intros. eapply H11. admit.
                       + auto.
                       + intros. admit.
                       + admit.
                       + admit.
                       + admit.
                       + admit.
                       + admit.
                       + admit.
                       + admit.
                     - assert ((uint.Z a1 <? uint.Z a2) = true) by word. rewrite H0.
                       destruct H6; auto.
                       + destruct H1; auto.
                       + destruct H1. symmetry in H1. eapply H13.
                         * repeat rewrite length_cons in H1.
                           assert (1%nat < uint.nat i) by word.
                           eassumption. 
                         * auto.
                         * auto.
                         * left. split.
                           { eapply H7.
                             - repeat rewrite length_cons in H1.
                               assert (0%nat < uint.nat i) by word.
                               eassumption.
                             - auto.
                             - auto.
                             - word.
                           }  word.
                   }
             ++ assert ((uint.Z a + 1 =? uint.Z a0) = false) by word. rewrite H0.
                destruct (decide (uint.Z a <? uint.Z a0 = false)).
                ** rewrite e. fold coq_oneOffVersionVector in *. apply (IHxs (uint.nat i - 1)); admit.
                ** assert ((uint.Z a <? uint.Z a0) = true) by word. rewrite H1.
                   admit.
                   
  Admitted.

  Definition is_sorted (l: list Operation.t) :=
    ∀ (i j: nat), (i < j)%nat ->
                  ∀ (o1 o2: Operation.t), l !! i = Some o1 ->
                                          l !! j = Some o2 ->
                                          coq_lexiographicCompare (o2.(Operation.VersionVector)) (o1.(Operation.VersionVector)) = true \/ coq_equalSlices (o2.(Operation.VersionVector)) (o1.(Operation.VersionVector)) = true.
  
  Lemma implies_Sorted :
    forall (l: list Operation.t) (element: Operation.t) (i: u64),
    is_sorted l ->
    uint.nat i <= length l ->
    (∀ (i': nat), i' < uint.nat i ->
                  ∀ (x: Operation.t), l !! i' = Some x ->
                                      coq_lexiographicCompare
                                        (element.(Operation.VersionVector)) (x.(Operation.VersionVector)) = true) -> 
    (∀ (j': nat),
       uint.nat i ≤ j' →
       ∀ (y: Operation.t), l !! j' = Some y →
                           coq_lexiographicCompare (y.(Operation.VersionVector)) (element.(Operation.VersionVector)) = true \/ coq_equalSlices (y.(Operation.VersionVector)) (element.(Operation.VersionVector)) = true) ->
    is_sorted ((take (uint.nat i) l) ++ (cons element (drop (uint.nat i) l))).
  Proof.
    rewrite /is_sorted. intros.
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
             left. eapply H1; try eassumption.
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
                ** assert (uint.nat i <= (uint.nat i + Init.Nat.pred (j - length (take (uint.nat i) l)))%nat) by word. apply H9. 
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
                ** assert (i0 < (uint.nat i + Init.Nat.pred (j - length (take (uint.nat i) l)))%nat)%nat by word. apply H9.
                ** auto.
                ** auto.
  Qed.
  
  Lemma wp_BinarySearch (s: Slice.t) (l: list Operation.t)
    (opv: Slice.t*u64) (needle: Operation.t) (n: nat) :
    {{{
          operation_slice s l n ∗
          is_operation opv (DfracOwn 1) needle n ∗
          ⌜is_sorted l⌝
    }}}
      binarySearch s (operation_val opv)
      {{{ (i: u64) , RET #i ;
          operation_slice s l n ∗
          is_operation opv (DfracOwn 1) needle n ∗
          ⌜is_sorted l⌝ ∗
          ⌜ ∀ (i': nat), i' < uint.nat i -> ∀ (x: Operation.t), l !! i' = Some x -> coq_lexiographicCompare (needle.(Operation.VersionVector)) (x.(Operation.VersionVector)) = true⌝ ∗
                                                                ⌜∀ (j': nat), uint.nat i ≤ j' -> ∀ (y: Operation.t), l !! j' = Some y -> coq_lexiographicCompare (y.(Operation.VersionVector)) (needle.(Operation.VersionVector)) = true \/ coq_equalSlices (y.(Operation.VersionVector)) (needle.(Operation.VersionVector)) = true⌝ ∗
                                                                                                                     ⌜uint.nat i <= length l⌝
      }}}.
  Proof.
    iIntros (Φ) "(H & H1 & %H2) H4". unfold binarySearch.
      wp_pures.
      wp_apply wp_ref_to; auto.
      iIntros (i_l) "i". wp_pures.
      wp_apply wp_slice_len.
      wp_apply wp_ref_to; auto.
      iIntros (j_l) "j". wp_pures.
      iNamed "H".
      iDestruct "H" as "(H & H2)".
      iDestruct "H" as "(H & H3)".
      iDestruct (big_sepL2_length with "H2") as "%len".
      iDestruct (slice.own_slice_small_sz with "H") as %Hsz.
      wp_apply (wp_forBreak_cond
                  (λ continue, ∃ (i j: w64),
                      operation_slice s l n ∗
                      is_operation opv (DfracOwn 1) needle n ∗
                      i_l ↦[uint64T] #i ∗
                      j_l ↦[uint64T] #j ∗
                      ⌜uint.Z i ≤ uint.Z j ≤ Z.of_nat (length l)⌝ ∗
                      ⌜∀ (i': nat),
                     i' < uint.nat i →
                     ∀ (x: Operation.t), l !! i' = Some x -> coq_lexiographicCompare (needle.(Operation.VersionVector)) (x.(Operation.VersionVector)) = true⌝ ∗
                                         ⌜∀ (j': nat),
                     uint.nat j ≤ j' →
                     ∀ (y: Operation.t), l !! j' = Some y ->
                                         coq_lexiographicCompare (y.(Operation.VersionVector)) (needle.(Operation.VersionVector)) = true \/ coq_equalSlices (y.(Operation.VersionVector)) (needle.(Operation.VersionVector)) = true⌝ ∗
                                         ⌜continue = false → i = j⌝ ∗
                                         ⌜uint.nat i <= length l⌝ 
                  )%I
                 with "[] [H H1 H2 H3 i j]").
      - iIntros (?). iModIntro. iIntros "H1 H2".
        wp_pures. iNamed "H1".
        iDestruct "H1" as "(H & H1 & H3 & H4 & %H5 & %H6 & %H7)".
        wp_load. wp_load.
        wp_if_destruct.
        + wp_pures.
          wp_load. wp_load. wp_load. wp_pures.
          set (mid := word.add i (word.divu (word.sub j i) (W64 2)) : w64).
          assert (uint.Z mid = (uint.Z i + uint.Z j) / 2) as Hmid_ok.
          { subst mid.
            word. }
          list_elem l (uint.nat mid) as x_mid.
          iNamed "H".
          iDestruct "H" as "(H & H5)".
          iDestruct "H" as "(H & H6)".
          iDestruct (big_sepL2_length with "H5") as "%H8".
          assert (length (list.untype ops0) = length ops0). {
            apply list_untype_length. }
          assert (uint.nat mid < length (list.untype ops0))%nat by word.
          assert (uint.nat mid < length ops0)%nat by word.
          apply list_lookup_lt in H0.
          apply list_lookup_lt in H1.
          destruct H0.
          destruct H1.
          wp_apply (slice.wp_SliceGet with "[H]").
          * unfold own_slice_small. simpl. iSplitL.
            { iFrame. }
            { iPureIntro. apply H0. }
          * iIntros "(H & %H3)". wp_pures.
            wp_bind (lexiographicCompare _ _).
            wp_pures. unfold operation_val.
            iDestruct (big_sepL2_insert_acc _ _ _ _ _ _ H1 Hx_mid_lookup with "H5")
              as "[H7 H8]".
            destruct x_mid as [a b].
            apply untype_lookup_Some in H0.
            destruct H0. destruct H0.
            assert (x0 = x1). {
              rewrite H0 in H1. inversion H1. auto. }
            rewrite H4.
            iDestruct "H7" as "(#H7 & %H10 & #H10)".
            iDestruct "H1" as "(H1 & %H11 & H12)".
            wp_apply (wp_lexiographicCompare with "[H12]").
            { unfold is_operation.
              iSplitL "H12".
              - iFrame.
              - iSplitL.
                + rewrite H9. iApply "H10".
                + rewrite <- H11. word.
            }
            iIntros (r) "(%H13 & H5 & H14 & H15)".
            wp_if_destruct.
            { wp_store. iModIntro. iApply "H2".
              iExists (W64 (uint.Z mid + 1)). 
              iExists (j).
              iFrame.
              remember ({| Operation.VersionVector := a; Operation.Data := b |}) as t0.
              iAssert (⌜t0 = {| Operation.VersionVector := a; Operation.Data := b |}⌝)%I as "H".
              { iPureIntro. auto. }
              iSpecialize ("H8" with "[H14 H10 H]"). {
                iAssert (□ is_operation x0 (DfracOwn 1) t0 n)%I with "[H14 H10]" as "H1". {
                  rewrite /is_operation. iSplitL.
                  - iApply "H7".
                  - iSplitL.
                    + word.
                    + iApply "H10". }
                iApply "H1". }
              iSplitL.
              - rewrite Heqt0. simpl in *. assert (<[uint.nat mid:=x1]> ops0 = ops0). {
                  apply list_insert_id. auto.
                }
                assert (<[uint.nat mid:={| Operation.VersionVector := a; Operation.Data := b |}]> l = l).
                { apply list_insert_id. rewrite <- Heqt0. auto. }
                rewrite H14. subst. rewrite H12. iFrame.
              - iPureIntro.
                split; try word. split. 
                + intros. unfold is_sorted in H2.
                  assert (coq_lexiographicCompare needle.(Operation.VersionVector) t0.(Operation.VersionVector) = true).
                  {
                    symmetry. auto.
                  }
                  word.
                + split.
                  * intros.
                  destruct (decide ((i' < uint.nat mid)%nat)).
                  { unfold is_sorted in H2.
                    apply (H2 i' (uint.nat mid) l0 x2 t0) in H14; try eassumption.
                    destruct H14.
                    { eapply aux0_lexiographicCompare; try eassumption. symmetry. auto. }
                    { rewrite H10 in H11.
                      symmetry.
                      apply aux0_equalSlices in H14; auto.
                      - rewrite <- H14. auto.
                      - admit.
                    }
                  }
                  { assert (i' <= uint.nat mid)%nat by word.
                    assert (i' = uint.nat mid) by word. subst.
                    rewrite Hx_mid_lookup in H14. injection H14 as ?.
                    rewrite H4 in H13. auto.
                  }
                  * split; try word.
                    intros. eapply H7; try eassumption.
            }
            {
              wp_store.
              iModIntro.
              iApply "H2".
              iExists i.
              iExists mid.
              iFrame.
              remember ({| Operation.VersionVector := a; Operation.Data := b |}) as t0.
              iAssert (⌜t0 = {| Operation.VersionVector := a; Operation.Data := b |}⌝)%I as "H".
              { iPureIntro. auto. }
              iSpecialize ("H8" with "[H14 H10 H]"). {
                iAssert (□ is_operation x0 (DfracOwn 1) t0 n)%I with "[H14 H10]" as "H1". {
                  rewrite /is_operation. iSplitL.
                  - iApply "H7".
                  - iSplitL.
                    + word.
                    + iApply "H10". }
                iApply "H1". }
              iSplitL.
              - rewrite Heqt0. simpl in *. assert (<[uint.nat mid:=x1]> ops0 = ops0). {
                  apply list_insert_id. auto.
                }
                assert (<[uint.nat mid:={| Operation.VersionVector := a; Operation.Data := b |}]> l = l).
                { apply list_insert_id. rewrite <- Heqt0. auto. }
                rewrite H14. subst. rewrite H12. iFrame.
              - iPureIntro.
                split_and!; try word.
                { auto. }
                intros. unfold is_sorted in *. 
                assert (coq_lexiographicCompare needle.(Operation.VersionVector) t0.(Operation.VersionVector) = false).
                {
                  symmetry. auto.
                }
                destruct (decide (uint.nat mid = j')).
                + rewrite e in Hx_mid_lookup. rewrite H14 in Hx_mid_lookup. injection Hx_mid_lookup as
                  ?. subst. destruct (decide (coq_equalSlices {| Operation.VersionVector := a; Operation.Data := b |}.(Operation.VersionVector) needle.(Operation.VersionVector) = true)).
                  * right. auto.
                  * left. apply aux1_lexiographicCompare; auto. apply aux1_equalSlices; auto.
                    admit.
                + assert (uint.nat mid < j')%nat by word.
                  left.
                  eapply (H2 (uint.nat mid) j' H16 t0 y) in H14.
                  * destruct (decide (coq_equalSlices {| Operation.VersionVector := a; Operation.Data := b |}.(Operation.VersionVector) needle.(Operation.VersionVector) = true)); admit.
                  * auto.
            }
        + iModIntro.
        iApply "H2".
        iFrame.
        iPureIntro.
        split_and!; try word; auto.
          * destruct H7. auto.
          * intros. word.
    - iFrame. iPureIntro.
      split; try word.
      + admit. (* length reasoning *)
      + split; try word.
        split; try word.
        intros. apply lookup_lt_Some in H0.
        assert (length ops = length (list.untype ops)). {
          symmetry. apply list_untype_length. } word.
    - iIntros "Hpost".
      wp_pures. iNamed "Hpost". iDestruct "Hpost" as "(H2 & H3 & H5 & H6 & %H7 & %H8 & %H9 & %H10)".
      wp_load. wp_pures. 
      (* iApply "H4". iFrame. iPureIntro. split; auto.
      split; auto. split.
      + intros. destruct H10. assert (false = false) by auto. apply H1 in H4. rewrite H4 in H.
        eapply H9; eassumption.
      + destruct H10. auto. *)
    Admitted. 

  Fixpoint coq_sortedInsert (l : list Operation.t) (i : Operation.t) :=
    match l with
    | [] => [i]
    | cons h t => if (coq_lexiographicCompare h.(Operation.VersionVector) i.(Operation.VersionVector)) then (i :: h :: t)%list else (h :: coq_sortedInsert t i)%list
    end.

  Lemma wp_insert (s: Slice.t) (l: list Operation.t)
    (opv: Slice.t*u64) (v: Operation.t) (n: nat) :
      {{{
            operation_slice s l n ∗
            is_operation opv (DfracOwn 1) v n ∗
            ⌜is_sorted l⌝ 
      }}}
        sortedInsert s (operation_val opv)
      {{{ (ns: Slice.t), RET slice_val (ns);
          ∃ nxs, operation_slice ns nxs n %I ∗
                 ⌜nxs = coq_sortedInsert l v⌝
      }}}.
  Proof.
  Admitted.

  Definition coq_equalOperations (o1 : Operation.t) (o2 : Operation.t) :=
  (coq_equalSlices o1.(Operation.VersionVector) o2.(Operation.VersionVector)) && ((uint.nat o1.(Operation.Data)) =? (uint.nat (o2.(Operation.Data)))).

  Definition coq_mergeOperations (l1: list Operation.t) (l2: list Operation.t) : (list Operation.t) :=
  let output := fold_left (fun acc element => coq_sortedInsert acc element) l1 l2 in
  snd (fold_left (fun (acc: Z * list Operation.t) element =>
                    let (index, acc) := acc in
                    match (output !! (uint.nat (index - 1))) with
                    | Some v => if (coq_equalOperations element v) then
                                  (index + 1, acc)
                                else
                                  (index + 1, (element :: acc)%list)
                    | None => (index + 1, (element :: acc)%list)
                    end) output (0, [])).

  (* Fix goose for bsearch *)
  
  Lemma wp_mergeOperations (opv: Slice.t*u64) (v: Operation.t) (n: nat) :
      {{{
            is_operation opv (DfracOwn 1) v n 
      }}}
      operationList (operation_val opv)
      {{{
            (ns: Slice.t), RET slice_val (ns);
            ∃ nxs, operation_slice ns nxs n 
      }}}.
  Proof.
    iIntros (Φ) "(#H & #H1 & Hb) H2".
    rewrite /operationList.
    iDestruct "Hb" as "[Hr Ha]".
    iMod (slice.own_slice_small_persist with "[Hr]") as "#Hs"; auto.
    wp_pures.
    wp_apply (wp_NewSlice).
    iIntros (s) "H3".
    Search "own_slice_cap".
    (* change proofs s.t. it only includes own_slice_small *)
    iAssert (□ (own_slice_cap opv.1 uint64T))%I as "H10".  {

    wp_pures.
    unfold operation_val. simpl.
    wp_apply (wp_SliceAppend' with "[H3]"); auto.
    iIntros (s1) "H3".
    iApply "H2".
    iExists [v].
    unfold operation_slice.
    unfold operation_slice'.
    Search "own_slice".
    Search "own_slice_cap".
    iExists ([(opv.1, opv.2)]).
    iFrame. unfold is_operation.
    simpl. iSplitL.
    - unfold own_slice. unfold slice.own_slice.
      
      iSplitL.
      * iModIntro. iApply "H".
      * iSplitL.
        {iModIntro. iApply "H1". }
        { iFrame.
      iModIntro. unfold own_slice.
      
    - auto.
  Qed.
    
    
      
    
    
