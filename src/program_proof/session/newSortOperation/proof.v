From Goose.github_com.session Require Import sort operations.
From Perennial.program_proof Require Import std_proof. 
From Perennial.goose_lang.ffi.grove_ffi Require Export impl.
From Perennial.program_logic Require Export atomic.
From Perennial.program_proof Require Export proof_prelude.
From Perennial.program_proof Require Import grove_prelude.
From RecordUpdate Require Import RecordSet.
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang.lib.list Require Import list.
From Perennial.goose_lang.lib Require Import map.impl list.impl list.list_slice slice.typed_slice.

Module operation.
  Section operation.

    Lemma struct_ty_operation_unfold :
      struct.t Operation = (uint64T * (slice.T uint64T * (uint64T * unitT)))%ht.
    Proof. reflexivity. Qed.

    Search "w64".
    Record t :=
      mk {
          operationType: u64 ;
          versionVector: list u64 ;
          data: u64 ;
        }.

  End operation.

  Section heap.
    Context `{hG: !heapGS Σ}.

     Definition operation_val (op:u64*Slice.t*u64): val :=
      (#op.1.1, ((slice_val op.1.2), (#op.2, #())))%V.

    Theorem operation_val_t op : val_ty (operation_val op) (struct.t Operation).
    Proof.
      repeat constructor.
      destruct op. simpl.
      val_ty.
    Qed.

    Hint Resolve operation_val_t : core.

    Global Instance operation_into_val : IntoVal (u64*Slice.t*u64).
    Proof.
      refine {| into_val.to_val := operation_val;
               from_val := λ v, match v with
                                | (#(LitInt a), (slice_v, (#(LitInt b), #())))%V =>
                                    match from_val slice_v with
                                    | Some s => Some (a, s, b)
                                    | None => None
                                    end
                                | _ => None
                                end;
               IntoVal_def := (W64 0, IntoVal_def Slice.t, W64 0);
             |}.
      destruct v as [[a []] c] ; done.
    Defined. 

    #[global] Instance into_val_for_type : IntoValForType (u64*Slice.t*u64) (struct.t Operation).
    Proof. constructor; auto. Qed.
    
    Definition is_operation (opv: u64*Slice.t*u64) (q:dfrac) (op: operation.t): iProp Σ :=
      (⌜opv.1.1 = op.(operationType)⌝ ∗
       ⌜opv.2 = op.(data)⌝ ∗
       own_slice opv.1.2 uint64T q op.(versionVector))%I.

    Definition operation_slice' q (op_s: Slice.t) (op: list operation.t): iProp Σ :=
      ∃ ops , own_slice op_s (struct.t Operation) (DfracOwn 1) (ops) ∗
              [∗ list] _ ↦ opv;o ∈ ops;op , let '(operation.mk a b c) := o in
                                            own_slice (opv.1.2) (uint64T) q b ∗
                                            ⌜opv.1.1 = a⌝ ∗
                                            ⌜opv.2 = c⌝.

    (* How can I bake in addition assumptions such as the length of each of the version
     vectors *)
    (* How do I instantiate an operation_slice ? *)
    Definition operation_slice (s: Slice.t) (ls: list operation.t): iProp Σ :=
      operation_slice' (DfracOwn 1) s ls.

    Lemma val_to_op_with_val_ty (x : val) :
      val_ty x (uint64T * (slice.T uint64T * (uint64T * unitT)))%ht->
      (∃ (t : u64) (s : Slice.t) (d : u64), x = operation_val (t, s, d)).
    Proof.
      intros.
      inversion_clear H.
      { inversion_clear H0. }
      inversion_clear H0.
      inversion_clear H.
      inversion_clear H1.
      { inversion_clear H. }
      inversion_clear H0.
      { inversion_clear H1. }
      inversion_clear H1.
      inversion_clear H0. 
      inversion_clear H2.
      exists x0.
    Admitted.
    
    (* 
    Definition op := (u64 * list u64 * u64)%type.
    
    Fixpoint val_of_list (l: list val) : val :=
      match l with
      | nil => InjLV (LitV LitUnit)
      | (v :: l)%list => InjRV (PairV v (val_of_list l))
      end.

    Definition op_to_val (x : op) :=
      (#x.1.1, ((val_of_list ((λ (y: u64), #y) <$> x.1.2)), (#x.2, #())))%V.

    Lemma val_to_op_with_val_ty (x : val) :
      val_ty x (uint64T * (slice.T uint64T * (uint64T * unitT)))%ht->
      (∃ (t : u64) (v : list u64) (d : u64), x = op_to_val (t, v, d)).
    Proof.
      Admitted.
    
     *)

    (* ./mvcc/tuple_read_version.v *)
    (* ./program_proof/wal/circ_proof.v *)

    Fixpoint coq_equalSlices (s1: list u64) (s2: list u64) :=
      match s1 with
      | [] => true
      | cons h1 t1 => match s2 with
                      | [] => true
                      | cons h2 t2 => if (negb ((uint.Z h1) =? (uint.Z h2)))
                                      then false else (coq_equalSlices t1 t2)
                      end
      end.

    Lemma equality_coq_equalSlices s1 s2 :
      length s1 = length s2 ->
      coq_equalSlices s1 s2 = true ->
      s1 = s2.
    Proof.
    Admitted.

    Definition coq_equalOperations (o1 o2: operation.t) :=
      (andb (andb (uint.Z o1.(operation.operationType) =? uint.Z o2.(operation.operationType))
               (coq_equalSlices o1.(operation.versionVector) o2.(operation.versionVector)))
         ((uint.Z o1.(operation.data) =? uint.Z o2.(operation.data)))).

    Definition operation_to_val (o: operation.t) (s: Slice.t) :=
      (#o.(operationType), (s, (#o.(data), #())))%V.

    Fixpoint coq_lexiographicCompare (v1 v2: list u64) : bool :=
      match v1 with
      | [] => false (* This will never happen since v1 and v2 should be unique lists *)
      | cons h1 t1 => match v2 with
                      | [] => false (* This will never happen since they are the same length *)
                      | cons h2 t2 => if (uint.Z h1) =? (uint.Z h2) then
                                        (coq_lexiographicCompare t1 t2) else (uint.Z h1) >? (uint.Z h2)
                      end
      end.

    Lemma transitive_coq_lexiographicCompare (v1 v2 v3: list u64) :
      coq_lexiographicCompare v2 v1 = true ->
      coq_lexiographicCompare v3 v2 = true ->
      coq_lexiographicCompare v3 v1 = true.
    Proof.
      intros.
      (* unfold coq_lexiographicCompare in *. *)
      induction v2.
      - inversion H.
      - induction v3.
        + inversion H0.
    Admitted.

    (* Maybe we can alter this so we don't have to consider that v1 and v2 are unique *)
    Lemma flip_coq_lexiographicCompare (v1 v2: list u64) :
      length v1 = length v2 -> 
      (coq_lexiographicCompare v2 v1 = false <->
                                         coq_lexiographicCompare v1 v2 = true).
    Proof.
    Admitted.
    (*
      intros. unfold coq_lexiographicCompare in *.
      generalize dependent v2.
      induction v1.
      - auto.
      - induction v2.
        + auto.
        + destruct (decide (uint.Z a =? uint.Z a0 = true)).
          * rewrite e. intros. apply IHv1.
            { auto. }
            { fold coq_lexiographicCompare. assert (uint.Z a0 =? uint.Z a = true) by word.
              rewrite H1 in H0. simpl in H0. auto. }
          * assert (uint.Z a =? uint.Z a0 = false) by word. rewrite H. intros.
            assert (uint.Z a0 =? uint.Z a = false) by word. rewrite H2 in H1. word.
    Qed.
     *)
    
    Lemma wp_lexiographicCompare (x: Slice.t) (xs: list u64) (y: Slice.t) (ys: list u64) :
      {{{
            own_slice x uint64T (DfracOwn 1) xs ∗
            own_slice y uint64T (DfracOwn 1) ys ∗
            ⌜length xs = length ys⌝ ∗
            ⌜length xs < 2^64⌝
      }}}
        lexiographicCompare x y 
        {{{
              r , RET #r;
              ⌜r = coq_lexiographicCompare xs ys⌝ ∗ 
              own_slice x uint64T (DfracOwn 1) xs ∗
              own_slice y uint64T (DfracOwn 1) ys ∗
              ⌜length xs = length ys⌝ ∗
              ⌜length xs < 2^64⌝
        }}}.
    Proof.
    Admitted.
    
    Definition is_sorted (l: list operation.t) :=
      ∀ (i j: nat), (i < j)%nat ->
                    ∀ (o1 o2: operation.t), l !! i = Some o1 ->
                                            l !! j = Some o2 ->
                                            coq_lexiographicCompare
                                              (o2.(versionVector)) (o1.(versionVector)) = true \/
                                                                                            coq_equalSlices (o2.(versionVector)) (o1.(versionVector)) = true.
    
    Lemma implies_Sorted :
      forall (l: list operation.t) (element: operation.t) (i: u64),
      is_sorted l ->
      uint.nat i <= length l ->
      (∀ (i': nat), i' < uint.nat i ->
                    ∀ (x: operation.t), l !! i' = Some x ->
                               coq_lexiographicCompare
                                 (element.(versionVector)) (x.(versionVector)) = true) -> 
      (∀ (j': nat),
         uint.nat i ≤ j' →
         ∀ (y: operation.t), l !! j' = Some y →
                             coq_lexiographicCompare (y.(versionVector)) (element.(versionVector)) = true \/ coq_equalSlices (y.(versionVector)) (element.(versionVector)) = true) ->
      is_sorted ((take (uint.nat i) l) ++ (cons element (drop (uint.nat i) l))).
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

    (* Basically the same thing as is_operation except that the fields are not in tuple
     format *)
    (*
    Definition operation_equiv
      (op: operation.t) (t: u64) (s: Slice.t) (d: u64) :=
      (⌜op.(operationType) = t⌝ ∗
       own_slice s (uint64T) (DfracOwn 1) (op.(versionVector)) ∗
       ⌜op.(data) = d⌝)%I.
     *)

    Lemma wp_BinarySearch (s: Slice.t) (l: list operation.t)
      (opv: u64*Slice.t*u64) (needle: operation.t) :
      {{{
            operation_slice s l ∗
            is_operation opv (DfracOwn 1) needle ∗
            ⌜is_sorted l⌝
      }}}
        binarySearch s (operation_val opv)
        {{{ (i: u64) , RET #i ;
            operation_slice s l ∗
            is_operation opv (DfracOwn 1) needle ∗
            ⌜is_sorted l⌝ ∗
            ⌜ ∀ (i': nat), i' < uint.nat i ->
                           ∀ (x: operation.t), l !! i' = Some x -> 
                                               coq_lexiographicCompare (needle.(versionVector)) (x.(versionVector)) = true⌝ ∗ ⌜∀ (j': nat),
              uint.nat i ≤ j' →
              ∀ (y: operation.t), l !! j' = Some y -> 
                                  coq_lexiographicCompare (y.(versionVector)) (needle.(versionVector)) = true \/ coq_equalSlices (y.(versionVector)) (needle.(versionVector)) = true⌝ ∗
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
                      operation_slice s l ∗
                      is_operation opv (DfracOwn 1) needle ∗
                      i_l ↦[uint64T] #i ∗
                      j_l ↦[uint64T] #j ∗
                      ⌜uint.Z i ≤ uint.Z j ≤ Z.of_nat (length l)⌝ ∗
                      ⌜∀ (i': nat),
                     i' < uint.nat i →
                     ∀ (x: operation.t), l !! i' = Some x -> coq_lexiographicCompare (needle.(versionVector)) (x.(versionVector)) = true⌝ ∗
                                         ⌜∀ (j': nat),
                     uint.nat j ≤ j' →
                     ∀ (y: operation.t), l !! j' = Some y ->
                                         coq_lexiographicCompare (y.(versionVector)) (needle.(versionVector)) = true \/ coq_equalSlices (y.(versionVector)) (needle.(versionVector)) = true⌝ ∗
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
            destruct x_mid as [a b c].
            apply untype_lookup_Some in H0.
            destruct H0. destruct H0.
            assert (x0 = x1). {
              rewrite H0 in H1. inversion H1. auto. }
            rewrite H4.
            iDestruct "H7" as "(H7 & H9 & H10)".
            iDestruct "H1" as "(H1 & H11 & H12)".
            wp_apply (wp_lexiographicCompare with "[H7 H12]").
            { unfold is_operation. 
              iSplitL "H12".
              - iFrame.
              - iSplitL.
                + rewrite H9. iFrame.
                + admit.
            }
            iIntros (r) "(%H13 & H5 & H14 & H15)".
            wp_if_destruct.
            { wp_store. iModIntro. iApply "H2".
              iExists (W64 (uint.Z mid + 1)). 
              iExists (j).
              iFrame.
              remember ({| operationType := a; versionVector := b; data := c |}) as t0.
              iAssert (⌜t0 = {| operationType := a; versionVector := b; data := c |}⌝)%I as "H".
              { iPureIntro. auto. }
              iSpecialize ("H8" with "[H14 H10 H9 H]"). {
                iAssert (let
                            '{| operationType := a; versionVector := b; data := c |} := t0 in
                          own_slice x1.1.2 uint64T (DfracOwn 1) b ∗ ⌜x1.1.1 = a⌝ ∗ ⌜x1.2 = c⌝)%I with "[H14 H10 H9]" as "H1". {
                  rewrite Heqt0. rewrite <- H9. iFrame. }
                iApply "H1". }
              iSplitL.
              - rewrite Heqt0. simpl in *. assert (<[uint.nat mid:=x1]> ops0 = ops0). {
                  apply list_insert_id. auto.
                }
                assert (<[uint.nat mid:={| operationType := a; versionVector := b; data := c |}]> l = l).
                { apply list_insert_id. rewrite <- Heqt0. auto. }
                rewrite H10. rewrite H11. iFrame.
              - iPureIntro.
                split; try word. split. 
                + intros. unfold is_sorted in H2.
                  assert (coq_lexiographicCompare needle.(versionVector) t0.(versionVector) = true).
                  {
                    rewrite Heqt0. simpl. auto.
                  }
                  destruct (decide ((i' < uint.nat mid)%nat)).
                  * unfold is_sorted in H2.
                    apply (H2 i' (uint.nat mid) l0 x2 t0) in H11; try eassumption.
                    destruct H11.
                    { eapply transitive_coq_lexiographicCompare; try eassumption. }
                    { apply equality_coq_equalSlices in H11; auto.
                      - rewrite <- H11. auto.
                      - admit. }
                  * assert (i' <= uint.nat mid)%nat by word.
                    assert (i' = uint.nat mid) by word. rewrite H15 in H11.
                    rewrite Hx_mid_lookup in H11. injection H11 as ?.
                    rewrite H11 in H12. auto.
                + split; try word.
                  intros. destruct H7 as (H7 & H12 & H14).
                  eapply H7; try apply H10. auto.
            }
            {
              wp_store.
              iModIntro.
              iApply "H2".
              iExists i.
              iExists mid.
              iFrame.
              remember ({| operationType := a; versionVector := b; data := c |}) as t0.
              iAssert (⌜t0 = {| operationType := a; versionVector := b; data := c |}⌝)%I as "H".
              { iPureIntro. auto. }
              iSpecialize ("H8" with "[H14 H10 H9 H]"). {
                iAssert (let
                            '{| operationType := a; versionVector := b; data := c |} := t0 in
                          own_slice x1.1.2 uint64T (DfracOwn 1) b ∗ ⌜x1.1.1 = a⌝ ∗ ⌜x1.2 = c⌝)%I with "[H14 H10 H9]" as "H1". {
                  rewrite Heqt0. rewrite <- H9. iFrame. }
                iApply "H1". }
              iSplitL.
              - rewrite Heqt0. simpl in *. assert (<[uint.nat mid:=x1]> ops0 = ops0). {
                  apply list_insert_id. auto.
                }
                assert (<[uint.nat mid:={| operationType := a; versionVector := b; data := c |}]> l = l).
                { apply list_insert_id. rewrite <- Heqt0. auto. }
                rewrite H10. rewrite H11. iFrame.
              - iPureIntro.
                split_and!; try word.
                { auto. }
                intros. unfold is_sorted in *. 
                assert (coq_lexiographicCompare needle.(versionVector) t0.(versionVector) = false).
                {
                  rewrite Heqt0. simpl. auto.
                }
                destruct (decide (uint.nat mid = j')).
                + rewrite e in Hx_mid_lookup. rewrite H11 in Hx_mid_lookup. injection Hx_mid_lookup as
                  ?. rewrite H14. left.
                  apply flip_coq_lexiographicCompare.
                  * admit.
                  * auto.
                + assert (uint.nat mid < j')%nat by word.
                  left.
                  eapply (H2 (uint.nat mid) j' H14 t0 y) in H11.
                  * destruct H11.
                    { apply flip_coq_lexiographicCompare in H12.
                      - eapply transitive_coq_lexiographicCompare; eassumption.
                      - admit.
                    }
                    { eapply equality_coq_equalSlices in H11.
                      - rewrite H11. eapply flip_coq_lexiographicCompare in H12.
                        + auto.
                        + admit.
                      - admit.
                    }
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
      iModIntro. iApply "H4". iFrame. iPureIntro. split; auto.
      split; auto. split.
      + intros. destruct H10. assert (false = false) by auto. apply H1 in H4. rewrite H4 in H.
        eapply H9; eassumption.
      + destruct H10. auto.
    Admitted. 
                
  Lemma cons_append (A: Type) (x: list A) (e : A):
    [e] ++ x = cons e x.
  Proof.
    induction x.
    - auto.
    - simpl. auto.
  Qed.
  
  Fixpoint insert (l : list operation.t) (i : operation.t) :=
    match l with
    | [] => [i]
    | cons h t => if (coq_lexiographicCompare h.(versionVector) i.(versionVector)) then (i :: h :: t)%list else (h :: insert t i)%list
    end.

  
  (* Define the hoare triple that calls this *)
  Lemma wp_insert (s: Slice.t) (l: list operation.t)
    (opv: u64*Slice.t*u64) (v: operation.t) :
      {{{
            operation_slice s l ∗
            is_operation opv (DfracOwn 1) v ∗
            ⌜is_sorted l⌝ ∗ ⌜length l < 2^64⌝
      }}}
        sortedInsert s (operation_val opv)
      {{{ (ns: Slice.t), RET slice_val (ns);
          ∃ nxs, operation_slice ns nxs %I ∗
                 ⌜nxs = insert l v⌝
      }}}.
  Proof.
    iIntros (Φ) "(H & H1 & %H2 & %H3) H4". unfold sortedInsert. wp_pures.
    wp_apply (wp_BinarySearch with "[$H $H1]"); auto.
    iIntros (i) "(H & H1 & %H4 & %H5 & %H6 & %H7)". wp_pures.
    unfold operation_slice.
    unfold operation_slice'.
    iNamed "H".
    iDestruct "H" as "[H H2]".
    iDestruct (big_sepL2_length with "H2") as %len.
    iDestruct (own_slice_sz with "H") as %Hsz.
    assert (length l = uint.nat s.(Slice.sz)) by word.
    unfold slice.len. wp_pures.
    remember i.
    wp_if_destruct.
    - unfold operation_val. wp_pures. 
      wp_apply (wp_SliceAppend with "[$]"); auto.
      iIntros (s') "H".
      iApply "H4".
      iExists (l ++ [v]).
      iSplitL.
      + iExists (ops ++ [opv]).
        iFrame.
        unfold is_operation.
        iApply big_sepL2_singleton.
        destruct v as [a b c].
        iDestruct "H1" as "(H1 & H2 & H3)".
        iFrame.
      + apply (implies_Sorted l v (length l)) in H2; try word.
        * iPureIntro.
          unfold insert.
          replace (uint.nat (W64 (length l))) with (length l)%nat in H2 by word.
          rewrite <- H in H5.  rewrite <- H in H6.
          clear H7.
          clear len.
          clear Hsz.
          clear H.
          induction l; try auto.
          assert (coq_lexiographicCompare v.(versionVector) a.(versionVector) = true
                                                                                \/ coq_equalSlices v.(versionVector) a.(versionVector) = true). { 
            assert (0 < S (length l))%nat by word.
            eapply H2 in H.
            eapply H.
            - auto.
            - simpl. rewrite <- cons_append. simpl. rewrite lookup_app_r.
              + rewrite length_take_le; try word. 
              replace (length l - length l)%nat with 0%nat by word.
              simpl. auto.
              + rewrite length_take_le; try word.
          }
          destruct H.
          { apply flip_coq_lexiographicCompare in H.
            - rewrite H. fold insert. assert (l ++ [v] = insert l v). {
                apply IHl.
                - unfold is_sorted.
                  intros. unfold is_sorted in H2. eapply H2.
                  + assert ((S i < S j)%nat) by word. apply H8.
                  + auto.
                  + auto.
                - rewrite length_cons in H3. word.
                - unfold is_sorted. intros. eapply H4.
                  + assert (S i < S j)%nat by word. apply H8.
                  + auto.
                  + auto.
                - intros. eapply H5.
                  + assert (S i' < S (length l)) by word.
                    assert (length (a :: l) = S (length l)). {
                      rewrite length_cons. auto. }
                    rewrite H8. eassumption.
                  + auto.
                - intros. eapply H6.
                  + assert (S (length l) ≤ S j') by word.
                    assert (length (a :: l) = S (length l)). {
                      rewrite length_cons. auto. }
                    rewrite H8. eassumption.
                  + auto.
              }
              rewrite <- app_comm_cons. rewrite H0. auto.
            - admit.
          }
          { assert (coq_lexiographicCompare a.(versionVector) v.(versionVector) = false) by admit.
            (* comes from coq_equalSlices v.(versionVector) a.(versionVector) = true *)
            admit. (* same proof as above *)
          }
        * intros. eapply H5.
          { assert (i' < length l) by word. rewrite <- H.
            apply H8. }
          { auto. }
        * intros. eapply H6.
          { assert (length l <= j') by word. rewrite <- H.
            apply H8. }
          { auto. }
    - wp_bind (SliceAppendSlice _ _ _).
      wp_apply wp_SliceSkip; try word.
      unfold own_slice.
      unfold slice.own_slice.
      iDestruct (own_slice_wf with "H") as %Hcap.
      iDestruct "H" as "[H H5]".
      iDestruct (slice_small_split with "H") as "H".
      + assert (uint.Z i <= length ops) by word.
        eassumption.
      + iDestruct "H" as "[H H6]".
        wp_apply slice.wp_SliceSingleton; auto.
        iIntros (s0) "H7".
        wp_apply (wp_SliceAppendSlice with "[H7 H6]"); try auto.
        * unfold own_slice. iSplitL "H7".
          -- assert (list.untype [opv] = cons (operation_val opv) []). {
               auto.
             }
             rewrite <- H0. iFrame.
          -- subst. iFrame.
        * iIntros (s') "[H7 H8]". wp_pures. wp_bind (SliceAppendSlice _ _ _).
          wp_apply wp_SliceTake; try word.
          unfold own_slice. unfold slice.own_slice.
          iDestruct "H7" as "[H7 H9]".
          wp_apply (wp_SliceAppendSlice with "[H8 H5 H7 H]"); try auto.
          -- iAssert (own_slice_small (slice_skip s (uint64T * (slice.T uint64T * (uint64T * unitT))%ht) w) (uint64T * (slice.T uint64T * (uint64T * unitT))%ht) (DfracOwn 1)
                        (drop (uint.nat w) ops) ∗ own_slice_cap s (struct.t Operation))%I with "[H8 H5]" as "H1". { subst. iFrame. }
             iSplitL "H H1".
             ++ unfold own_slice. unfold slice.own_slice.
                iSplitR "H1".
                ** unfold own_slice_small. simpl. subst.
                   iFrame.
                ** iApply own_slice_cap_take; try word. iDestruct "H1" as "[H H1]". iFrame.
             ++ iFrame.
          -- iIntros (s'0) "H". wp_pures. iModIntro. iApply "H4".
             iExists (take (uint.nat i) l ++ [#v] ++ drop (uint.nat i) l).
             iSplitL.
             ++ iExists (take (uint.nat i) ops ++ [opv] ++ drop (uint.nat i) ops).
                unfold own_slice. unfold slice.own_slice. iDestruct "H" as "(H & H3)".
                subst. iFrame.
                unfold is_operation. admit.
             ++ iPureIntro.
                apply (implies_Sorted l v (uint.nat i)) in H2;
                  try word.
                ** clear len.
                   clear Hsz.
                   clear H4.
                   clear Heqb.
                   clear Hcap.
                   clear H.
                   subst.
                   generalize dependent i. induction l.
                   { simpl. intros. rewrite take_nil. rewrite drop_nil. auto. }
                   { intros. unfold insert.
                     destruct (decide (uint.nat i = 0%nat)). 
                     -- rewrite e. rewrite e in H2. simpl.
                        assert (coq_lexiographicCompare a.(versionVector) v.(versionVector) = true
                               ∨ coq_equalSlices a.(versionVector) v.(versionVector) = true).
                        { unfold is_sorted in H2.
                          assert (0 < 1)%nat by word. eapply H2.
                          - apply H.
                          - auto.
                          - auto.
                        }
                        destruct H.
                        ++ rewrite H. auto.
                        ++ assert (coq_lexiographicCompare a.(versionVector) v.(versionVector) =
                                   false) by admit.
                           apply equality_coq_equalSlices in H.
                           ** rewrite H0.
                              fold insert.
                              assert (take (uint.nat 0) l ++ [#v] ++ drop (uint.nat 0) l = (a :: l)%list). {
                                replace (uint.nat 0) with 0%nat by word.
                                simpl. rewrite drop_0.
                                f_equal. admit. (* Prove a lemma that states
                                                 operations are unique by version vectors*)
                              }
                              { rewrite <- H1. simpl.
                                replace (uint.nat (W64 0)) with 0%nat by word.
                                rewrite take_0. simpl. admit.
                              }
                           **  admit.
                     -- assert (H: (exists n, S n = uint.nat i)%nat). {
                          exists (Nat.pred (uint.nat i)). word. }
                        destruct H. 
                        rewrite <- H. simpl.
                        assert (coq_lexiographicCompare v.(versionVector) a.(versionVector) = true \/ coq_equalSlices v.(versionVector) a.(versionVector) = true). {
                          unfold is_sorted in H2.
                          eapply H2.
                          - assert (0 < (uint.nat i))%nat by word.
                            apply H0.
                          - replace (uint.nat (W64 (uint.nat i))) with (uint.nat i) by word. rewrite <- H. simpl. auto.
                          - replace (uint.nat (W64 (uint.nat i))) with (uint.nat i) by word. rewrite <- H. simpl. apply list_lookup_middle. rewrite length_take_le;
                              try word. rewrite length_cons in H7. word.
                        }
                        assert (coq_lexiographicCompare a.(versionVector) v.(versionVector) = false) by admit. (* we can do this by analyzing both cases *)
                        ++ rewrite H1.
                           fold insert.
                           assert (take (uint.nat x) l ++ [#v] ++ drop (uint.nat x) l = insert l v). {
                             eapply IHl.
                             - rewrite length_cons in H3. word.
                             - replace (uint.nat (W64 (uint.nat (W64 x)))) with x%nat by word. replace (uint.nat (W64 (S x))) with (S x)%nat in H2 by word. simpl in H2. unfold is_sorted. intros.
                               eapply H2.
                               + assert (S i0 < S j)%nat by word. apply H10.
                               + replace (uint.nat (W64 (uint.nat i))) with
                                   (uint.nat i) by word.
                                 rewrite <- H. auto.
                               + replace (uint.nat (W64 (uint.nat i))) with
                                   (uint.nat i) by word.
                                 rewrite <- H. auto.
                             - rewrite length_cons in H7. word.
                             - intros. eapply H6.
                               + assert (uint.nat i <= S j') by word. apply H9.
                               + auto.
                             - intros. eapply H5.
                               + assert (S i' < uint.nat i) by word. apply H9.
                               + auto.
                           }
                           rewrite <- H4. replace (uint.nat (W64 x)) with x by word.
                           auto.
                   }
                ** intros. eapply H5.
                   { assert (i' < uint.nat w) by word. apply H8. }
                   { auto. }
                ** intros. eapply H6.
                   { assert (uint.nat w <= j') by word. apply H8. }
                   { auto. }
  Qed.
                
                   
                  
  
  End heap.
  
  
