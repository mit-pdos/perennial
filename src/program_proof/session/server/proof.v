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

  Definition is_operation (opv: Slice.t*u64) (q:dfrac) (op: Operation.t) (opv_len: nat): iProp Σ :=
    ⌜opv.2 = op.(Operation.Data)⌝ ∗
    ⌜opv_len = length (op.(Operation.VersionVector))⌝ ∗
    own_slice opv.1 uint64T q op.(Operation.VersionVector)%I.

  Definition operation_slice' q (op_s: Slice.t) (op: list Operation.t): iProp Σ :=
    ∃ ops , own_slice op_s (struct.t Operation) (DfracOwn 1) (ops) ∗
            [∗ list] _ ↦ opv;o ∈ ops;op , let '(Operation.mk s d) := o in
                                          own_slice (opv.1) (uint64T) q s ∗
                                          ⌜opv.2 = d⌝.

  Definition operation_slice (s: Slice.t) (ls: list Operation.t): iProp Σ :=
    operation_slice' (DfracOwn 1) s ls.

  Definition operation_to_val (o: Operation.t) (s: Slice.t) :=
    (s, (#o.(Operation.Data), #()))%V.

  Definition coq_getDataFromOperationLog (l: list Operation.t) :=
    match list_lookup (uint.nat ((length l) - 1)) l with
    | Some v => v.(Operation.Data)
    | None => 0
    end. 

  Lemma wp_getDataFromOperationLog (s: Slice.t) (l: list Operation.t) :
    {{{
          operation_slice s l 
    }}}
      getDataFromOperationLog s
    {{{
          r , RET #r;
          ⌜r = coq_getDataFromOperationLog l⌝
    }}}.
  Proof.
    rewrite /getDataFromOperationLog. wp_pures. iIntros "%Φ Hl H1". wp_pures.
    wp_rec. iDestruct "Hl" as "(%ops & Hs & Hl)". wp_if_destruct.
    - wp_rec.
      iAssert (⌜is_Some (ops !! uint.nat (w64_word_instance .(word.sub) s .(Slice.sz) (W64 1)))⌝%I) with "[Hl Hs]" as "%Hl".
      { induction ops as [ | ? ? _] using List.rev_ind.
        - iAssert (⌜l = []⌝)%I with "[Hl]" as "%Hl".
          { iApply big_sepL2_nil_inv_l. iExact "Hl". }
          subst l. simpl. iPoseProof (own_slice_sz with "[$Hs]") as "%Hs".
          simpl in *. iPureIntro. word.
        - iPoseProof (own_slice_sz with "[$Hs]") as "%Hs".
          iPureIntro. red. exists x. eapply list_lookup_middle. rewrite length_app in Hs. simpl in Hs. word.
      }
      iAssert (⌜length ops = length l⌝)%I with "[Hl]" as "%Hlength".
      { iApply big_sepL2_length. iExact "Hl". }
      destruct Hl as (x & EQ).
      wp_apply (wp_SliceGet with "[Hs] [Hl H1]").
      + iSplitL "Hs".
        * simpl (struct.t Operation). iApply (own_slice_to_small with "[Hs]"). iExact "Hs".
        * iPureIntro. exact EQ.
      + iModIntro. iIntros "Hs".
        wp_pures. iModIntro. iApply "H1".
        unfold coq_getDataFromOperationLog.
        iPoseProof (own_slice_small_sz with "[$Hs]") as "%Hs".
        induction ops as [ | ops_last ops_init _] using List.rev_ind.
        { simpl in *. word. }
        induction l as [ | l_last l_init _] using List.rev_ind.
        { simpl in *. word. }
        iPoseProof big_sepL2_snoc as "LEMMA1".  iApply "LEMMA1" in "Hl". iClear "LEMMA1".
        iDestruct "Hl" as "[H_init H_last]". simpl in *. destruct ops_last, l_last. simpl.
        iDestruct "H_last" as "[Ht ->]". repeat rewrite length_app. simpl.
        iAssert (⌜uint.nat (W64 ((length l_init + 1)%nat - 1)) = length l_init⌝)%I as "%YES1".
        { iPureIntro. do 2 rewrite app_length in Hlength. rewrite app_length in Hs. simpl in *. word. }
        iAssert (⌜list_lookup (uint.nat (W64 ((length l_init + 1)%nat - 1))) (l_init ++ [ {| Operation.VersionVector := VersionVector; Operation.Data := Data |} ])%list = Some {| Operation.VersionVector := VersionVector; Operation.Data := Data |}⌝)%I as "%YES".
        { iPureIntro. eapply lookup_snoc_Some. right. done. }
        rewrite YES. simpl. iPureIntro. destruct x as [x1 x2]. simpl.
        assert (YES2 : uint.nat (w64_word_instance .(word.sub) s .(Slice.sz) (W64 1)) = length ops_init).
        { do 2 rewrite app_length in Hlength. rewrite app_length in Hs. simpl in *. word. }
        rewrite YES2 in EQ. rewrite lookup_snoc in EQ. congruence.
    - iModIntro. iApply "H1". unfold coq_getDataFromOperationLog.
      iAssert (⌜uint.Z (W64 0) = uint.Z s .(Slice.sz)⌝)%I as "%NIL".
      { word. }
      destruct l as [ | ? ?].
      { simpl. iPureIntro. done. }
      simpl. destruct ops as [ | ? ?].
      { iPoseProof (big_sepL2_nil_inv_l with "[$Hl]") as "%Hl". congruence. }
      iPoseProof (own_slice_sz with "[$Hs]") as "%Hs".
      simpl in Hs. word.
  Qed.

  Fixpoint coq_equalSlices (l1: list u64) (l2: list u64) :=
    match l1 with
    | [] => true
    | cons h1 t1 => match l2 with
                    | [] => true
                    | cons h2 t2 => if (negb ((uint.Z h1) =? (uint.Z h2)))
                                    then false else (coq_equalSlices t1 t2)
                    end
    end.

  Lemma aux_coq_equalSlices (l1 l2: list u64) :
    length l1 = length l2 ->
    coq_equalSlices l1 l2 = true ->
    l1 = l2.
  Proof.
    revert l2. induction l1 as [ | x1 l1 IH], l2 as [ | x2 l2]; simpl; intros; try congruence.
    destruct (uint.Z x1 =? uint.Z x2) as [ | ] eqn: H_OBS; simpl in *.
    - rewrite Z.eqb_eq in H_OBS. f_equal.
      + word.
      + eauto.
    - discriminate.
  Qed.

  Definition coq_equalOperations (o1 : Operation.t) (o2 : Operation.t) :=
    (coq_equalSlices o1.(Operation.VersionVector) o2.(Operation.VersionVector)) && ((uint.nat o1.(Operation.Data)) =? (uint.nat (o2.(Operation.Data)))).

  Axiom wp_equalSlices : forall (x: Slice.t) (xs: list w64) (y: Slice.t) (ys: list w64),
    {{{
          own_slice x uint64T (DfracOwn 1) xs ∗
          own_slice y uint64T (DfracOwn 1) ys ∗
          ⌜length xs = length ys⌝ ∗
          ⌜length xs < 2^64⌝
    }}}
      equalSlices x y 
    {{{
          r , RET #r;
          ⌜r = coq_equalSlices xs ys⌝ ∗ 
          own_slice x uint64T (DfracOwn 1) xs ∗
          own_slice y uint64T (DfracOwn 1) ys ∗
          ⌜length xs = length ys⌝ ∗
          ⌜length xs < 2^64⌝
    }}}.

  Lemma wp_equalOperations (opv1: Slice.t*u64) (o1: Operation.t) (opv2: Slice.t*u64) (o2: Operation.t) (n: nat):
    {{{
          is_operation opv1 (DfracOwn 1) o1 n ∗
          is_operation opv2 (DfracOwn 1) o2 n
    }}}
      equalOperations (operation_val opv1) (operation_val opv2)
    {{{ r , RET #r;
        ⌜r = coq_equalOperations o1 o2⌝
    }}}.
  Proof.
    rewrite /equalOperations. iIntros "%Φ [Ho1 Ho2] Hret".
    iDestruct "Ho1" as "(%Hopv1snd & %Hlen1 & Ho1)". iDestruct "Ho2" as "(%Hopv2snd & %Hlen2 & Ho2)".
    wp_rec. wp_pures. wp_apply (wp_equalSlices with "[Ho1 Ho2]").
    { iAssert (⌜length (o1 .(Operation.VersionVector)) < 2 ^ 64⌝)%I with "[Ho1]" as "%Hlen264".
      { iPoseProof (own_slice_sz with "[$Ho1]") as "%LEN". iPureIntro. word. }
      instantiate (1 := o1.(Operation.VersionVector)). instantiate (1 := o2.(Operation.VersionVector)).
      iFrame. iSplitL.
      - iPureIntro. congruence.
      - iPureIntro. done.
    }
    iIntros "%r (%OBS & Hopv1 & Hopv2 & %LEN1 & %LEN2)". wp_if_destruct.
    - wp_pures. iModIntro. iApply "Hret". unfold coq_equalOperations.
      rewrite <- OBS. simpl. rewrite Hopv1snd Hopv2snd.
      iPureIntro. destruct (_ =? _) as [ | ] eqn: H_compare.
      + rewrite Z.eqb_eq in H_compare.
        assert (EQ : o1.(Operation.Data) = o2.(Operation.Data)) by word.
        eapply bool_decide_eq_true_2. congruence.
      + rewrite Z.eqb_neq in H_compare.
        assert (NE : o1.(Operation.Data) ≠ o2.(Operation.Data)) by word.
        eapply bool_decide_eq_false_2. congruence.
    - iModIntro. iApply "Hret". unfold coq_equalOperations.
      rewrite <- OBS. simpl. iPureIntro. done.
  Qed.

  Fixpoint coq_lexicographicCompare (v1 v2: list u64) : bool :=
    match v1 with
    | [] => false 
    | cons h1 t1 => match v2 with
                    | [] => false 
                    | cons h2 t2 => if (uint.Z h1) =? (uint.Z h2) then
                                      (coq_lexicographicCompare t1 t2) else (uint.Z h1) >? (uint.Z h2)
                    end
    end.

  Lemma aux0_lexicographicCompare (l1 l2 l3: list u64) :
    coq_lexicographicCompare l2 l1 = true ->
    coq_lexicographicCompare l3 l2 = true ->
    coq_lexicographicCompare l3 l1 = true.
  Proof with done || word || eauto.
    revert l1 l3; induction l2 as [ | x2 l2 IH], l1 as [ | x1 l1], l3 as [ | x3 l3]; simpl...
    repeat
      lazymatch goal with
      | [ |- context[ uint.Z ?x =? uint.Z ?y ] ] => let H_OBS := fresh in destruct (uint.Z x =? uint.Z y) as [ | ] eqn: H_OBS; [rewrite Z.eqb_eq in H_OBS | rewrite Z.eqb_neq in H_OBS]
      | [ |- context[ uint.Z ?x >? uint.Z ?y ] ] => let H_OBS := fresh in pose proof (H_OBS := Zgt_cases (uint.Z x) (uint.Z y)); destruct (uint.Z x >? uint.Z y) as [ | ]
      | [ H : uint.Z ?x = uint.Z ?y |- _ ] => apply word.unsigned_inj in H; subst
      end...
  Qed.

  Lemma aux1_lexicographicCompare (l1 l2: list u64) :
    length l1 = length l2 -> 
    l1 ≠ l2 ->
    (coq_lexicographicCompare l2 l1 = false <-> coq_lexicographicCompare l1 l2 = true).
  Proof with done || word || eauto.
    revert l2; induction l1 as [ | x1 l1 IH], l2 as [ | x2 l2]; simpl; intros...
    repeat
      lazymatch goal with
      | [ |- context[ uint.Z ?x =? uint.Z ?y ] ] => let H := fresh in destruct (uint.Z x =? uint.Z y) as [ | ] eqn: H; [rewrite Z.eqb_eq in H | rewrite Z.eqb_neq in H]
      | [ |- context[ uint.Z ?x >? uint.Z ?y ] ] => let H := fresh in pose proof (Zgt_cases (uint.Z x) (uint.Z y)) as H; destruct (uint.Z x >? uint.Z y) as [ | ]
      | [ H : uint.Z ?x = uint.Z ?y |- _ ] => apply word.unsigned_inj in H; subst
      end...
    eapply IH; congruence.
  Qed.

End heap.


