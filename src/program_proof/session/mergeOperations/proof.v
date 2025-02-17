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

  Fixpoint coq_equalSlices (l1: list u64) (l2: list u64) :=
    match l1 with
    | [] => true
    | cons h1 t1 => match l2 with
                    | [] => true
                    | cons h2 t2 => if (negb ((uint.Z h1) =? (uint.Z h2)))
                                    then false else (coq_equalSlices t1 t2)
                    end
    end.
  

  Lemma aux1_equalSlices (l1 l2: list u64) :
    length l1 = length l2 ->
    coq_equalSlices l1 l2 = false ->
    l1 ≠ l2.
  Proof.
    revert l2. induction l1 as [ | x1 l1 IH], l2 as [ | x2 l2]; simpl; intros; congruence || eauto.
    destruct (_ =? _) as [ | ] eqn: H_OBS; [rewrite Z.eqb_eq in H_OBS | rewrite Z.eqb_neq in H_OBS]; simpl in *.
    - specialize IH with (l2 := l2). apply f_equal with (f := Nat.pred) in H. simpl in H. specialize (IH H H0). congruence.
    - intros CONTRA. eapply H_OBS. congruence.
  Qed.

  Fixpoint coq_lexiographicCompare (v1 v2: list u64) : bool :=
    match v1 with
    | [] => false 
    | cons h1 t1 => match v2 with
                    | [] => false 
                    | cons h2 t2 => if (uint.Z h1) =? (uint.Z h2) then
                                      (coq_lexiographicCompare t1 t2) else (uint.Z h1) >? (uint.Z h2)
                    end
    end.
  
  Fixpoint coq_sortedInsert (l : list Operation.t) (i : Operation.t) :=
    match l with
    | [] => [i]
    | cons h t => if (coq_lexiographicCompare h.(Operation.VersionVector) i.(Operation.VersionVector)) then (i :: h :: t)%list else (h :: coq_sortedInsert t i)%list
    end.

  Definition coq_equalOperations (o1 : Operation.t) (o2 : Operation.t) :=
    (coq_equalSlices o1.(Operation.VersionVector) o2.(Operation.VersionVector)) && ((uint.nat o1.(Operation.Data)) =? (uint.nat (o2.(Operation.Data)))).

  Definition coq_mergeOperations (l1: list Operation.t) (l2: list Operation.t) : (list Operation.t) :=
    let output := fold_left (fun acc element => coq_sortedInsert acc element) l2 l1 in
    snd (fold_left (fun (acc: nat * list Operation.t) element =>
                      let (index, acc) := acc in
                      if (index >? 0) then 
                        match (output !! (uint.nat (index - 1))) with
                        | Some v => if (coq_equalOperations element v) then
                                      ((index + 1)%nat, acc)
                                    else
                                      ((index + 1)%nat,  acc ++ [element])
                        | None => ((index + 1)%nat, acc ++ [element])
                        end
                      else ((index + 1)%nat, acc ++ [element]))
           output (0%nat, [])). 

  Lemma wp_mergeOperations (s1 s2: Slice.t) (l1 l2: list Operation.t) (n: nat) :
    {{{
          operation_slice s1 l1 n ∗
          operation_slice s2 l2 n 
    }}}
      mergeOperations s1 s2 
      {{{
            (ns: Slice.t), RET slice_val (ns);
            ∃ nxs, operation_slice ns nxs n ∗
                   ⌜nxs = coq_mergeOperations l1 l2⌝
      }}}.
  Proof.
    rewrite /mergeOperations. iIntros (Φ) "[(%l1_ops & H_s1 & H_l1_ops) (%l2_ops & H_s2 & H_l2_ops)] H_ret".
    wp_rec. wp_pures. wp_apply (wp_NewSlice). iIntros "%s3 H_s3". replace (uint.nat (W64 0)) with 0%nat by word. simpl.
    wp_apply (wp_SliceAppendSlice with "[H_s1 H_s3]"); auto.
    { iFrame. iApply (own_slice_to_small with "[$H_s1]"). }
    clear s3. iIntros "%s3 [H_s3 H_s1]".
    wp_apply wp_ref_to; auto. iIntros "%output H_output". wp_pures.
    wp_apply wp_ref_to; auto. iIntros "%i H_i".
    wp_pures. wp_apply wp_slice_len. simpl.
    wp_apply wp_ref_to; auto. iIntros "%l H_l". wp_pures.
    wp_apply (wp_forBreak_cond
      ( λ continue, ∃ s3 : Slice.t, ∃ l3_ops : list (Slice.t * w64), ∃ l2_prevs : list Operation.t, ∃ l2_nexts : list Operation.t,
        "H_s1" ∷ own_slice_small s1 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l1_ops ∗
        "H_s2" ∷ own_slice s2 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l2_ops ∗
        "H_s3" ∷ own_slice s3 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l3_ops ∗
        ([∗ list] opv;o ∈ l1_ops;l1, □ is_operation opv (DfracOwn 1) o n) ∗
        ([∗ list] opv;o ∈ l2_ops;l2, □ is_operation opv (DfracOwn 1) o n) ∗
        ([∗ list] opv;o ∈ l3_ops;fold_left coq_sortedInsert l2_prevs l1, is_operation opv (DfracOwn 1) o n) ∗
        ⌜l2 = l2_prevs ++ l2_nexts⌝ ∗
        i ↦[uint64T] #(W64 (length l2_prevs)) ∗
        l ↦[uint64T] #s2 .(Slice.sz) ∗
        output ↦[slice.T (slice.T uint64T * (uint64T * unitT)%ht)] s3 ∗
        ⌜continue = false -> l2_nexts = []⌝
      )%I
    with "[] [H_l1_ops H_l2_ops H_s1 H_s2 H_s3 H_output H_i H_l]").
    { clear Φ s3. iIntros (Φ). iModIntro. iIntros "(%s3 & %l3_ops & %l2_prevs & %l2_nexts & H_s1 & H_s2 & H_s3 & H_l1_ops & H_l2_ops & H_l3_ops & %H_l2 & H_i & H_l & H_output & %H_continue)".
      clear H_continue. iNamed "H_s1". iNamed "H_s2". iNamed "H_s3". iIntros "H_ret".
      wp_rec. wp_load. wp_load. wp_if_destruct.
      - iAssert (⌜uint.nat (s2.(Slice.sz)) = length l2⌝%I) as "%H_l2_len".
        { iPoseProof (big_sepL2_length with "[$H_l2_ops]") as "%H_l2_len".
          iPoseProof (own_slice_sz with "[$H_s2]") as "%H_l2_ops_len".
          iPureIntro. congruence.
        }
        iAssert (⌜uint.nat (W64 (length l2_prevs)) < length l2_ops⌝%nat)%I as "%H_bound".
        { iPoseProof (own_slice_sz with "[$H_s2]") as "%H_l2_ops_len".
          iPureIntro. word.
        }
        apply lookup_lt_is_Some_2 in H_bound. destruct H_bound as [cur H_cur].
        wp_load. wp_apply (wp_SliceGet with "[H_s2]").
        { iSplitL "H_s2".
          - iApply (own_slice_to_small with "[H_s2]"). iExact "H_s2".
          - iPureIntro. exact H_cur.
        }
        iIntros "H_s2". wp_load. admit.
      - iModIntro. iApply "H_ret". iExists s3. iExists l3_ops. iExists l2_prevs. iExists l2_nexts.
        iAssert (⌜uint.nat (s2.(Slice.sz)) = length l2⌝%I) as "%H_l2_len".
        { iPoseProof (big_sepL2_length with "[$H_l2_ops]") as "%H_l2_len".
          iPoseProof (own_slice_sz with "[$H_s2]") as "%H_l2_ops_len".
          iPureIntro. congruence.
        }
        iFrame.
        iAssert ⌜l2_nexts = []⌝%I as "%H_l2_nexts".
        { iPureIntro. destruct l2_nexts as [ | l2_cur l2_nexts]; trivial.
          contradiction Heqb. replace (uint.Z s2 .(Slice.sz)) with (Z.of_nat (length l2)) by word.
          rewrite H_l2. rewrite length_app. simpl. word.
        }
        iAssert ⌜l2_prevs = l2⌝%I as "%H_l2_prevs".
        { subst l2_nexts. rewrite app_nil_r in H_l2. done. }
        done.
    }
    { iExists s3. iExists l1_ops. iExists []. iExists l2. simpl.
      iAssert (<pers> ([∗ list] opv;o ∈ l1_ops;l1, □ is_operation opv (DfracOwn 1) o n))%I as "#H_l1_ops_pers".
      { iApply (big_sepL2_persistently). iApply (big_sepL2_mono (fun k => fun y1 => fun y2 => □ is_operation y1 (DfracOwn 1) y2 n)%I).
        - intros. iIntros "#H". iApply intuitionistically_into_persistently_1. iModIntro. done.
        - done.
      }
      iPoseProof (big_sepL2_length with "[$H_l1_ops_pers]") as "%H_l1_len".
      iFrame. iSplit.
      - iApply (big_sepL2_mono (fun k => fun y1 => fun y2 => □ is_operation y1 (DfracOwn 1) y2 n)%I).
        { intros. iIntros "#H". done. }
        { done. }
      - done.
    }
    clear s3. iIntros "(%s3 & %l3_ops & %l2_prevs & %l2_nexts & H_s1 & H_s2 & H_s3 & H_l1_ops & H_l2_ops & H_l3_ops & %H_l2 & H_i & H_l & H_output & %H_l2_nexts)".
    specialize (H_l2_nexts eq_refl). subst l2_nexts. rewrite app_nil_r in H_l2. subst l2_prevs. iNamed "H_s1". iNamed "H_s2". iNamed "H_s3".
    wp_pures. wp_apply wp_ref_to; auto. iIntros "%prev H_prev".
    wp_pures. wp_apply wp_ref_to; auto. iIntros "%curr H_curr".
    wp_pures.
    remember (fold_left coq_sortedInsert l2 l1) as l3 eqn: H_l3.
    set (loop_step := λ (acc: nat * list Operation.t) (element : Operation.t),
      let (index, acc) := acc in
      if (index >? 0) then 
        match (l3 !! (uint.nat (index - 1))) with
        | Some v => if (coq_equalOperations element v) then ((index + 1)%nat, acc) else ((index + 1)%nat,  acc ++ [element])
        | None => ((index + 1)%nat, acc ++ [element])
        end
      else ((index + 1)%nat, acc ++ [element])
    ).
    set (loop_init := (0%nat, @nil Operation.t)).
    destruct l3 as [ | l3_hd l3_tl].
    - wp_apply (wp_forBreak_cond
        ( λ continue, ∃ s3 : Slice.t, ∃ l3_ops : list (Slice.t * w64), 
          "H_s1" ∷ own_slice_small s1 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l1_ops ∗
          "H_s2" ∷ own_slice s2 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l2_ops ∗
          "H_s3" ∷ own_slice s3 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l3_ops ∗
          ([∗ list] opv;o ∈ l1_ops;l1, □ is_operation opv (DfracOwn 1) o n) ∗
          ([∗ list] opv;o ∈ l2_ops;l2, □ is_operation opv (DfracOwn 1) o n) ∗
          ([∗ list] opv;o ∈ l3_ops;[], is_operation opv (DfracOwn 1) o n) ∗
          prev ↦[uint64T] #1 ∗
          curr ↦[uint64T] #1 ∗
          output ↦[slice.T (slice.T uint64T * (uint64T * unitT)%ht)] s3
        )%I
      with "[] [H_prev H_curr H_output H_s1 H_s2 H_s3 H_l1_ops H_l2_ops H_l3_ops]").
      { clear Φ s3 l3_ops. iIntros (Φ). iModIntro. iIntros "(%s3 & %l3_ops & H_s1 & H_s2 & H_s3 & H_l1_ops & H_l2_ops & H_l3_ops & H_prev & H_curr & H_output) H_ret".
        wp_pures. wp_load. wp_load. wp_apply wp_slice_len. wp_if_destruct.
        - wp_pures. iExFalso.
          iPoseProof (own_slice_sz with "[$H_s3]") as "%H_l3_ops_len".
          iPoseProof (big_sepL2_length with "[$H_l3_ops]") as "%H_l3_len".
          simpl in *. word.
        - iModIntro. iApply "H_ret". iExists s3. iExists l3_ops. iFrame.
      }
      { iExists s3. iExists l3_ops. iFrame. }
      { clear s3 l3_ops.
        iIntros "(%s3 & %l3_ops & H_s1 & H_s2 & H_s3 & H_l1_ops & H_l2_ops & H_l3_ops & H_output & H_prev & H_curr)".
        wp_pures. wp_load. wp_load. wp_apply (wp_SliceTake).
        { admit. (* uint.Z (W64 1) ≤ uint.Z s3 .(Slice.cap) *) }
        iApply "H_ret". iExists (coq_mergeOperations l1 l2). iSplitL.
        - iExists []. unfold coq_mergeOperations. replace (fold_left (λ (acc : list Operation.t) (element : Operation.t), coq_sortedInsert acc element) l2 l1) with (@nil Operation.t). simpl.
          iAssert ⌜l3_ops = []⌝%I as "%H_l3_ops_nil".
          { iApply (big_sepL2_nil_inv_r with "[$H_l3_ops]"). }
          subst l3_ops. iSplitR "H_l3_ops".
          + admit. (* own_slice (slice_take s3 (W64 1)) (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) [] *)
          + iApply (big_sepL2_nil). iExact "H_l3_ops".
        - done.
      }
    - wp_apply (wp_forBreak_cond
        ( λ continue, ∃ s3 : Slice.t, ∃ l3_ops : list (Slice.t * w64), ∃ l3_sec1 : list Operation.t, ∃ l3_sec2 : list Operation.t, ∃ l3_sec3 : list Operation.t,
          "H_s1" ∷ own_slice_small s1 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l1_ops ∗
          "H_s2" ∷ own_slice s2 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l2_ops ∗
          "H_s3" ∷ own_slice s3 (slice.T uint64T * (uint64T * unitT)%ht) (DfracOwn 1) l3_ops ∗
          ([∗ list] opv;o ∈ l1_ops;l1, □ is_operation opv (DfracOwn 1) o n) ∗
          ([∗ list] opv;o ∈ l2_ops;l2, □ is_operation opv (DfracOwn 1) o n) ∗
          ([∗ list] opv;o ∈ l3_ops;snd (fold_left loop_step (l3_sec1 ++ l3_sec2) loop_init) ++ l3_sec2 ++ l3_sec3, is_operation opv (DfracOwn 1) o n) ∗
          ⌜l3_hd :: l3_tl = l3_sec1 ++ l3_sec2 ++ l3_sec3⌝%list ∗
          prev ↦[uint64T] #(length l3_sec1) ∗
          curr ↦[uint64T] #(length (l3_sec1 ++ l3_sec2)) ∗
          output ↦[slice.T (slice.T uint64T * (uint64T * unitT)%ht)] s3 ∗
          ⌜continue = false -> l3_sec3 = []⌝ ∗
          ⌜length l3_sec1 = length (snd (fold_left loop_step (l3_sec1 ++ l3_sec2) loop_init))⌝ ∗
          ⌜length (l3_sec1 ++ l3_sec2) = fst (fold_left loop_step (l3_sec1 ++ l3_sec2) loop_init)⌝ ∗
          ⌜length (l3_sec1 ++ l3_sec2 ++ l3_sec3) = uint.nat s3 .(Slice.sz)⌝ ∗
          ⌜length (l3_sec1) > 0⌝%nat ∗
          ⌜length (l3_sec1 ++ l3_sec2) > 0⌝%nat
        )%I
      with "[] [H_l1_ops H_l2_ops H_l3_ops H_s1 H_s2 H_s3 H_output H_prev H_curr]").
      { clear Φ s3 l3_ops. iIntros (Φ). iModIntro.
        iIntros "(%s3 & %l3_ops & %l3_sec1 & %l3_sec2 & %l3_sec3 & H_s1 & H_s2 & H_s3 & H_l1_ops & H_l2_ops & H_l3_ops & %H_l3_secs & H_prev & H_curr & H_output & %H_continue & %H_prev_val & %H_curr_val & %H_l3_len & %H_prev_val_pos & %H_curr_val_pos) H_ret".
        wp_rec. wp_load. wp_load. wp_apply wp_slice_len. wp_if_destruct.
        - iAssert (⌜is_Some (l3_ops !! uint.nat (W64 (length (l3_sec1 ++ l3_sec2))))⌝%I) as "%SOME".
          { iPoseProof (big_sepL2_length with "[$H_l3_ops]") as "%H_l3_ops_len". 
            rewrite length_app in H_l3_ops_len. rewrite <- H_prev_val in H_l3_ops_len. rewrite length_app in H_l3_ops_len.
            iPureIntro. eapply lookup_lt_is_Some_2. do 2 rewrite length_app in H_l3_len. rewrite length_app. rewrite length_app in Heqb. word.
          }
          destruct SOME as [peek H_peek].
          wp_pures. wp_load. wp_load. wp_apply (wp_SliceGet with "[H_s3]").
          { iSplitL "H_s3".
            - iApply (own_slice_to_small with "[$H_s3]").
            - iPureIntro. exact H_peek.
          }
          iAssert (⌜is_Some (l3_ops !! uint.nat (W64 (length (l3_sec1 ++ l3_sec2) - 1)))⌝%I) as "%SOME".
          { iPoseProof (big_sepL2_length with "[$H_l3_ops]") as "%H_l3_ops_len". 
            rewrite length_app in H_l3_ops_len. rewrite <- H_prev_val in H_l3_ops_len. rewrite length_app in H_l3_ops_len.
            iPureIntro. eapply lookup_lt_is_Some_2. do 2 rewrite length_app in H_l3_len. rewrite length_app. rewrite length_app in Heqb. word.
          }
          destruct SOME as [peek' H_peek'].
          iIntros "H_s3". wp_load. wp_load. wp_apply (wp_SliceGet with "[H_s3]").
          { iSplitL "H_s3".
            - iExact "H_s3".
            - iPureIntro. replace (uint.nat (W64 (length (l3_sec1 ++ l3_sec2) - 1))) with (uint.nat (w64_word_instance .(word.sub) (W64 (length (l3_sec1 ++ l3_sec2))) (W64 1))) in H_peek' by word. exact H_peek'.
          }
          iIntros "H_s3". simpl. admit.
        - iModIntro. iApply "H_ret". iExists s3. iExists l3_ops. iExists l3_sec1. iExists l3_sec2. iExists l3_sec3.
          iAssert ⌜l3_sec3 = []⌝%I as "%H_l3_sec3_nil".
          { iPureIntro. enough (length l3_sec3 = 0)%nat by by destruct l3_sec3.
            rewrite length_app in Heqb. rewrite length_app in H_curr_val_pos. do 2 rewrite length_app in H_l3_len. word.
          }
          iFrame. done.
      }
      { iExists s3. iExists l3_ops. iExists [l3_hd]%list. iExists []%list. iExists l3_tl. simpl.
        iPoseProof (own_slice_sz with "[$H_s3]") as "%claim1".
        iPoseProof (big_sepL2_length with "[$H_l3_ops]") as "%claim2".
        rewrite claim1 in claim2. simpl in *. symmetry in claim2. iFrame.
        iSplit. { iPureIntro. done. }
        iSplit. { iPureIntro. congruence. }
        iSplit. { iPureIntro. done. }
        iSplit. { iPureIntro. done. }
        iSplit. { iPureIntro. done. }
        word.
      }
      { clear s3 l3_ops.
        iIntros "(%s3 & %l3_ops & %l3_sec1 & %l3_sec2 & %l3_sec3 & H_s1 & H_s2 & H_s3 & H_l1_ops & H_l2_ops & H_l3_ops & %H_l3_secs & H_prev & H_curr & H_output & %H_continue & %H_prev_val & %H_curr_val & %H_l3_len & %H_prev_val_pos & %H_curr_val_pos)".
        iNamed "H_s1". iNamed "H_s2". iNamed "H_s3".
        wp_pures. wp_load. wp_load. 
        iAssert ⌜uint.Z (W64 (length l3_sec1)) ≤ uint.Z s3 .(Slice.cap)⌝%I as "%H_s3_cap".
        { iPoseProof (own_slice_small_wf with "[H_s3]") as "%H_claim1".
          { iApply (own_slice_to_small with "[$H_s3]"). }
          do 2 rewrite length_app in H_l3_len. simpl in *. word.
        }
        iAssert ⌜uint.Z (W64 (length l3_sec1)) ≤ length l3_ops⌝%I as "%claim1".
        { iPoseProof (big_sepL2_length with "[$H_l3_ops]") as "%H_l3_ops_len".
          do 2 rewrite length_app in H_l3_ops_len. rewrite <- H_prev_val in H_l3_ops_len. word.
        }
        wp_apply (wp_SliceTake_full with "[$H_s3]"); auto. iIntros "H_s3".
        iApply "H_ret". iExists (coq_mergeOperations l1 l2). iSplitL.
        - iExists (take (length l3_sec1) l3_ops). do 2 rewrite length_app in H_l3_len.
          replace (uint.nat (W64 (length l3_sec1))) with (length l3_sec1) by word.
          unfold coq_mergeOperations. replace (fold_left (λ (acc : list Operation.t) (element : Operation.t), coq_sortedInsert acc element) l2 l1) with (l3_hd :: l3_tl)%list.
          specialize (H_continue eq_refl). subst l3_sec3. rewrite app_nil_r in H_l3_secs, H_l3_len |- *.
          fold loop_step. fold loop_init. rewrite H_l3. iFrame. clear Φ.
          simpl in *. rewrite Nat.add_0_r in H_l3_len. admit.
        - done.
      }
  Admitted.
