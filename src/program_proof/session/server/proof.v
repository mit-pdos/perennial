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
  
  Definition is_operation (opv: Slice.t*u64) (q:dfrac) (op: Operation.t): iProp Σ :=
    ⌜opv.2 = op.(Operation.Data)⌝ ∗
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

  Lemma aux_coq_equalSlices (l1 l2: list u64) :
    length l1 = length l2 ->
    coq_equalSlices l1 l2 = true ->
    l1 = l2.
  Proof.
    Admitted.

  Definition coq_equalOperations (o1 : Operation.t) (o2 : Operation.t) :=
    (coq_equalSlices o1.(Operation.VersionVector) o2.(Operation.VersionVector)) && ((uint.nat o1.(Operation.Data)) =? (uint.nat (o2.(Operation.Data)))).

  Lemma wp_equalOperations (opv1: Slice.t*u64) (o1: Operation.t) (opv2: Slice.t*u64) (o2: Operation.t):
    {{{
          is_operation opv1 (DfracOwn 1) o1 ∗
          is_operation opv2 (DfracOwn 1) o2 
    }}}
      equalOperations (operation_val opv1) (operation_val opv2)
      {{{ r , RET #r;
          ⌜r = coq_equalOperations o1 o2⌝
      }}}.
  Proof.
  Admitted.
  
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
    coq_lexiographicCompare l2 l1 = true ->
    coq_lexiographicCompare l3 l2 = true ->
    coq_lexiographicCompare l3 l1 = true.
  Proof.
  Admitted.

  Lemma aux1_lexiographicCompare (l1 l2: list u64) :
    length l1 = length l2 -> 
    (coq_lexiographicCompare l2 l1 = false <-> coq_lexiographicCompare l1 l2 = true).
  Proof.
  Admitted.

End heap.


