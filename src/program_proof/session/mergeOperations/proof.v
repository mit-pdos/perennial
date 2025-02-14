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
  
Fixpoint coq_sortedInsert (l : list Operation.t) (i : Operation.t) :=
  match l with
  | [] => [i]
  | cons h t => if (coq_lexiographicCompare h.(Operation.VersionVector) i.(Operation.VersionVector)) then (i :: h :: t)%list else (h :: coq_sortedInsert t i)%list
  end.

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
    Admitted.
    
