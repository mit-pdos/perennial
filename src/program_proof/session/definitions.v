From Perennial.program_proof Require Export session_prelude.

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

                  C2S_Client_Id:            u64;
	          C2S_Client_OperationType: u64;
	          C2S_Client_Data:          u64;
	          C2S_Client_VersionVector: list u64;

	          S2S_Gossip_Sending_ServerId:   u64;
	          S2S_Gossip_Receiving_ServerId: u64;
	          S2S_Gossip_Operations:         list Operation.t;
	          S2S_Gossip_Index:              u64;

	          S2S_Acknowledge_Gossip_Sending_ServerId:   u64;
	          S2S_Acknowledge_Gossip_Receiving_ServerId: u64;
	          S2S_Acknowledge_Gossip_Index:              u64;

	          S2C_Client_OperationType: u64;    
	          S2C_Client_Data:          u64;
	          S2C_Client_VersionVector: list u64;
	          S2C_Client_RequestNumber: u64;
	          S2C_Client_Number:        u64;
                }.

End Message.

Module Server.

  Record t :=
    mk {
        Id:                     u64 ;
	NumberOfServers:        u64 ;
	UnsatisfiedRequests:    list Message.t ;
	VectorClock:            list u64 ;
	OperationsPerformed:    list Operation.t ;
	MyOperations:           list Operation.t ;
	PendingOperations:      list Operation.t ;
	GossipAcknowledgements: list u64 ;
	SeenRequests:           list u64 ;
      }.

End Server.

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

  Definition is_operation (opv: Slice.t*u64) (op: Operation.t) (opv_len: nat): iProp Σ :=
    ⌜opv.2 = op.(Operation.Data)⌝ ∗
    ⌜opv_len = length (op.(Operation.VersionVector))⌝ ∗
    (own_slice_small opv.1 uint64T DfracDiscarded op.(Operation.VersionVector))%I.

  Definition operation_slice' (op_s: Slice.t) (op: list Operation.t)
                              (n: nat) : iProp Σ :=
    ∃ ops , own_slice op_s (struct.t Operation) (DfracOwn 1) (ops) ∗
            [∗ list] _ ↦ opv;o ∈ ops;op , (is_operation opv o n).
  
  Definition operation_slice (s: Slice.t) (ls: list Operation.t) (n: nat) : iProp Σ :=
    operation_slice' s ls n.

  Definition operation_to_val (o: Operation.t) (s: Slice.t) :=
    (s, (#o.(Operation.Data), #()))%V.

End heap.
