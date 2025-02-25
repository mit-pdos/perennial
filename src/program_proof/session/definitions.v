From Perennial.program_proof.session Require Export session_prelude.

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
	          C2S_Server_Id:            u64;
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
                  S2C_Server_Id:            u64;
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
      }.

End Server.

Section heap.
  Context `{hG: !heapGS Σ}.

  Definition operation_val (op:Slice.t*u64): val :=
    (slice_val op.1, (#op.2, #()))%V.

  Theorem operation_val_t op : val_ty (operation_val op) (struct.t Operation).
  Proof.
    repeat constructor; auto.
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
  
  #[global] Instance operation_into_val_for_type : IntoValForType (Slice.t*u64) (struct.t Operation).
  Proof. constructor; auto. Qed.

  Definition is_operation (opv: Slice.t*u64) (op: Operation.t) (opv_len: nat): iProp Σ :=
    ⌜opv.2 = op.(Operation.Data)⌝ ∗
    ⌜opv_len = length (op.(Operation.VersionVector))⌝ ∗
    (own_slice_small opv.1 uint64T DfracDiscarded op.(Operation.VersionVector))%I.

  Definition operation_slice' (op_s: Slice.t) (op: list Operation.t)
                              (n: nat) : iProp Σ :=
    ∃ ops , own_slice op_s (struct.t Operation) (DfracOwn 1) (ops) ∗
            [∗ list] _ ↦ opv;o ∈ ops;op, is_operation opv o n.
  
  Definition operation_slice (s: Slice.t) (l: list Operation.t) (n: nat) : iProp Σ :=
    operation_slice' s l n.

  Definition message_val (msg:u64*u64*u64*u64*u64*Slice.t*u64*u64*Slice.t*u64*u64*u64*u64*u64*u64*Slice.t*u64*u64) : val :=
    (#msg.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1,
       (#msg.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2,
          (#msg.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2,
             (#msg.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2,
                (#msg.1.1.1.1.1.1.1.1.1.1.1.1.1.2,
                   (slice_val msg.1.1.1.1.1.1.1.1.1.1.1.1.2,
                      (#msg.1.1.1.1.1.1.1.1.1.1.1.2,
                         (#msg.1.1.1.1.1.1.1.1.1.1.2,
                            (slice_val msg.1.1.1.1.1.1.1.1.1.2,
                               (#msg.1.1.1.1.1.1.1.1.2,
                                  (#msg.1.1.1.1.1.1.1.2,
                                     (#msg.1.1.1.1.1.1.2,
                                        (#msg.1.1.1.1.1.2,
                                           (#msg.1.1.1.1.2,
                                              (#msg.1.1.1.2,
                                                 (slice_val msg.1.1.2,
                                                    (#msg.1.2,
                                                       (#msg.2,
                                                          #()))))))))))))))))))%V.

  Theorem message_val_t msg : val_ty (message_val msg) (struct.t server.Message).
  Proof.
    repeat constructor; auto.
  Qed.

  Hint Resolve message_val_t : core.
  
  Definition message_from_val (v : val) :=
    match v with
    | (#(LitInt MessageType),
         (#(LitInt C2S_Client_Id),
            (#(LitInt C2S_Server_Id),
               (#(LitInt C2S_Client_OperationType),
                  (#(LitInt C2S_Client_Data),
                     (C2S_Client_VersionVector,
                        (#(LitInt S2S_Gossip_Sending_ServerId),
                           (#(LitInt S2S_Gossip_Receiving_ServerId),
                              (S2S_Gossip_Operations,
                                 (#(LitInt S2S_Gossip_Index),
                                    (#(LitInt S2S_Acknowledge_Gossip_Sending_ServerId),
                                       (#(LitInt S2S_Acknowledge_Gossip_Receiving_ServerId),
                                          (#(LitInt S2S_Acknowledge_Gossip_Index),
                                             (#(LitInt S2C_Client_OperationType),
                                                (#(LitInt S2C_Client_Data),
                                                   (S2C_Client_VersionVector,
                                                      (#(LitInt S2C_Server_Id),
                                                         (#(LitInt S2C_Client_Number), #()))))))))))))))))))%V =>
        match ((from_val C2S_Client_VersionVector: option Slice.t),
                 (from_val S2S_Gossip_Operations: option Slice.t),
                   (from_val S2C_Client_VersionVector: option Slice.t)) with
        | (Some s1, Some s2, Some s3) => Some (MessageType,
                                                 C2S_Client_Id,
                                                   C2S_Server_Id,
                                                     C2S_Client_OperationType,
                                                       C2S_Client_Data,
                                                         s1, 
                                                           S2S_Gossip_Sending_ServerId,
                                                             S2S_Gossip_Receiving_ServerId, s2, S2S_Gossip_Index,
                                                               S2S_Acknowledge_Gossip_Sending_ServerId,
                                                                 S2S_Acknowledge_Gossip_Receiving_ServerId,
                                                                   S2S_Acknowledge_Gossip_Index,
                                                                     S2C_Client_OperationType,
                                                                       S2C_Client_Data,
                                                                         s3,
                                                                           S2C_Server_Id,
                                                                             S2C_Client_Number)
        | _ => None
        end
    | _ => None
  end.
  
  Global Instance message_into_val : IntoVal (u64*u64*u64*u64*u64*Slice.t*u64*u64*Slice.t*u64*u64*u64*u64*u64*u64*Slice.t*u64*u64).
  Proof.
    refine {| into_val.to_val := message_val;
             from_val := message_from_val ;
             IntoVal_def := (W64 0, W64 0, W64 0, W64 0, W64 0,
                               IntoVal_def Slice.t, W64 0, W64 0,
                                 IntoVal_def Slice.t,
                                   W64 0, W64 0, W64 0, W64 0, W64 0,
                                     W64 0, IntoVal_def Slice.t,
                                       W64 0, W64 0);
           |}.
    destruct v. repeat destruct p. simpl. f_equal.
    destruct t1. destruct t0. destruct t.
    simpl. auto.
  Defined. 

  #[global] Instance message_into_val_for_type : IntoValForType (u64*u64*u64*u64*u64*Slice.t*u64*u64*Slice.t*u64*u64*u64*u64*u64*u64*Slice.t*u64*u64) (struct.t server.Message).
  Proof. constructor; auto. simpl. repeat split; auto. Qed.
  
  Definition is_message (msgv: u64*u64*u64*u64*u64*Slice.t*u64*u64*Slice.t*u64*u64*u64*u64*u64*u64*Slice.t*u64*u64)
    (msg: Message.t) (msgv_len: nat): iProp Σ :=
    ⌜msgv.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1 = msg.(Message.MessageType)⌝ ∗
    ⌜msgv.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 = msg.(Message.C2S_Client_Id)⌝ ∗
    ⌜msgv.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 = msg.(Message.C2S_Server_Id)⌝ ∗
    ⌜msgv.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2 = msg.(Message.C2S_Client_OperationType)⌝ ∗
    ⌜msgv.1.1.1.1.1.1.1.1.1.1.1.1.1.2 = msg.(Message.C2S_Client_Data)⌝ ∗
    ⌜msgv_len = length msg.(Message.C2S_Client_VersionVector)⌝ ∗
    own_slice_small msgv.1.1.1.1.1.1.1.1.1.1.1.1.2 uint64T (DfracOwn 1) msg.(Message.C2S_Client_VersionVector) ∗
    ⌜msgv.1.1.1.1.1.1.1.1.1.1.1.2 = msg.(Message.S2S_Gossip_Sending_ServerId)⌝ ∗
    ⌜msgv.1.1.1.1.1.1.1.1.1.1.2 = msg.(Message.S2S_Gossip_Receiving_ServerId)⌝ ∗
    operation_slice msgv.1.1.1.1.1.1.1.1.1.2 msg.(Message.S2S_Gossip_Operations) msgv_len ∗
    ⌜msgv.1.1.1.1.1.1.1.1.2 = msg.(Message.S2S_Gossip_Index)⌝ ∗
    ⌜msgv.1.1.1.1.1.1.1.2 = msg.(Message.S2S_Acknowledge_Gossip_Sending_ServerId)⌝ ∗
    ⌜msgv.1.1.1.1.1.1.2 = msg.(Message.S2S_Acknowledge_Gossip_Receiving_ServerId)⌝ ∗
    ⌜msgv.1.1.1.1.1.2 = msg.(Message.S2S_Acknowledge_Gossip_Index)⌝ ∗
    ⌜msgv.1.1.1.1.2 = msg.(Message.S2C_Client_OperationType)⌝ ∗
    ⌜msgv.1.1.1.2 = msg.(Message.S2C_Client_Data)⌝ ∗
    ⌜msgv_len = length msg.(Message.S2C_Client_VersionVector)⌝ ∗
    own_slice_small msgv.1.1.2 uint64T (DfracOwn 1) msg.(Message.S2C_Client_VersionVector) ∗
    ⌜msgv.1.2 = msg.(Message.S2C_Server_Id)⌝ ∗
    ⌜msgv.2 = msg.(Message.S2C_Client_Number)⌝.

  Definition message_slice' (msg_s: Slice.t) (msg: list Message.t)
                              (n: nat) : iProp Σ :=
    ∃ msgs, own_slice msg_s (struct.t server.Message) (DfracOwn 1) msgs ∗
            [∗ list] _ ↦ mv;m ∈ msgs;msg, is_message mv m n.
  
  Definition message_slice (s: Slice.t) (l: list Message.t) (n: nat) : iProp Σ :=
    message_slice' s l n.

  Definition server_val (s:u64*u64*Slice.t*Slice.t*Slice.t*Slice.t*Slice.t*Slice.t) : val :=
    (#s.1.1.1.1.1.1.1,
       (#s.1.1.1.1.1.1.2,
          (slice_val s.1.1.1.1.1.2,
             (slice_val s.1.1.1.1.2,
                (slice_val s.1.1.1.2, 
                   (slice_val s.1.1.2,
                      (slice_val s.1.2,
                         (slice_val s.2,
                            #()))))))))%V.

  Definition is_server (sv: u64*u64*Slice.t*Slice.t*Slice.t*Slice.t*Slice.t*Slice.t) (s: Server.t) (sv_len: nat): iProp Σ :=
    ⌜sv.1.1.1.1.1.1.1 = s.(Server.Id)⌝ ∗
    ⌜sv.1.1.1.1.1.1.2 = s.(Server.NumberOfServers)⌝ ∗
    message_slice sv.1.1.1.1.1.2 s.(Server.UnsatisfiedRequests) sv_len ∗
    ⌜sv_len = length s.(Server.UnsatisfiedRequests)⌝ ∗
    own_slice_small sv.1.1.1.1.2 uint64T (DfracOwn 1) s.(Server.VectorClock) ∗
    operation_slice sv.1.1.1.2 s.(Server.OperationsPerformed) sv_len ∗
    operation_slice sv.1.1.2 s.(Server.MyOperations) sv_len ∗
    operation_slice sv.1.2 s.(Server.PendingOperations) sv_len ∗
    ⌜sv_len = length s.(Server.GossipAcknowledgements)⌝ ∗
    own_slice_small sv.2 uint64T (DfracOwn 1) s.(Server.GossipAcknowledgements).

End heap.
