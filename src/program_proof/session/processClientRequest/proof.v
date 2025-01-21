From Goose.github_com.session Require Import processClientRequest.
From Perennial.program_proof Require Import std_proof. 
From Perennial.goose_lang.ffi.grove_ffi Require Export impl.
From Perennial.program_logic Require Export atomic.
From Perennial.program_proof Require Export proof_prelude.
From Perennial.program_proof Require Import grove_prelude.
From RecordUpdate Require Import RecordSet.
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang.lib.list Require Import list.
From Perennial.goose_lang.lib Require Import map.impl list.impl list.list_slice slice.typed_slice.

Local Lemma Z_scope_test : (0%Z) + (0%Z) = 0%Z.
Proof. done. Qed.

Module Operation.
  
    Record t :=
      mk {
          operationType: u64 ;
          versionVector: list u64 ;
          data: u64 ;
        }.

End Operation.

Module Server.

  Record t :=
    mk {
        id: u64 ;
        numberOfServers: u64 ;
        vectorClock: list u64 ;
        operationsPerformed: list Operation.t ;
        myOperations: list Operation.t ;
        pendingOperations: list Operation.t ;
        data: u64 ;
        gossipAcknowledgements: list u64 ;
      }.


  
  Record val_t :=
     mkServer {
        v_id: u64 ;
        v_numberOfServers: u64 ;
        v_vectorClock: Slice.t ;
        v_operationsPerformed: Slice.t ;
        v_myOperations: Slice.t ;
        v_pendingOperations: Slice.t ;
        v_data: w64 ;
        v_gossipAcknowledgments: Slice.t ;
      }.

End Server.

Module Request.

  Record t :=
    mk {
        requestType: u64 ;
        client_OperationType: u64 ;
	client_SessionType: u64 ;
	client_Data: u64;
	client_Vector: list u64 ;

	receive_Gossip_ServerId: u64 ;
	receive_Gossip_Operations: list Operation.t ;

	acknowledge_Gossip_ServerId: u64 ;
	acknowledge_Gossip_Index: u64 ;

	receiver_ServerId: u64
      }.

  Record val_t :=
    mkRequest {
        v_RequestType: u64 ;
        v_Client_OperationType: u64 ;
	v_Client_SessionType: u64 ;
	v_Client_Data: u64;
	v_Client_Vector: Slice.t ;

	v_Receive_Gossip_ServerId: u64 ;
	v_Receive_Gossip_Operations: Slice.t ;

	v_Acknowledge_Gossip_ServerId: u64 ;
	v_Acknowledge_Gossip_Index: u64 ;

	v_Receiver_ServerId: u64
      }.

End Request.
  
Module Reply.

  Record t :=
    mk {
        replyType: u64 ;

	client_Succeeded: bool ;
	client_OperationType: u64 ;
	client_Data: u64 ;
	client_ReadVector: list u64 ;
	client_WriteVector: list u64 ;
      }.

End Reply.

Section heap.
  
  Context `{hG: !heapGS Σ}.

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
          ⌜length xs = length ys⌝ ∗
          ⌜length xs < 2^64⌝
    }}}
       compareVersionVector x y 
      {{{
            r , RET #r;
            ⌜r = coq_compareVersionVector xs ys⌝ ∗ 
            own_slice x uint64T (DfracOwn 1) xs ∗
            own_slice y uint64T (DfracOwn 1) ys ∗
            ⌜length xs = length ys⌝ ∗
            ⌜length xs < 2^64⌝
      }}}.
  Proof.
  Admitted.
  
  Definition coq_maxTwoInts (x: w64) (y: w64) :=
    if uint.Z x >? uint.Z y then x else y.

  Lemma wp_maxTwoInts (x: w64) (y: w64) :
    {{{
          True
    }}}
      maxTwoInts #x #y 
      {{{
            r , RET #r;
            ⌜r = coq_maxTwoInts x y⌝
      }}}.
  Proof.
    iIntros (Φ) "H H1".
    unfold maxTwoInts. wp_pures.
    wp_if_destruct.
    - iModIntro. iApply "H1". iPureIntro.
      unfold coq_maxTwoInts. apply Z.gtb_lt in Heqb.
      rewrite Heqb. auto.
    - iModIntro. iApply "H1". iPureIntro.
      unfold coq_maxTwoInts. 
      assert (uint.Z y >= uint.Z x) by word.
      assert (uint.Z x >? uint.Z y = false) by word.
      rewrite H0.
      auto.
  Qed.

  Fixpoint coq_maxTS (t1: list w64) (t2: list w64) : list w64 :=
    match t1 with
    | [] => []
    | cons hd1 tl1 => match t2 with
                      | [] => [] 
                      | cons hd2 tl2 => if (uint.Z hd1) >? (uint.Z hd2) then
                                          (cons hd1 (coq_maxTS tl1 tl2)) else (cons hd2 (coq_maxTS tl1 tl2))
                      end
    end.
  
  Lemma wp_maxTS (x: Slice.t) (xs: list w64) (y: Slice.t) (ys: list w64) :
    {{{
          own_slice x uint64T (DfracOwn 1) xs ∗
            own_slice y uint64T (DfracOwn 1) ys ∗
            ⌜length xs = length ys⌝ ∗ ⌜length xs < 2^64⌝
    }}}
      maxTS x y 
      {{{
            (s': Slice.t), RET slice_val s'; 
            own_slice s' uint64T (DfracOwn 1) (coq_maxTS xs ys) ∗ 
              own_slice x uint64T (DfracOwn 1) xs ∗
              own_slice y uint64T (DfracOwn 1) ys 
      }}}.
  Proof.
  Admitted.

  (* What does it mean to have an equivalent
     request struct
   *)

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

    Definition is_operation (opv: u64*Slice.t*u64) (op: Operation.t): iProp Σ :=
      ⌜opv.1.1 = op.(Operation.operationType)⌝ ∗
      ⌜opv.2 = op.(Operation.data)⌝ ∗
      own_slice opv.1.2 uint64T (DfracOwn 1) op.(Operation.versionVector)%I.
    (* How do I make this persistent? *)

    (* 
    Global Instance is_operation_persistent opv op : Persistent (is_operation opv op).
    Proof. apply _. Qed.
     *)

    Definition operation_slice' (q:dfrac) (op_s: Slice.t) (op: list Operation.t): iProp Σ :=
      ∃ ops , own_slice op_s (struct.t Operation) (DfracOwn 1) (ops) ∗
              [∗ list] _ ↦ opv;o ∈ ops;op,
    □ (is_operation opv o).

  Definition operation_slice (s: Slice.t) (ls: list Operation.t): iProp Σ :=
    operation_slice' (DfracOwn 1) s ls.
  
  Definition is_server (s: Server.val_t) (q: dfrac) (ser: Server.t) : iProp Σ :=
    (operation_slice s.(Server.v_myOperations) (ser.(Server.myOperations)) ∗
     own_slice s.(Server.v_gossipAcknowledgments) (uint64T) (DfracOwn 1) ser.(Server.gossipAcknowledgements))%I.

  Global Instance request_into_val : IntoVal (u64*Slice.t*u64).
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

  Definition is_request (r: Request.val_t) (q: dfrac) (req: Request.t) : iProp Σ :=
    ⌜req.(Request.acknowledge_Gossip_ServerId) = r.(Request.v_Acknowledge_Gossip_ServerId)⌝ ∗
    ⌜req.(Request.acknowledge_Gossip_Index) = r.(Request.v_Acknowledge_Gossip_Index)⌝.

  Definition coq_getGossipOperations (server: Server.t) (serverId: u64) :=
    let x := list_lookup_total (uint.nat serverId) (server.(Server.gossipAcknowledgements)) in
    drop (uint.nat x) (server.(Server.myOperations)).

  Definition server_val (s: Server.val_t) : val :=
    (#(s.(Server.v_id)),
       ((#s.(Server.v_numberOfServers)),
          ((slice_val s.(Server.v_vectorClock),
              ((slice_val s.(Server.v_operationsPerformed)),
                 ((slice_val s.(Server.v_myOperations)),
                    ((slice_val s.(Server.v_pendingOperations)),
                       ((#s.(Server.v_data)),
                          ((slice_val s.(Server.v_gossipAcknowledgments)),
                             #())))))))))%V.

  Definition request_val (r: Request.val_t) : val :=
    (#(r.(Request.v_RequestType)),
       ((#r.(Request.v_Client_OperationType)),
          ((#r.(Request.v_Client_SessionType),
              ((#r.(Request.v_Client_Data)),
                 ((slice_val r.(Request.v_Client_Vector)),
                    ((#r.(Request.v_Receive_Gossip_ServerId)),
                       ((slice_val r.(Request.v_Receive_Gossip_Operations)),
                          ((#r.(Request.v_Acknowledge_Gossip_ServerId)),
                             ((#r.(Request.v_Acknowledge_Gossip_Index)),
                                (#r.(Request.v_Receiver_ServerId),
                                   #())))))))))))%V.

  (* what is the difference between readonly and discarding the frac *)
  (* I think points-to is not *)

  (* not exactly sure what the difference between readonly,
       <pers>, Persistent and □ is *)
  
  Lemma wp_getGossipOperations (s: Server.val_t) (ser: Server.t) (serverId: u64) :
    {{{
          is_server s (DfracOwn 1) ser ∗
          ⌜uint.nat serverId < length (ser.(Server.gossipAcknowledgements))⌝%nat
                                      (* We need to add another precondition that x is less than the length *)
                                      
    }}}
      getGossipOperations (server_val s) #serverId
      {{{
            (r: Slice.t) , RET slice_val (r);
            is_server s (DfracOwn 1) ser ∗
            ∃ rs, operation_slice r rs ∗ ⌜rs = coq_getGossipOperations ser serverId⌝
      }}}.
  Proof.
    iIntros (Φ) "(H & %H1) H2". unfold getGossipOperations.
    wp_pures. unfold is_server. iDestruct "H" as "[H H1]".
    iDestruct (own_slice_sz with "H1") as %Hsz.    
    iDestruct "H1" as "[H1 H3]".
    apply list_lookup_lt in H1.
    destruct H1.
    wp_bind (NewSlice _ _).
    wp_apply wp_NewSlice.
    iIntros (s') "H4".
    wp_pures.
    wp_bind (SliceSkip _ _ _)%E.
    iNamed "H".
    iDestruct "H" as "[H #H5]".
    iDestruct "H" as "[H H6]".
    iDestruct (big_sepL2_length with "H5") as %len.
     iApply own_slice_small_take_drop in "H".
     { assert ((uint.nat x <= uint.nat s.(Server.v_myOperations).(Slice.sz))%nat) by admit. eassumption. }
     iDestruct "H" as "[H H7]".
    wp_apply (wp_SliceGet with "[H1]").
    - iFrame. iPureIntro. eassumption.
    - iIntros "H1".
      wp_pures.
      wp_apply (wp_SliceSkip with "[H H3 H6 H4 H1 H2 H7]").
      + admit.
      + iModIntro. wp_apply (wp_SliceAppendSlice with "[H H4]"); auto.
        * simpl. iFrame. 
        * iIntros (s'') "H".
          iApply "H2". iDestruct "H" as "[H H2]". iSplitL "H2 H7 H1 H6 H3".
          { unfold operation_slice. unfold operation_slice'.
            iSplitL "H7 H2 H6".
            - iExists ops. iFrame. iApply own_slice_combine in "H7". 
              + admit.
              + iApply "H7" in "H2". rewrite take_drop. auto.
            - iFrame.
          }
          { iExists (drop (uint.nat x) ser.(Server.myOperations)).
            iSplitL; iFrame.
            - iDestruct (big_sepL2_suffix with "[H5]") as "H".
                + assert (drop (uint.nat x) ops `suffix_of` ops).
                 * unfold suffix. exists (take (uint.nat x) ops).
                    rewrite take_drop. auto. 
                  * eassumption. 
                + assert (drop (uint.nat x) (ser.(Server.myOperations)) `suffix_of` (ser.(Server.myOperations))).
                  * unfold suffix. exists (take (uint.nat x)
                                             (ser.(Server.myOperations))). rewrite take_drop. auto. 
                  * eassumption. 
                + repeat rewrite length_drop. word.
                + iApply "H5".
                + simpl. iApply "H".
            - unfold coq_getGossipOperations. iPureIntro.
                assert ((list_lookup_total (uint.nat serverId)
                               ser.(Server.gossipAcknowledgements)) = x). { 
                  apply list_lookup_total_correct. auto. }
                rewrite H0. simpl. auto.
  Admitted.
  
  Definition coq_acknowledgeGossip (server: Server.t) (request: Request.t) :=
    (* change the index of the list *)
    let i := request.(Request.acknowledge_Gossip_ServerId) in
    let l : (list u64) := server.(Server.gossipAcknowledgements) in
    let gossipAcknowedgements: (list u64) :=
      <[uint.nat i := request.(Request.acknowledge_Gossip_Index)]> l in
    Server.mk 
      server.(Server.id) server.(Server.numberOfServers) server.(Server.vectorClock) server.(Server.operationsPerformed) server.(Server.myOperations) server.(Server.pendingOperations) server.(Server.data) gossipAcknowedgements.


  Lemma wp_acknowledgeGossip (s: Server.val_t) (ser: Server.t) (r: Request.val_t) (req: Request.t) :
    {{{
          is_server s (DfracOwn 1) ser ∗
          is_request r (DfracOwn 1) req
    }}}
      acknowledgeGossip (server_val s) (request_val r)
      {{{
            s0, RET (server_val s0);
            is_server s0 (DfracOwn 1) (coq_acknowledgeGossip ser req)
      }}}.
  Proof.
    iIntros (Φ) "(H & %H1) H2". unfold acknowledgeGossip.
    wp_pures.
    wp_bind (SliceSet _ _ _ _)%E.
    unfold is_server.
    iDestruct "H" as "[H [H1 H3]]".
    wp_apply (slice.wp_SliceSet with "[H1]").
    - iSplitL "H1".
      + iFrame.
      + iSplitR; auto.
        admit. (* need to put in precondition *)
    - iIntros "H1". wp_pures. iModIntro. iApply "H2".
      iSplitL "H".
      + iFrame.
      + unfold own_slice. unfold slice.own_slice. iSplitL "H1".
        * simpl.
          assert ((<[uint.nat r.(Request.v_Acknowledge_Gossip_ServerId):=#
                                  r.(Request.v_Acknowledge_Gossip_Index)]>
                     (list.untype ser.(Server.gossipAcknowledgements))) =
                  (list.untype
                     (<[uint.nat req.(Request.acknowledge_Gossip_ServerId):=
                          req.(Request.acknowledge_Gossip_Index)]>
                        ser.(Server.gossipAcknowledgements)))). {
            destruct H1. rewrite H. rewrite H0. unfold list.untype.
            simpl. rewrite list_fmap_insert. auto.
          }
          rewrite H. iFrame.
        * iFrame.
  Admitted.

End heap.
  

                        
