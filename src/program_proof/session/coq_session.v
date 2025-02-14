From Perennial.program_proof Require Import std_proof. 
From Perennial.goose_lang.ffi.grove_ffi Require Export impl.
From Perennial.program_logic Require Export atomic.
From Perennial.program_proof Require Export proof_prelude.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.goose_lang.lib Require Import struct.struct into_val.
From RecordUpdate Require Import RecordSet.
From Perennial.goose_lang Require Import prelude.

Module Operation.

  Record t :=
    mk {
        VersionVector: list u64 ;
        Data:          u64 ;
      }.

End Operation.

Module Message.

  Record t :=
    mk {
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

Fixpoint coq_compareVersionVector (v1: list u64) (v2: list u64) : bool :=
  match v1 with
  | [] => true
  | cons h1 t1 => match v2 with
                  | [] => true
                  | cons h2 t2 => if (uint.nat h1 <? uint.nat h2) then false else
                                    (coq_compareVersionVector t1 t2)
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

Definition coq_maxTwoInts (x: w64) (y: w64) :=
  if uint.Z x >? uint.Z y then x else y. 

Fixpoint coq_maxTS (t1: list u64) (t2: list u64) : list u64 :=
  match t1 with
  | [] => []
  | cons hd1 tl1 => match t2 with
                    | [] => [] 
                    | cons hd2 tl2 => (cons (coq_maxTwoInts hd1 hd2) (coq_maxTS tl1 tl2))
                    end
  end.


Fixpoint coq_oneOffVersionVector (v1: list w64) (v2: list w64) (index: nat) (canApply: bool) : bool :=
  match v1 with
  | [] => true
  | cons h1 t1 => match v2 with
                  | [] => true
                  | cons h2 t2 => (if (canApply && (uint.Z h1 + 1 =? uint.Z h2)) then (coq_oneOffVersionVector t1 t2 (index + 1) (false)) else false)
                  end
  end.


Fixpoint coq_equalSlices (s1: list u64) (s2: list u64) :=
  match s1 with
  | [] => true
  | cons h1 t1 => match s2 with
                  | [] => true
                  | cons h2 t2 => if (negb ((uint.Z h1) =? (uint.Z h2)))
                                  then false else (coq_equalSlices t1 t2)
                  end
  end.

Definition coq_equalOperations (o1 : Operation.t) (o2 : Operation.t) :=
  (coq_equalSlices o1.(Operation.VersionVector) o2.(Operation.VersionVector)) && ((uint.nat o1.(Operation.Data)) =? (uint.nat (o2.(Operation.Data)))).

Fixpoint coq_sortedInsert (l : list Operation.t) (i : Operation.t) :=
  match l with
  | [] => [i]
  | cons h t => if (coq_lexiographicCompare h.(Operation.VersionVector) i.(Operation.VersionVector)) then (i :: h :: t)%list else (h :: coq_sortedInsert t i)%list
  end.

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

Definition coq_deleteAtIndexOperation (o : list Operation.t) index :=
  (take index o) ++ (drop (index + 1) o).

Definition coq_deleteAtIndexMessage (m : list Message.t) index :=
  (take index m) ++ (drop (index + 1) m).

Definition coq_getDataFromOperationLog (l: list Operation.t) :=
  match list_lookup (uint.nat ((length l) - 1)) l with
  | Some v => v.(Operation.Data)
  | None => 0
  end. 

Definition coq_receiveGossip (s: Server.t) (r: Message.t) : Server.t :=
  if length (r.(Message.S2S_Gossip_Operations)) =? 0 then
    s
  else
    let pendingOperations := coq_mergeOperations s.(Server.PendingOperations) r.(Message.S2S_Gossip_Operations) in
    snd (fold_left (fun (acc: Z * Server.t) (element: Operation.t) =>
                      let (index, acc) := acc in 
                      if coq_oneOffVersionVector acc.(Server.VectorClock) element.(Operation.VersionVector) 0 true then
                        let OperationsPerformed := coq_mergeOperations acc.(Server.OperationsPerformed) [element] in
                        let VectorClock := coq_maxTS acc.(Server.VectorClock) element.(Operation.VersionVector) in
                        let PendingOperations := coq_deleteAtIndexOperation s.(Server.PendingOperations) (uint.nat index) in (index + 1,
                                                                                                                                Server.mk s.(Server.Id) s.(Server.NumberOfServers) s.(Server.UnsatisfiedRequests) VectorClock OperationsPerformed s.(Server.MyOperations) PendingOperations s.(Server.GossipAcknowledgements) s.(Server.SeenRequests)) else (index + 1, s)) s.(Server.PendingOperations) (0, s)).


Definition coq_acknowledgeGossip (s: Server.t) (r: Message.t) :=
  let i := r.(Message.S2S_Acknowledge_Gossip_Sending_ServerId) in
  let l : (list u64) := s.(Server.GossipAcknowledgements) in
  let gossipAcknowledgements: (list u64) :=
    <[uint.nat i := r.(Message.S2S_Gossip_Index)]> l in
  Server.mk s.(Server.Id) s.(Server.NumberOfServers) s.(Server.UnsatisfiedRequests) s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) gossipAcknowledgements s.(Server.SeenRequests).

Definition coq_getGossipOperations (s: Server.t) (serverId: u64) : (list Operation.t) :=
  snd (fold_left (fun (acc: Z * list Operation.t) element =>
                    let (index, acc) := acc in
                    match lookup (uint.nat serverId) (s.(Server.GossipAcknowledgements)) with
                    | Some v => if index >=? (uint.nat v) then
                                  (index + 1, acc ++ [element])
                                else (index + 1, acc)
                    | None => (index + 1, acc)
                    end)
         [] (0, s.(Server.MyOperations))).

Definition coq_checkIfDuplicateRequest (s: Server.t) (r: Message.t) : bool :=
  match s.(Server.SeenRequests) !! (uint.nat (r.(Message.C2S_Client_Id))) with
  | Some v => (uint.Z v) >=? (uint.Z r.(Message.C2S_Client_RequestNumber))
  | None => false
  end.

Definition coq_processClientRequest (s: Server.t) (r: Message.t) :
  (bool * Server.t * Message.t) :=
  if (negb (coq_compareVersionVector s.(Server.VectorClock) r.(Message.C2S_Client_VersionVector))) || (coq_checkIfDuplicateRequest s r) then
    (false, s, (Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0))
  else
    if (uint.nat r.(Message.C2S_Client_OperationType) =? 0) then
      let S2C_Client_Data : u64 := coq_getDataFromOperationLog s.(Server.OperationsPerformed) in
      let S2C_Client_VersionVector : (list u64) :=
        coq_maxTS r.(Message.C2S_Client_VersionVector) s.(Server.VectorClock) in
      let S2C_Client_Number : u64 := r.(Message.C2S_Client_Id) in
      let S2C_Client_RequestNumber : u64 := r.(Message.C2S_Client_RequestNumber) in
      (true, s, (Message.mk 4 0 0 0 0 [] 0 0 [] 0 0 0 0 0 S2C_Client_Data S2C_Client_VersionVector S2C_Client_RequestNumber S2C_Client_Number))
    else
      let v : nat := uint.nat (list_lookup_total (uint.nat s.(Server.Id)) s.(Server.VectorClock)) in
      let VectorClock : list u64 := <[(uint.nat s.(Server.Id))%nat := (W64 (v + 1))]>s.(Server.VectorClock) in
      let OperationsPerformed : list Operation.t := cons (Operation.mk VectorClock r.(Message.C2S_Client_Data)) s.(Server.OperationsPerformed) in
      let MyOperations : list Operation.t := cons (Operation.mk VectorClock r.(Message.C2S_Client_Data)) s.(Server.MyOperations) in
      let SeenRequests := <[(uint.nat r.(Message.C2S_Client_Id))%nat := r.(Message.C2S_Client_RequestNumber)]>s.(Server.SeenRequests) in
      let S2C_Client_OperationType := 1 in
      let S2C_Client_Data := coq_getDataFromOperationLog s.(Server.OperationsPerformed) in
      let S2C_Client_VersionVector := s.(Server.VectorClock) in
      let S2C_Client_Number := r.(Message.C2S_Client_Id) in
      let S2C_Client_RequestNumber := r.(Message.C2S_Client_RequestNumber) in
      (true, Server.mk s.(Server.Id) s.(Server.NumberOfServers) s.(Server.UnsatisfiedRequests) VectorClock OperationsPerformed MyOperations s.(Server.PendingOperations) s.(Server.GossipAcknowledgements) SeenRequests, (Message.mk 4 0 0 0 0 [] 0 0 [] 0 0 0 0 1 S2C_Client_Data S2C_Client_VersionVector S2C_Client_RequestNumber S2C_Client_Number)).

Definition coq_processRequest (s: Server.t) (r: Message.t) : (Server.t * list Message.t) :=
  match (uint.nat r.(Message.MessageType))%nat with
  | 0%nat =>
      let '(succeeded, server, reply) := coq_processClientRequest s r in
      if succeeded then
        (server, [reply])
      else
        (* change that *)
        let UnsatisfiedRequests := s.(Server.UnsatisfiedRequests) ++ [r] in 
        let server := Server.mk s.(Server.Id) s.(Server.NumberOfServers) UnsatisfiedRequests s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) s.(Server.GossipAcknowledgements) s.(Server.SeenRequests) in
        (server, [])
  | 1%nat =>
      let s := coq_receiveGossip s r in
      let outGoingRequests := [Message.mk 0 0 0 0 0 [] 0 0 [] 0 (s.(Server.Id)) (r.(Message.S2S_Gossip_Sending_ServerId)) (r.(Message.S2S_Gossip_Index)) 0 0 [] 0 0] in
      let '(_, deletedIndex, outGoingRequests) := fold_left (fun (acc: nat * list nat * list Message.t) element =>
                                           let '(index, deletedIndex, acc) := acc in
                                           let '(succeeded, server, reply) := coq_processClientRequest s r in
                                           if succeeded then
                                             ((index + 1)%nat, deletedIndex ++ [index], acc ++ [reply])
                                           else
                                             ((index + 1)%nat, deletedIndex, acc)) s.(Server.UnsatisfiedRequests) (0%nat, [], outGoingRequests) in
      let remainingIndexes := list_difference (seq 0 (length s.(Server.UnsatisfiedRequests))) deletedIndex in 
      let UnsatisfiedRequests := 
        fold_left (fun acc index =>
                     match (s.(Server.UnsatisfiedRequests) !! index) with
                     | Some v => acc ++ [v]
                     | None => acc
                     end
          ) remainingIndexes [] in
      let s := Server.mk s.(Server.Id) s.(Server.NumberOfServers) UnsatisfiedRequests s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) s.(Server.GossipAcknowledgements) s.(Server.SeenRequests) in
      (s, outGoingRequests)
  | 2%nat =>
      let s := coq_acknowledgeGossip s r in
      (s, [])
  | 3%nat =>
      let outGoingRequests := fold_left (fun acc (index: nat) =>
                                           if (negb (index =? (uint.nat s.(Server.Id)))) then
                                             let S2S_Gossip_Sending_ServerId := s.(Server.Id) in
                                              let S2S_Gossip_Receiving_ServerId := index in
                                              let S2S_Gossip_Operations := coq_getGossipOperations s index in
                                              let S2S_Gossip_Index := length (s.(Server.MyOperations)) in
                                              let message := Message.mk 1 0 0 0 0 [] S2S_Gossip_Sending_ServerId S2S_Gossip_Receiving_ServerId S2S_Gossip_Operations S2S_Gossip_Index 0 0 0 0 0 [] 0 0 in acc ++ [message]
                                            else
                                              acc) (seq 0 (uint.nat s.(Server.NumberOfServers)))  [] in
      (s, outGoingRequests)
        
  | _ => (s, [])
  end.


