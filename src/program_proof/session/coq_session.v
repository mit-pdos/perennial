From Perennial.program_proof.session Require Export session_prelude.
From Perennial.program_proof.session Require Export definitions.

Fixpoint coq_compareVersionVector (v1: list u64) (v2: list u64) : bool :=
  match v1 with
  | [] => true
  | cons h1 t1 => match v2 with
                  | [] => true
                  | cons h2 t2 => if (uint.nat h1 <? uint.nat h2) then false else
                                    (coq_compareVersionVector t1 t2)
                  end
                    
  end.

Fixpoint coq_lexicographicCompare (v1 v2: list u64) : bool :=
  match v1 with
  | [] => false 
  | cons h1 t1 => match v2 with
                  | [] => false 
                  | cons h2 t2 => if (uint.Z h1) =? (uint.Z h2) then
                                    (coq_lexicographicCompare t1 t2) else (uint.Z h1) >? (uint.Z h2)
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

Definition coq_oneOffVersionVector (v1: list w64) (v2: list w64) : bool :=
  let (output, canApply) :=
    fold_left (fun (acc: bool * bool) (element: w64 * w64) =>
                 let (e1, e2) := element in
                 let (output, canApply) := acc in
                 if (canApply && (uint.Z e1 + 1 =? uint.Z e2)) then
                   (output && true, false)
                 else
                   if uint.Z e1 >=? uint.Z e2 then
                     (output && true, canApply)
                   else 
                     (false, canApply)) (zip v1 v2) (true, true) in
  output && (negb canApply).

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
  | cons h t => if (coq_lexicographicCompare h.(Operation.VersionVector) i.(Operation.VersionVector)) then (i :: h :: t)%list else (h :: coq_sortedInsert t i)%list
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
                                                                                                                                Server.mk s.(Server.Id) s.(Server.NumberOfServers) s.(Server.UnsatisfiedRequests) VectorClock OperationsPerformed s.(Server.MyOperations) PendingOperations s.(Server.GossipAcknowledgements)) else (index + 1, s)) s.(Server.PendingOperations) (0, s)).

Definition coq_acknowledgeGossip (s: Server.t) (r: Message.t) :=
  let i := r.(Message.S2S_Acknowledge_Gossip_Sending_ServerId) in
  let l : (list u64) := s.(Server.GossipAcknowledgements) in
  let prevGossipAcknowledgementsValue : u64 := match s.(Server.GossipAcknowledgements) !! (uint.nat i) with
                                            | Some x => x
                                            | None => 0
                                            end in
  let newGossipAcknowledgements : u64 := coq_maxTwoInts prevGossipAcknowledgementsValue r.(Message.S2S_Acknowledge_Gossip_Index) in
  let gossipAcknowledgements: (list u64) := (<[uint.nat i := newGossipAcknowledgements]> l) in
  Server.mk s.(Server.Id) s.(Server.NumberOfServers) s.(Server.UnsatisfiedRequests) s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) gossipAcknowledgements.

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

Definition coq_processClientRequest (s: Server.t) (r: Message.t) :
  (bool * Server.t * Message.t) :=
  if (negb (coq_equalSlices (replicate (uint.nat s.(Server.NumberOfServers)) (W64 0)) r.(Message.C2S_Client_VersionVector))) &&
       (negb (coq_compareVersionVector s.(Server.VectorClock) r.(Message.C2S_Client_VersionVector))) then
    (false, s, (Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0))
  else
    if (uint.nat r.(Message.C2S_Client_OperationType) =? 0) then
      let S2C_Client_Data : u64 := coq_getDataFromOperationLog s.(Server.OperationsPerformed) in
      let S2C_Client_VersionVector : (list u64) := s.(Server.VectorClock) in
      let S2C_Client_Number : u64 := r.(Message.C2S_Client_Id) in
      (true, s, (Message.mk 4 0 0 0 0 [] 0 0 [] 0 0 0 0 0 S2C_Client_Data S2C_Client_VersionVector S2C_Client_Number))
    else
      let v : nat := uint.nat (list_lookup_total (uint.nat s.(Server.Id)) s.(Server.VectorClock)) in
      let VectorClock : list u64 := <[(uint.nat s.(Server.Id))%nat := (W64 (v + 1))]>s.(Server.VectorClock) in
      let OperationsPerformed : list Operation.t := s.(Server.OperationsPerformed) ++ [Operation.mk VectorClock r.(Message.C2S_Client_Data)] in
      let MyOperations : list Operation.t := s.(Server.MyOperations) ++ [Operation.mk VectorClock r.(Message.C2S_Client_Data)] in
      let S2C_Client_OperationType := 1 in
      let S2C_Client_Data := 0 in
      let S2C_Client_VersionVector := VectorClock in
      let S2C_Client_Number := r.(Message.C2S_Client_Id) in
      (true, Server.mk s.(Server.Id) s.(Server.NumberOfServers) s.(Server.UnsatisfiedRequests) VectorClock OperationsPerformed MyOperations s.(Server.PendingOperations) s.(Server.GossipAcknowledgements), (Message.mk 4 0 0 0 0 [] 0 0 [] 0 0 0 0 1 S2C_Client_Data S2C_Client_VersionVector S2C_Client_Number)).

Definition coq_processRequest (s: Server.t) (r: Message.t) : (Server.t * list Message.t) :=
  match (uint.nat r.(Message.MessageType))%nat with
  | 0%nat =>
      let '(succeeded, server, reply) := coq_processClientRequest s r in
      if succeeded then
        (server, [reply])
      else
        let UnsatisfiedRequests := s.(Server.UnsatisfiedRequests) ++ [r] in 
        let server := Server.mk s.(Server.Id) s.(Server.NumberOfServers) UnsatisfiedRequests s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) s.(Server.GossipAcknowledgements) in
        (server, [])
  | 1%nat =>
      let s := coq_receiveGossip s r in
      let outGoingRequests := [Message.mk 0 0 0 0 0 [] 0 0 [] 0 (s.(Server.Id)) (r.(Message.S2S_Gossip_Sending_ServerId)) (r.(Message.S2S_Gossip_Index)) 0 0 [] 0] in
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
      let s := Server.mk s.(Server.Id) s.(Server.NumberOfServers) UnsatisfiedRequests s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) s.(Server.GossipAcknowledgements) in
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
                                              let message := Message.mk 1 0 0 0 0 [] S2S_Gossip_Sending_ServerId S2S_Gossip_Receiving_ServerId S2S_Gossip_Operations S2S_Gossip_Index 0 0 0 0 0 [] 0 in acc ++ [message]
                                            else
                                              acc) (seq 0 (uint.nat s.(Server.NumberOfServers)))  [] in
      (s, outGoingRequests)
        
  | _ => (s, [])
  end.

Section REDEFINE.

  Import SessionPrelude.

  Lemma redefine_coq_lexicographicCompare :
    coq_lexicographicCompare = vectorGt.
  Proof.
    reflexivity.
  Defined.

  Lemma redefine_coq_equalSlices :
    coq_equalSlices = vectorEq.
  Proof.
    reflexivity.
  Defined.

  Definition Operation_wf (len : nat) : Operation.t -> Prop :=
    fun o => Forall (fun _ => True) (o .(Operation.VersionVector)) /\ length (o .(Operation.VersionVector)) = len.

  #[global]
  Instance hsEq_Operation (len : nat) : hsEq Operation.t (well_formed := Operation_wf len) :=
    hsEq_preimage _.

  #[global]
  Instance hsOrd_Operation (len : nat) : hsOrd Operation.t (hsEq := hsEq_Operation len) :=
    hsOrd_preimage _.

  Lemma redefine_coq_sortedInsert (len : nat) :
    coq_sortedInsert = sortedInsert (hsOrd := hsOrd_Operation len).
  Proof.
    reflexivity.
  Defined.

  #[local] Hint Resolve @Forall_True : core.

  Lemma aux0_lexicographicCompare (l1 l2 l3: list u64) :
    coq_lexicographicCompare l2 l1 = true ->
    coq_lexicographicCompare l3 l2 = true ->
    coq_lexicographicCompare l3 l1 = true.
  Proof.
    rewrite redefine_coq_lexicographicCompare. 
    intros. eapply vectorGt_transitive; eauto.
  Qed.

  Lemma aux1_lexicographicCompare (l1 l2: list u64) :
    length l1 = length l2 -> 
    l1 ≠ l2 ->
    (coq_lexicographicCompare l2 l1 = false <-> coq_lexicographicCompare l1 l2 = true).
  Proof.
    rewrite redefine_coq_lexicographicCompare. remember (length l1) as len eqn: len_eq.
    pose proof (ltProp_trichotomy (hsOrd := hsOrd_vector len) l1 l2) as claim. simpl in claim.
    symmetry in len_eq. intros len_eq'. symmetry in len_eq'.
    specialize (claim (conj (Forall_True _) len_eq) (conj (Forall_True _) len_eq')).
    destruct claim as [H_lt | [H_eq | H_gt]].
    - rewrite H_lt. intros NE. split.
      + congruence.
      + intros l1_gt_l2. contradiction (ltProp_irreflexivity (hsOrd := hsOrd_vector len) l1 l1); eauto.
        * eapply eqProp_reflexivity; eauto.
        * eapply ltProp_transitivity with (y := l2); eauto.
    - intros NE. contradiction NE. clear NE. rewrite <- vectorEq_true_iff; eauto 2.
      change (eqb (hsEq := hsEq_vector len) l1 l2 = true). rewrite eqb_eq; eauto 2.
    - rewrite H_gt. intros NE. split.
      + congruence.
      + intros _. change (ltb (hsOrd := hsOrd_vector len) l1 l2 = false).
        rewrite ltb_nlt; eauto 2. intros NLT. change (ltb (hsOrd := hsOrd_vector len) l2 l1 = true) in H_gt.
        rewrite ltb_lt in H_gt; eauto 2. contradiction (ltProp_irreflexivity (hsOrd := hsOrd_vector len) l1 l1); eauto.
        * eapply eqProp_reflexivity; eauto.
        * eapply ltProp_transitivity with (y := l2); eauto.
  Qed.

  Lemma aux3_lexicographicCompare (l1 l2: list u64) :
    length l1 = length l2 -> 
    coq_lexicographicCompare l2 l1 = false ->
    coq_lexicographicCompare l1 l2 = false ->
    l1 = l2.
  Proof.
    rewrite redefine_coq_lexicographicCompare. intros. rewrite <- vectorEq_true_iff; eauto 2.
    change (eqb (hsEq := hsEq_vector (length l1)) l1 l2 = true). rewrite eqb_eq; eauto 2.
    pose proof (ltProp_trichotomy (hsOrd := hsOrd_vector (length l1)) l1 l2) as [H_lt | [H_eq | H_gt]]; eauto.
    - rewrite <- ltb_lt in H_lt; eauto 2. simpl in *. congruence.
    - rewrite <- ltb_lt in H_gt; eauto 2. simpl in *. congruence.
  Qed.

  Lemma aux4_lexicographicCompare (l1 l2: list u64) :
    coq_lexicographicCompare l1 l2 = true ->
    coq_equalSlices l1 l2 = false.
  Proof.
    rewrite redefine_coq_lexicographicCompare. rewrite redefine_coq_equalSlices.
    intros. eapply vectorGt_implies_not_vectorEq; eauto 2.
  Qed.

  Lemma aux5_lexicographicCompare (l1 l2: list u64) :
    coq_equalSlices l1 l2 = true ->
    coq_lexicographicCompare l1 l2 = false.
  Proof.
    rewrite redefine_coq_lexicographicCompare. rewrite redefine_coq_equalSlices.
    intros. eapply vectorEq_implies_not_vectorGt; eauto 2.
  Qed.

  Lemma aux0_equalSlices (l1 l2: list u64) :
    length l1 = length l2 ->
    coq_equalSlices l1 l2 = true ->
    l1 = l2.
  Proof.
    rewrite redefine_coq_equalSlices. intros. rewrite <- vectorEq_true_iff; eauto 2.
  Qed.

  Lemma aux1_equalSlices (l1 l2: list u64) :
    length l1 = length l2 ->
    coq_equalSlices l1 l2 = false ->
    l1 ≠ l2.
  Proof.
    rewrite redefine_coq_equalSlices. intros. rewrite <- vectorEq_true_iff; eauto 2.
    rewrite H0; congruence.
  Qed.

  Lemma aux2_equalSlices (l1 l2: list u64) (b: bool) :
    length l1 = length l2 ->
    coq_equalSlices l1 l2 = b ->
    coq_equalSlices l2 l1 = b.
  Proof.
    rewrite redefine_coq_equalSlices. intros. subst b. eapply (eqb_comm (hsEq_A := hsEq_vector (length l1))); eauto.
  Qed.

  Lemma aux3_equalSlices (l: list u64) :
    coq_equalSlices l l = true.
  Proof.
    change (coq_equalSlices l l) with (eqb (hsEq := hsEq_vector (length l)) l l).
    rewrite eqb_eq; eauto 2. eapply eqProp_reflexivity; eauto 2.
  Qed.

End REDEFINE.

Section heap.

  Context `{hG: !heapGS Σ}.

  Lemma Forall_Operation_wf l ops (n : nat)
    : ([∗ list] opv;o ∈ ops; l, is_operation opv o n)%I ⊢@{iProp Σ} (⌜Forall (Operation_wf n) l⌝)%I.
  Proof.
    revert ops. induction l as [ | hd tl IH]; intros ops.
    - iIntros "H_big_sepL2". iPureIntro. eauto.
    - iIntros "H_big_sepL2". iPoseProof (big_sepL2_cons_inv_r with "H_big_sepL2") as "(%hd' & %tl' & -> & H_hd & H_tl)".
      iDestruct "H_hd" as "(%H1 & %H2 & H3)". iClear "H3".
      iAssert ⌜Forall (Operation_wf n) tl⌝%I as "%YES1".
      { iApply IH. iExact "H_tl". }
      iPureIntro. econstructor.
      + split.
        * eapply SessionPrelude.Forall_True.
        * done.
      + exact YES1.
  Qed.

  Lemma pers_big_sepL2_is_operation l ops (n : nat)
    : ([∗ list] opv;o ∈ ops;l, is_operation opv o n)%I ⊢@{iProp Σ} (<pers> ([∗ list] opv;o ∈ ops;l, is_operation opv o n))%I.
  Proof.
    iIntros "H_big_sepL2". iApply (big_sepL2_persistently). iApply (big_sepL2_mono (λ k, λ y1, λ y2, is_operation y1 y2 n)%I).
    - intros. iIntros "#H". iApply intuitionistically_into_persistently_1. iModIntro. done.
    - done.
  Qed.

End heap.
