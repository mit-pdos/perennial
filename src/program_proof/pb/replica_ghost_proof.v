From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import pb.
From Perennial.program_proof.pb Require Export replica_ghost_defns.

Section replica_ghost_proof.

Context `{!heapGS Σ}.
Context `{!rpcregG Σ}.
Implicit Type γ:pb_names.

Lemma append_new_ghost {rid} γ r (newCn:u64) newLog :
  int.Z r.(cn) < int.Z newCn ∨ length r.(opLog) ≤ length newLog →
  "Hown" ∷ own_Replica_ghost rid γ r ∗
  "#HnewProp" ∷ proposal_lb γ newCn newLog
  ={⊤}=∗
  own_Replica_ghost rid γ (mkReplica newLog newCn) ∗
  accepted_lb γ newCn rid newLog.
Proof.
Admitted.

(*
  If we increase a replica's cn, want to know that we can keep its commitIdx
  unchanged. This is true because the proposal for cn' will need to have all of
  the committed entries from all previous cn's.
 *)
Lemma maintain_committer_ghost γ r c newCn newLog :
  int.Z r.(cn) ≤ int.Z newCn →
  int.Z r.(cn) < int.Z newCn ∨ length r.(opLog) ≤ length newLog →
  "#HnewProp" ∷ proposal_lb γ newCn newLog ∗
  "#Hownc" ∷ own_Committer_ghost γ r c
  ={⊤}=∗
  own_Committer_ghost γ (mkReplica newLog newCn) c.
Proof.
Admitted.

Lemma append_dup_ghost {rid} γ r (newCn:u64) newLog :
  int.Z r.(cn) = int.Z newCn ∧ length newLog ≤ length r.(opLog) →
  "Hown" ∷ own_Replica_ghost rid γ r ∗
  "#HnewProp" ∷ proposal_lb γ newCn newLog
  ={⊤}=∗
  own_Replica_ghost rid γ r ∗
  accepted_lb γ newCn rid newLog.
Proof.
Admitted.

Lemma commit_update {rid} γ r log newCommitIdx :
  int.Z newCommitIdx ≤ length log →
  "Hown" ∷ own_Replica_ghost rid γ r ∗
  "#Hacc" ∷ accepted_lb γ r.(cn) rid log ∗
  "#Hcommit_lb" ∷ commit_lb_by γ r.(cn) (take (int.nat newCommitIdx) log)
  ={⊤}=∗
  own_Replica_ghost rid γ r ∗
  own_Committer_ghost γ r (mkCommitterExtra newCommitIdx).
Proof.
Admitted.

End replica_ghost_proof.
