From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import pb.
From Perennial.program_proof.pb Require Export replica_ghost_defns.

Section replica_ghost_proof.

Context `{!heapGS Σ}.
Context `{!rpcregG Σ}.
Implicit Type γ:pb_names.

Lemma append_new_ghost {rid} γ r (newCn:u64) newLog :
  int.Z r.(cn) < int.Z newCn ∨ length r.(opLog ) ≤ length newLog →
  "Hown" ∷ own_Replica_ghost rid γ r ∗
  "#HnewProp" ∷ proposal_lb γ newCn newLog
  ={⊤}=∗
  own_Replica_ghost rid γ (mkReplica newLog newCn) ∗
  accepted_lb γ newCn rid newLog.
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

End replica_ghost_proof.
