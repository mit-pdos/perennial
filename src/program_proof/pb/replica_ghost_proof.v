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

(* Increase commitIdx by getting a commit_lb_by witness from primary *)
Lemma commit_idx_update {rid} γ r log newCommitIdx :
  int.Z newCommitIdx ≤ length log →
  "Hown" ∷ own_Replica_ghost rid γ r ∗
  "#Hacc" ∷ accepted_lb γ r.(cn) rid log ∗
  "#Hcommit_lb" ∷ commit_lb_by γ r.(cn) (take (int.nat newCommitIdx) log)
  ={⊤}=∗
  own_Replica_ghost rid γ r ∗
  own_Committer_ghost γ r (mkCommitterExtra newCommitIdx).
Proof.
Admitted.

Lemma primary_matchidx_lookup {rid} conf (i:u64) γ r p :
  conf !! int.nat i = Some rid →
  "#Hconf" ∷ config_ptsto γ r.(cn) conf ∗
  "HprimaryG" ∷ own_Primary_ghost γ r p
  -∗
  ⌜∃ (x:u64), p.(matchIdx) !! int.nat i = Some x⌝.
Proof.
Admitted.

Lemma primary_update_matchidx {rid} (i oldIdx:u64) γ r p newLog (newLogLen:u64) :
  p.(matchIdx) !! int.nat i = Some oldIdx →
  length newLog = int.nat newLogLen →
  "HprimaryG" ∷ own_Primary_ghost γ r p ∗
  "#Hacc_lb" ∷ accepted_lb γ r.(cn) rid newLog
  ={⊤}=∗
  own_Primary_ghost γ r (mkPrimaryExtra
                           p.(conf)
                           (<[int.nat i:=newLogLen]> p.(matchIdx)) ).
Proof.
Admitted.

Lemma primary_commit m γ r (p:PrimaryExtra) :
  m ∈ p.(matchIdx) →
  (∀ n, n ∈ p.(matchIdx) → int.Z m ≤ int.Z n) →
  own_Primary_ghost γ r p
  ={⊤}=∗
  own_Primary_ghost γ r p ∗
  own_Committer_ghost γ r (mkCommitterExtra m).
Proof.
Admitted.

End replica_ghost_proof.
