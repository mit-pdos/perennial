From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import pb.
From Perennial.program_proof.pb Require Export ghost_proof.

Section append_ghost_proof.

Context `{!heapGS Σ}.
Context `{!rpcregG Σ}.
Implicit Type γ:pb_names.

Record Replica := mkReplica
{
  rid : u64;
  opLog : list u8;
  cn : u64;
}.

Definition own_Replica_ghost γ (r:Replica) : iProp Σ :=
  "Haccepted" ∷ accepted_ptsto γ r.(cn) r.(rid) r.(opLog) ∗
  "HacceptedUnused" ∷ ([∗ set] cn_some ∈ (fin_to_set u64),
                      ⌜int.Z cn_some ≤ int.Z r.(cn)⌝ ∨ accepted_ptsto γ cn_some r.(rid) []
                      ) ∗
  "#Hproposal_lb" ∷ proposal_lb γ r.(cn) r.(opLog)
.

Definition append_rpc_new_ghost γ r (newCn:u64) newLog :
  "Hown" ∷ own_Replica_ghost γ r ∗
  "#HnewProp" ∷ proposal_lb γ newCn newLog ∗
  "%Hnew" ∷ ⌜int.Z r.(cn) < int.Z newCn ∨ r.(opLog )⪯ newLog⌝
  ={⊤}=∗
  accepted_lb γ newCn r.(rid) newLog.
Proof.
  iNamed 1.
  iNamed "Hown".
Admitted.

Definition append_rpc_dup_ghost γ r (newCn:u64) newLog :
  "Hown" ∷ own_Replica_ghost γ r ∗
  "#HnewProp" ∷ proposal_lb γ newCn newLog ∗
  "%Hdup" ∷ ⌜int.Z r.(cn) = int.Z newCn ∧ newLog ⪯ r.(opLog )⌝
  ={⊤}=∗
  accepted_lb γ newCn r.(rid) newLog.
Proof.
  iNamed 1.
  iNamed "Hown".
Admitted.

(* A primary is a replica with some more stuff; technically, the rid from the
   replica is not necessary to have a primary*)
Record PrimaryExtra := mkPrimaryExtra
{
  conf : list u64;
  matchIdx : list u64;
}.

Definition own_Primary_ghost γ (r:Replica) (p:PrimaryExtra) : iProp Σ :=
  "HprimaryOwnsProposal" ∷ proposal_ptsto γ r.(cn) r.(opLog) ∗
  "#HconfPtsto" ∷ config_ptsto γ r.(cn) p.(conf) ∗
  "#HmatchIdxAccepted" ∷ [∗ list] _ ↦ rid;j ∈ p.(conf); p.(matchIdx), accepted_lb γ r.(cn) rid (take (int.nat j) r.(opLog))
.

Record CommitterExtra := mkCommitterExtra
{
  commitIdx : u64;
}.

Definition own_Commiter_ghost γ (r:Replica) (c:CommitterExtra) : iProp Σ :=
  "#Hcommit_lb" ∷ commit_lb_by γ r.(cn) (take (int.nat c.(commitIdx)) r.(opLog)) ∗
  "%HcommitLeLogLen" ∷ ⌜int.Z c.(commitIdx) <= length r.(opLog)⌝
.

End append_ghost_proof.
