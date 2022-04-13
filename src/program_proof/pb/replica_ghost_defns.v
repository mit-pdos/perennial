From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import pb.
From Perennial.program_proof.pb Require Export ghost_proof.

(*
  Ownership/repr predicates for owning a ghost replica.

  The state of a replica is split into the core Replica state, the extra state
  that a Primary has, and the extra state that a Committer has. A committer is
  just a replica that also keeps information about what part of the log has been
  committed.
 *)
Section replica_ghost_defns.

Context `{!heapGS Σ}.
Context `{!urpcregG Σ}.
Context `{!pb_ghostG Σ}.
Implicit Type γ:pb_names.

Record Replica := mkReplica
{
  opLog : list u8;
  cn : u64;
}.

Definition own_Replica_ghost (rid:u64) γ (r:Replica) : iProp Σ :=
  "Haccepted" ∷ accepted_ptsto γ r.(cn) rid r.(opLog) ∗
  "HacceptedUnused" ∷ ([∗ set] cn_some ∈ (fin_to_set u64),
                      ⌜int.Z cn_some ≤ int.Z r.(cn)⌝ ∨ accepted_ptsto γ cn_some rid []
                      ) ∗
  "#Hproposal_lb" ∷ proposal_lb_fancy γ r.(cn) r.(opLog)
.

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

Definition own_Committer_ghost γ (r:Replica) (c:CommitterExtra) : iProp Σ :=
  "#Hcommit_lb" ∷ commit_lb_by γ r.(cn) (take (int.nat c.(commitIdx)) r.(opLog)) ∗
  "%HcommitLeLogLen" ∷ ⌜int.Z c.(commitIdx) <= length r.(opLog)⌝
.

End replica_ghost_defns.
