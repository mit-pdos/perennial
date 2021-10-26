From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import pb.

From Perennial.program_proof.memkv Require Export rpc_proof.
From Perennial.program_proof.pb Require Export ghost_proof.

Section replica_definitions.
Record ConfigurationC :=
{
  C_replicas: list u64
}.

Context `{!heapGS Σ}.
Context `{!rpcregG Σ}.
Implicit Type γ:pb_names.

Definition uREPLICA_APPEND: nat :=
  Eval vm_compute in match REPLICA_APPEND with LitV (LitInt n) => int.nat n | _ => 0 end.

Definition is_Replica (host:u64) γ : iProp Σ :=
  True.

Definition is_ReplicaClerk (ck_ptr:loc) (rid:u64) γ : iProp Σ :=
  ∃ (cl_ptr:loc),
  "#Hcl" ∷ readonly (ck_ptr ↦[ReplicaClerk :: "cl"] #cl_ptr) ∗
  "#His_Replica" ∷ is_Replica rid γ ∗
  "#Hc_own" ∷ RPCClient_own cl_ptr rid
.

Definition own_ReplicaServer (s:loc) (me:u64) γ
  : iProp Σ :=
  ∃ (cn commitIdx:u64) (matchIdx_sl opLog_sl replicaClerks_sl : Slice.t) (isPrimary:bool)
    (matchIdx:list u64) (opLog:list u8) (replicaClerks:list loc),
  "Hcn" ∷ s ↦[ReplicaServer :: "cn"] #cn ∗
  (* don't need use the conf field right now *)
  "HisPrimary" ∷ s ↦[ReplicaServer :: "isPrimary"] #isPrimary ∗
  "HreplicaClerks" ∷ s ↦[ReplicaServer :: "replicaClerks"] (slice_val replicaClerks_sl) ∗
  "HreplicaClerks_slice" ∷ is_slice replicaClerks_sl (struct.ptrT ReplicaClerk) 1%Qp replicaClerks ∗
  "HopLog" ∷ s ↦[ReplicaServer :: "opLog"] (slice_val opLog_sl) ∗
  "HopLog_slice" ∷ is_slice opLog_sl byteT 1%Qp opLog ∗
  "HcommitIdx" ∷ s ↦[ReplicaServer :: "commitIdx"] #commitIdx ∗
  "HmatchIdx" ∷ s ↦[ReplicaServer :: "matchIdx"] (slice_val matchIdx_sl) ∗
  "HmatchIdx_slice" ∷ is_slice_small matchIdx_sl uint64T 1%Qp matchIdx∗

  (* ghost stuff *)
  "Haccepted" ∷ accepted_ptsto γ cn me opLog ∗
  "HacceptedUnused" ∷ ([∗ set] cn_some ∈ (fin_to_set u64),
                      ⌜int.Z cn_some ≤ int.Z cn⌝ ∨ accepted_ptsto γ cn_some me []
                      ) ∗
  "#Hproposal_lb" ∷ proposal_lb γ cn opLog ∗
  "#HoldConfMax" ∷ oldConfMax γ cn opLog ∗
  "HprimaryOwnsProposal" ∷ (if isPrimary then (proposal_ptsto γ cn opLog) else True) ∗
  "#Hcommit_lb" ∷ commit_lb_by γ cn (take (int.nat commitIdx) opLog) ∗
  "%HcommitLeLogLen" ∷ ⌜int.Z commitIdx <= length opLog⌝ ∗

  (* this is stuff for the primary only *)
  if isPrimary then
    ∃ (conf:list u64),
  "#HconfPtsto" ∷ config_ptsto γ cn conf ∗
  "#HmatchIdxAccepted" ∷ [∗ list] _ ↦ rid;j ∈ conf; matchIdx, accepted_lb γ cn rid (take (int.nat j) opLog)
  else True
.

Definition ReplicaServerN := nroot .@ "ReplicaServer".

Definition is_ReplicaServer (s:loc) (rid:u64) γ: iProp Σ :=
  ∃ (mu:val),
  "#Hmu" ∷ readonly (s ↦[ReplicaServer :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock ReplicaServerN mu (own_ReplicaServer s rid γ)
.

End replica_definitions.
