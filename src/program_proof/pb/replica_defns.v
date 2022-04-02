From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import pb.

From Perennial.program_proof.memkv Require Export urpc_proof.
From Perennial.program_proof.pb Require Export replica_ghost_defns.

Section replica_defns.

Context `{!heapGS Σ}.
Context `{!rpcregG Σ}.
Context `{!pb_ghostG Σ}.
Implicit Type γ:pb_names.

Definition uREPLICA_APPEND: nat :=
  Eval vm_compute in match REPLICA_APPEND with LitV (LitInt n) => int.nat n | _ => 0 end.

(* The RPC specs that a replica server must provide *)
Definition is_Replica (host:u64) γ : iProp Σ :=
  True.

Definition is_ReplicaClerk (ck_ptr:loc) (rid:u64) γ : iProp Σ :=
  ∃ (cl_ptr:loc),
  "#Hcl" ∷ readonly (ck_ptr ↦[ReplicaClerk :: "cl"] #cl_ptr) ∗
  "#His_Replica" ∷ is_Replica rid γ ∗
  "#Hc_own" ∷ RPCClient_own cl_ptr rid
.

Definition own_Replica_phys (s:loc) (r:Replica) : iProp Σ :=
  ∃ (opLog_sl : Slice.t),
  "Hcn" ∷ s ↦[ReplicaServer :: "cn"] #r.(cn) ∗
  "HopLog" ∷ s ↦[ReplicaServer :: "opLog"] (slice_val opLog_sl) ∗
  "HopLog_slice" ∷ is_slice opLog_sl byteT 1%Qp r.(opLog)
.

Definition own_Primary_phys (s:loc) (r:Replica) (p:PrimaryExtra) : iProp Σ :=
  ∃ (matchIdx_sl : Slice.t),
  "HmatchIdx" ∷ s ↦[ReplicaServer :: "matchIdx"] (slice_val matchIdx_sl) ∗
  "HmatchIdx_slice" ∷ is_slice_small matchIdx_sl uint64T 1%Qp p.(matchIdx)
.

Definition own_Committer_phys (s:loc) (r:Replica) (c:CommitterExtra) : iProp Σ :=
  "HcommitIdx" ∷ s ↦[ReplicaServer :: "commitIdx"] #c.(commitIdx)
.

(* FIXME: should make `rid` not part of Replica record *)
Definition own_ReplicaServer (s:loc) (me:u64) γ
  : iProp Σ :=
  ∃ (r:Replica) (p:PrimaryExtra) (c:CommitterExtra) (replicaClerks_sl : Slice.t) (isPrimary:bool) (replicaClerks:list loc),
  "HisPrimary" ∷ s ↦[ReplicaServer :: "isPrimary"] #isPrimary ∗

  (* Physical stuff *)
  "Hrep" ∷ own_Replica_phys s r ∗
  "Hprimary" ∷ own_Primary_phys s r p ∗
  "Hcommitter" ∷ own_Committer_phys s r c ∗

  (* Ghost stuff *)
  "HrepG" ∷ own_Replica_ghost me γ r ∗
  "HprimaryG" ∷ (if isPrimary then own_Primary_ghost γ r p else True) ∗
  "#HcommitterG" ∷ own_Committer_ghost γ r c ∗

  (* only used for primary *)
  "HreplicaClerks" ∷ s ↦[ReplicaServer :: "replicaClerks"] (slice_val replicaClerks_sl) ∗
  "HreplicaClerks_slice" ∷ is_slice replicaClerks_sl ptrT 1%Qp replicaClerks
.

Definition ReplicaServerN := nroot .@ "ReplicaServer".

Definition is_ReplicaServer (s:loc) (rid:u64) γ: iProp Σ :=
  ∃ (mu:val),
  "#Hmu" ∷ readonly (s ↦[ReplicaServer :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock ReplicaServerN mu (own_ReplicaServer s rid γ)
.

End replica_defns.
