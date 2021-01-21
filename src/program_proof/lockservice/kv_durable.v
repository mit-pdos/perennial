From Coq.Structures Require Import OrdersTac.
From stdpp Require Import gmap.
From iris.algebra Require Import numbers.
From iris.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.
From Perennial.goose_lang Require Import notation.
From Perennial.program_proof Require Import proof_prelude.
From RecordUpdate Require Import RecordUpdate.
From Perennial.algebra Require Import auth_map.
From Perennial.goose_lang.lib Require Import lock.
From Perennial.goose_lang.lib Require Import crash_lock.
From Perennial.Helpers Require Import NamedProps.
From Perennial.Helpers Require Import ModArith.
From Goose.github_com.mit_pdos.lockservice Require Import lockservice.
From Perennial.program_proof.lockservice Require Import rpc_proof rpc nondet kv_proof fmcounter_map rpc_durable_proof.

Section kv_durable_proof.
Context `{!heapG Σ, !kvserviceG Σ, stagedG Σ}.

Implicit Types (γ : kvservice_names).

Local Notation "k [[ γ ]]↦ '_'" := (∃ v, k [[γ]]↦ v)%I
(at level 20, format "k  [[ γ ]]↦ '_'") : bi_scope.

Record KVServerC :=
  {
  kvsM : gmap u64 u64;
  }.

Axiom KVServer_core_own_durable : KVServerC → RPCServerC  -> iProp Σ.

Definition KVServer_core_own_vol (srv:loc) kv_server : iProp Σ :=
  ∃ (kvs_ptr:loc),
  "HkvsOwn" ∷ srv ↦[KVServer.S :: "kvs"] #kvs_ptr ∗
  "HkvsMap" ∷ is_map (kvs_ptr) kv_server.(kvsM)
.

Definition KVServer_core_own_ghost γ kv_server : iProp Σ :=
  "Hkvctx" ∷ map_ctx γ.(ks_kvMapGN) 1 kv_server.(kvsM)
.

Definition RPCServer_own_vol (sv:loc) rpc_server : iProp Σ :=
  ∃ (lastSeq_ptr lastReply_ptr:loc),
    "HlastSeqOwn" ∷ sv ↦[RPCServer.S :: "lastSeq"] #lastSeq_ptr
∗ "HlastReplyOwn" ∷ sv ↦[RPCServer.S :: "lastReply"] #lastReply_ptr
∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) rpc_server.(lastSeqM)
∗ "HlastReplyMap" ∷ is_map (lastReply_ptr) rpc_server.(lastReplyM)
.

Definition RPCServer_own_ghost (sv:loc) γrpc rpc_server : iProp Σ :=
  "Hsrpc" ∷ RPCServer_own γrpc rpc_server.(lastSeqM) rpc_server.(lastReplyM) (* TODO: Probably should get better naming for this *)
.

Definition RPCServer_phys_own γrpc (sv:loc) rpc_server : iProp Σ :=
  "Hrpcvol" ∷ RPCServer_own_vol sv rpc_server ∗
  "Hrpcghost" ∷ RPCServer_own_ghost sv γrpc rpc_server
.

Instance durable_timeless kv_server rpc_server: Timeless (KVServer_core_own_durable kv_server rpc_server).
Admitted.

Instance durable_disc kv_server rpc_server: Discretizable (KVServer_core_own_durable kv_server rpc_server).
Admitted.

Definition own_kvclerk γ ck_ptr srv : iProp Σ :=
  ∃ (cl_ptr:loc),
   "Hcl_ptr" ∷ ck_ptr ↦[KVClerk.S :: "client"] #cl_ptr ∗
   "Hprimary" ∷ ck_ptr ↦[KVClerk.S :: "primary"] #srv ∗
   "Hcl" ∷ own_rpcclient cl_ptr γ.(ks_rpcGN).

Lemma wpc_put_core γ (srv:loc) args kvserver :
{{{
     KVServer_core_own_vol srv kvserver ∗
     Put_Pre γ args
}}}
  KVServer__put_core #srv (into_val.to_val args) @ 36 ; ⊤
{{{
      kvserver' (r:u64) P', RET #r;
            ⌜Discretizable P'⌝ ∗
             (P') ∗
            KVServer_core_own_vol srv kvserver' ∗
            □ (P' -∗ Put_Pre γ args) ∗
            (* TODO: putting this here because need to be discretizable *)
            □ (▷ P' -∗ KVServer_core_own_ghost γ kvserver ==∗ Put_Post γ args r ∗ KVServer_core_own_ghost γ kvserver')
}}}
{{{
     Put_Pre γ args
}}}.
Proof.
Admitted.

Definition kv_core_mu (srv rpc_srv:loc) γ : rpc_core_mu :=
  {|
  core_own_durable := λ server rpc_server, KVServer_core_own_durable server rpc_server;
  core_own_ghost := λ server, KVServer_core_own_ghost γ server;
  core_own_vol := λ srv_unused server, KVServer_core_own_vol srv server
  |}.

Definition is_kvserver γ (srv rpc_srv:loc) := is_server KVServerC (kv_core_mu srv rpc_srv γ) srv rpc_srv γ.(ks_rpcGN).

Lemma KVServer__Get_spec srv rpc_srv va γ :
is_kvserver γ srv rpc_srv -∗
{{{
    True
}}}
    KVServer__Get #srv
{{{ (f:goose_lang.val), RET f;
        is_rpcHandler f γ.(ks_rpcGN) (Get_Pre γ va) (Get_Post γ va)
}}}.
Proof.
  iIntros "#Hks".
  iIntros (Φ) "!# Hpre HΦ".
  wp_lam.
  wp_pures.
  iApply "HΦ".
  iApply is_rpcHandler_eta. simpl.
  iModIntro.
  iIntros (_ _).

  iIntros (????? Φ) "!# Hpre HΦ".
  iNamed "Hpre".
  wp_pures.
Admitted.
End kv_durable_proof.
