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
From Perennial.program_proof.lockservice Require Import lockservice_crash rpc nondet kv_proof common_proof.

Section kv_durable_proof.
Context `{!heapG Σ, !kvserviceG Σ, stagedG Σ}.

Implicit Types (γ : kvservice_names).

Local Notation "k [[ γ ]]↦ '_'" := (∃ v, k [[γ]]↦ v)%I
(at level 20, format "k  [[ γ ]]↦ '_'") : bi_scope.

Record RPCServerC :=
  {
  lastSeqM : gmap u64 u64;
  lastReplyM  : gmap u64 u64;
  }.

Record KVServerC :=
  {
  sv : RPCServerC ;
  kvsM : gmap u64 u64;
  }.

Axiom kvserver_durable_is : KVServerC -> iProp Σ.

Definition RPCServer_mutex_cinv γ : iProp Σ :=
  ∃ kv_server,
  "Hkvdurable" ∷ kvserver_durable_is kv_server
∗ "Hsrpc" ∷ RPCServer_own γ.(ks_rpcGN) kv_server.(sv).(lastSeqM) kv_server.(sv).(lastReplyM)
∗ "Hkvctx" ∷ map_ctx γ.(ks_kvMapGN) 1 kv_server.(kvsM)
.

Definition KVServer_own_core γ (srv:loc) kv_server : iProp Σ :=
  ∃ (kvs_ptr:loc),
  "HlocksOwn" ∷ srv ↦[KVServer.S :: "kvs"] #kvs_ptr
∗ "HkvsMap" ∷ is_map (kvs_ptr) kv_server.(kvsM)
∗ "Hkvctx" ∷ map_ctx γ.(ks_kvMapGN) 1 kv_server.(kvsM)
.

Definition RPCServer_own_phys γrpc (sv:loc) rpc_server : iProp Σ :=
  ∃ (lastSeq_ptr lastReply_ptr:loc),
    "HlastSeqOwn" ∷ sv ↦[RPCServer.S :: "lastSeq"] #lastSeq_ptr
∗ "HlastReplyOwn" ∷ sv ↦[RPCServer.S :: "lastReply"] #lastReply_ptr
∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) rpc_server.(lastSeqM)
∗ "HlastReplyMap" ∷ is_map (lastReply_ptr) rpc_server.(lastReplyM)
∗ ("Hsrpc" ∷ rpc.RPCServer_own γrpc rpc_server.(lastSeqM) rpc_server.(lastReplyM)) (* TODO: Probably should get better naming for this *)
.

Instance durable_timeless kv_server : Timeless (kvserver_durable_is kv_server).
Admitted.

Instance durable_disc kv_server : Discretizable (kvserver_durable_is kv_server).
Admitted.

Definition RPCServer_mutex_inv srv_ptr sv_ptr γ : iProp Σ :=
  ∃ kv_server,
    "Hkv" ∷ KVServer_own_core γ srv_ptr kv_server ∗
    "Hrpc" ∷ RPCServer_own_phys γ.(ks_rpcGN) sv_ptr kv_server.(sv) ∗
    "Hkvdurable" ∷ kvserver_durable_is kv_server
.

Definition mutexN : namespace := nroot .@ "kvmutexN".

Definition is_kvserver (srv_ptr sv_ptr:loc) γ : iProp Σ :=
  ∃ (mu_ptr:loc),
  "#Hsv" ∷ readonly (srv_ptr ↦[KVServer.S :: "sv"] #sv_ptr) ∗
  "#Hlinv" ∷ is_RPCServer γ.(ks_rpcGN) ∗
  "#Hmu_ptr" ∷ readonly(sv_ptr ↦[RPCServer.S :: "mu"] #mu_ptr) ∗
  "#Hmu" ∷ is_crash_lock mutexN 37 #mu_ptr (RPCServer_mutex_inv srv_ptr sv_ptr γ)
    (RPCServer_mutex_cinv γ)
.

Definition own_kvclerk γ ck_ptr srv : iProp Σ :=
  ∃ (cl_ptr:loc),
   "Hcl_ptr" ∷ ck_ptr ↦[KVClerk.S :: "client"] #cl_ptr ∗
   "Hprimary" ∷ ck_ptr ↦[KVClerk.S :: "primary"] #srv ∗
   "Hcl" ∷ own_rpcclient cl_ptr γ.(ks_rpcGN).

Lemma RPCServer__HandleRequest_spec' (coreFunction makeDurable:goose_lang.val) (srv sv req_ptr reply_ptr:loc) (req:Request64) (reply:Reply64) γ γPost PreCond PostCond :
{{{
  "#Hls" ∷ is_kvserver srv sv γ
  ∗ "#HreqInv" ∷ is_RPCRequest γ.(ks_rpcGN) γPost PreCond PostCond req
  ∗ "#Hreq" ∷ read_request req_ptr req
  ∗ "Hreply" ∷ own_reply reply_ptr reply
}}}
  RPCServer__HandleRequest #sv coreFunction makeDurable #req_ptr #reply_ptr
{{{ RET #false; ∃ reply':Reply64, own_reply reply_ptr reply'
    ∗ ((⌜reply'.(Stale) = true⌝ ∗ RPCRequestStale γ.(ks_rpcGN) req)
  ∨ RPCReplyReceipt γ.(ks_rpcGN) req reply'.(Ret))
}}}.
Proof.
  iIntros (Φ) "Hpre Hpost".
  iNamed "Hpre".
  wp_lam.
  wp_pures.
  iNamed "Hls".
  wp_loadField.
  wp_apply (crash_lock.acquire_spec with "Hmu"); first done.
  iIntros "Hlocked".
  wp_pures.
  iApply (wpc_wp _ _ _ _ _ True).
  crash_lock_open "Hlocked"; eauto.
  { iModIntro. done. }
  iIntros ">Hlsown".
  iNamed "Hlsown".
  iNamed "Hkv". iNamed "Hrpc".
  iNamed "Hreq".
  iCache with "Hkvdurable Hkvctx Hsrpc".
  { iModIntro; iNext. iSplit; first done.
    iExists _; iFrame.
  }
  wpc_loadField.
  wpc_loadField.

  (* Do loadField on non-readonly ptsto *)
  wpc_bind (struct.loadF _ _ _).
  wpc_frame.
  wp_loadField.
  iNamed 1.

  (* This is the style of the wpc_loadField tactic *)
  wpc_bind (struct.loadF _ _ _).
  wpc_frame_go "HlastSeqOwn" base.Right [INamed "HlastSeqOwn"].
  wp_loadField.
  iNamed 1.
Admitted.

End kv_proof.
