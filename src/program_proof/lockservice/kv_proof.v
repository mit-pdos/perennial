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
From Perennial.Helpers Require Import NamedProps.
From Perennial.Helpers Require Import ModArith.
From Perennial.program_proof.lockservice Require Import lockservice rpc common_proof nondet rpc.

Record kvservice_names := KVserviceGN {
  ks_rpcGN : rpc_names;
  ks_kvMapGN : gname;
}.

Class kvserviceG Σ := KVserviceG {
  ls_rpcG :> rpcG Σ u64; (* RPC layer ghost state *)
  ls_kvMapG :> mapG Σ u64 u64; (* [γkv]: tracks the state of the KV server *logically* *)
}.

Section kv_proof.
Context `{!heapG Σ, !kvserviceG Σ}.

Implicit Types (γ : kvservice_names).

Local Notation "k [[ γ ]]↦ '_'" := (∃ v, k [[γ]]↦ v)%I
(at level 20, format "k  [[ γ ]]↦ '_'") : bi_scope.

(*
Definition Get_Pre : u64 -> iProp Σ := (λ k, k [[γkv]]↦ _)%I.
Definition Get_Post : u64 -> u64 -> iProp Σ := λ k v, (k [[γkv]]↦ v)%I.

Definition Put_Pre : u64 -> u64 -> iProp Σ := (λ k _, k [[γkv]]↦ _)%I.
Definition Put_Post : u64 -> u64 -> iProp Σ := (λ k v, k [[γkv]]↦ v)%I.
*)

Definition KVServer_own_core γ (srv:loc) : iProp Σ :=
  ∃ (kvs_ptr:loc) (kvsM:gmap u64 u64),
  "HlocksOwn" ∷ srv ↦[KVServer.S :: "kvs"] #kvs_ptr
∗ "HkvsMap" ∷ is_map (kvs_ptr) kvsM
∗ "Hkvctx" ∷ map_ctx γ.(ks_kvMapGN) 1 kvsM
.

(* FIXME: this is currently just a placeholder *)
Definition own_kvclerk (γrpc:rpc_names) (kck ks_srv:loc): iProp Σ := True.

Definition is_kvserver γ (srv:loc) := is_server (Server_own_core:=KVServer_own_core γ) srv γ.(ks_rpcGN).

Lemma put_core_spec γ (srv:loc) (k:u64) (v:u64) :
{{{ 
     KVServer_own_core γ srv ∗ k [[γ.(ks_kvMapGN)]]↦ _
}}}
  KVServer__put_core #srv (#k, (#v, #()))%V
{{{
   RET #0; KVServer_own_core γ srv
      ∗ k [[γ.(ks_kvMapGN)]]↦ v
}}}.
Proof.
  iIntros (Φ) "[Hksown Hpre] Hpost".
  wp_lam.
  wp_pures.
  iNamed "Hksown".
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapInsert with "HkvsMap"); eauto; iIntros "HkvsMap".
  iDestruct "Hpre" as (v') "Hpre".
  iMod (map_update with "Hkvctx Hpre") as "[Hkvctx Hptsto]".
  wp_seq.
  iApply "Hpost".
  iFrame. iExists _, _; iFrame.
Qed.

Lemma get_core_spec (srv:loc) (k:u64) γ :
{{{ 
     KVServer_own_core γ srv ∗ k [[γ.(ks_kvMapGN)]]↦ _
}}}
  KVServer__get_core #srv #k%V
{{{
   v, RET v; ∃va:u64, ⌜v = #va⌝ ∗ KVServer_own_core γ srv
      ∗ k [[γ.(ks_kvMapGN)]]↦ va
}}}.
Proof.
  iIntros (Φ) "[Hksown Hpre] Hpost".
  wp_lam.
  wp_pures.
  iNamed "Hksown".
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapGet with "HkvsMap").
  iIntros (va ok) "[% HkvsMap]".
  iDestruct "Hpre" as (v') "Hpre".
  iDestruct (map_valid with "Hkvctx Hpre") as %Hvalid.
  assert (va = v') as ->.
  {
    rewrite /map_get in H.
    rewrite ->bool_decide_true in H; eauto.
    simpl in H.
    injection H as H.
    rewrite /default in H.
    rewrite Hvalid in H.
    done.
  }
  wp_pures.
  iApply "Hpost".
  iExists v'; iFrame.
  iSplit; eauto. iExists _, _; iFrame.
Qed.

Lemma KVClerk__Get_spec (kck ksrv:loc) (key va:u64) γ  :
{{{
     is_kvserver γ ksrv ∗
     own_kvclerk γ.(ks_rpcGN) kck ksrv ∗ (key [[γ.(ks_kvMapGN)]]↦ va)
}}}
  KVClerk__Get #kck #key
{{{
     v, RET v; ⌜v = #va⌝ ∗ own_kvclerk γ.(ks_rpcGN) kck ksrv ∗ (key [[γ.(ks_kvMapGN)]]↦ va )
}}}.
Admitted.

Lemma KVClerk__Put_spec (kck ksrv:loc) (key va:u64) γ :
{{{
     is_kvserver γ ksrv ∗
     own_kvclerk γ.(ks_rpcGN) kck ksrv ∗ (key [[γ.(ks_kvMapGN)]]↦ _ )
}}}
  KVClerk__Put #kck #key #va
{{{
     RET #();
     own_kvclerk γ.(ks_rpcGN) kck ksrv ∗ (key [[γ.(ks_kvMapGN)]]↦ va )
}}}.
Admitted.

End kv_proof.
