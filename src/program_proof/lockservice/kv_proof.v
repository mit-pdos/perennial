From Coq.Structures Require Import OrdersTac.
From stdpp Require Import gmap.
From iris.algebra Require Import numbers.
From iris.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.
From Perennial.goose_lang Require Import notation.
From Perennial.program_proof Require Import proof_prelude.
From RecordUpdate Require Import RecordUpdate.
From Perennial.algebra Require Import auth_map fmcounter.
From Perennial.goose_lang.lib Require Import lock.
From Perennial.Helpers Require Import NamedProps.
From Perennial.Helpers Require Import ModArith.
From Perennial.program_proof.lockservice Require Import lockservice fmcounter_map rpc common_proof nondet.

Section kv_proof.
Context `{!heapG Σ}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

  Context `{!rpcG Σ u64}.
  Context `{!mapG Σ (u64*u64) unit}.
  Context `{!mapG Σ u64 u64}.
  Context `{Ps : u64 -> iProp Σ}.

  Parameter validLocknames : gmap u64 unit.

  Context `{γkv:gname}.

Local Notation "k [[ γ ]]↦ '_'" := (∃ v, k [[γ]]↦ v)%I
(at level 20, format "k  [[ γ ]]↦ '_'") : bi_scope.

Definition Get_Pre : u64 -> iProp Σ := (λ k, k [[γkv]]↦ _)%I.
Definition Get_Post : u64 -> u64 -> iProp Σ := λ k v, (k [[γkv]]↦ v)%I.

Definition Put_Pre : u64 -> u64 -> iProp Σ := (λ k _, k [[γkv]]↦ _)%I.
Definition Put_Post : u64 -> u64 -> iProp Σ := (λ k v, k [[γkv]]↦ v)%I.

Definition KVServer_own_core (srv:loc) : iProp Σ :=
  ∃ (kvs_ptr:loc) (kvsM:gmap u64 u64),
  "HlocksOwn" ∷ srv ↦[KVServer.S :: "kvs"] #kvs_ptr
∗ "HkvsMap" ∷ is_map (kvs_ptr) kvsM
∗ "Hkvctx" ∷ map_ctx γkv 1 kvsM
.

Definition is_kvserver := is_server (Server_own_core:=KVServer_own_core).

Lemma put_core_spec (srv:loc) (k:u64) (v:u64) :
{{{ 
     KVServer_own_core srv ∗ ▷ Put_Pre k v
}}}
  KVServer__put_core #srv (#k, (#v, #()))%V
{{{
   RET #0; KVServer_own_core srv
      ∗ (Put_Post k v)
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


End lockservice_proof.
