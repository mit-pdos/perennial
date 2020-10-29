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
From Perennial.program_proof.lockservice Require Import lockservice fmcounter_map rpc common_proof nondet rpc proof kv_proof.

Record bank_names := BankGN {
  bank_ls_names : lockservice_names;
  bank_ks_names : kvservice_names;
  bank_logBalGN : gname (* *)
}.

Class bankG Σ := BankG {
  bank_ls :> lockserviceG Σ;
  bank_ks :> kvserviceG Σ;
  bank_logBalG :> mapG Σ u64 u64
}.

Section bank_proof.
Context `{!heapG Σ, !bankG Σ}.

Implicit Types (γ : bank_names).

Context `{acc1:u64, acc2:u64}. (* Per-lock invariant *)

Definition kv_gn γ := γ.(bank_ks_names).(ks_kvMapGN).
Definition log_gn γ := γ.(bank_logBalGN).

(* TODO: consider making is_*server part of own_*clerk *)
Definition own_bank_clerk (bank_ck:loc) γ : iProp Σ :=
  ∃ (lck kck ls_srv ks_srv:loc), 
  "#Hls" ∷ is_lockserver ls_srv γ.(bank_ls_names) (Ps:=λ k, (∃v, k [[kv_gn γ]]↦v ∗ k [[log_gn γ]]↦v) )∗
  "#Hks" ∷ is_kvserver ks_srv γ.(bank_ks_names) ∗
  "Hlck_own" ∷ own_clerk #lck ls_srv γ.(bank_ls_names).(ls_rpcGN) ∗
  "Hkck_own" ∷ own_kvclerk kck ks_srv γ.(bank_ks_names).(ks_rpcGN) ∗

  "Hkck" ∷ bank_ck ↦[BankClerk.S :: "kvck"] #kck ∗
  "Hlck" ∷ bank_ck ↦[BankClerk.S :: "lck"] #lck ∗
  "Hacc1" ∷ bank_ck ↦[BankClerk.S :: "acc1"] #acc1 ∗
  "Hacc1" ∷ bank_ck ↦[BankClerk.S :: "acc2"] #acc2 ∗

  "#Hacc1_is_lock" ∷ lockservice_is_lock γ.(bank_ls_names) acc1 ∗
  "#Hacc2_is_lock" ∷ lockservice_is_lock γ.(bank_ls_names) acc2
.

Definition bank_inv γ : iProp Σ :=
  ∃ logBalMap:gmap u64 u64,
  "HlogBalCtxl" ∷ map_ctx (log_gn γ) 1 logBalMap
  .

End bank_proof.
