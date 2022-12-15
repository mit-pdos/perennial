From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Export ffi.grove_prelude.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.ffi Require Export grove_ffi_time_axiom.
From Perennial.base_logic.lib Require Import ghost_var.
From Goose.github_com.mit_pdos.gokv Require Import minlease.

Section proof.

Context `{!heapGS Σ}.
Context `{!ghost_varG Σ u64}.

Context {γtime:gname}.
Notation is_time_lb := (is_time_lb γtime).
Notation own_time := (own_time γtime).

(* Q is the lease obligation *)
Definition underLease (N:namespace) (leaseExpiration:u64) (P:iProp Σ) (Q:iProp Σ) : iProp Σ :=
  ∀ (t:u64),
  ⌜int.nat t < int.nat leaseExpiration⌝ →
  own_time t ={↑N}=∗
  (P ∗ (P ={↑N}=∗ own_time t))
.
(* inv N (P ∨ is_time_lb leaseExpiration) *)

Definition postLease (N:namespace) (leaseExpiration:u64) (P:iProp Σ) :=
  is_time_lb leaseExpiration ={↑N}=∗ P
.

(* P are resources you can access and modify at the moment you check that the
   lease is unexpired.
 *)

Definition own_Server s γ : iProp Σ :=
  ∃ (v:u64) (leaseExpiration:u64),
  "Hval" ∷ s ↦[Server :: "val"] #v ∗
  "HleaseExpiration" ∷ s ↦[Server :: "leaseExpiration"] #leaseExpiration ∗
  "Hauth" ∷ ghost_var γ (1/2) v
.

Definition is_Server s γ : iProp Σ :=
  ∃ mu,
  "#Hmu" ∷ readonly (s ↦[Server :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock nroot mu (own_Server s γ)
.

Definition clientPre s γ : iProp Σ :=
  ∃ mu,
  "#Hmu" ∷ readonly (s ↦[Server :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock nroot mu (own_Server s γ)
.

End proof.
