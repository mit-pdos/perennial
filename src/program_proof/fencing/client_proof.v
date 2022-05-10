From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.fencing Require Import client.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.grove_shared Require Export erpc_lib urpc_proof urpc_spec.
From Perennial.program_proof.fencing Require Export config_proof frontend_proof.
From Perennial.program_proof Require Export marshal_proof.
From iris.base_logic Require Import mono_nat.
From Perennial.goose_lang Require Import prelude ffi.grove_exit_axiom.

Module client.
Section client_proof.
Context `{!heapGS Σ}.

Record client_names :=
  {
    config_gn: config.names;
  }.

Implicit Type γ : client_names.
Context `{!urpcregG Σ}.

(* This is "own" not "is" because the frontendCk field is written to inside of
   FetchAndIncrement, so it's actually not safe for one Clerk to have concurrent
   FAIs. *)
Definition own_Clerk γ ck : iProp Σ :=
  ∃ (configCk frontendCk:loc),
  "HconfigCk" ∷ ck ↦[client.Clerk :: "configCk"] #configCk ∗
  "HfrontendCk" ∷ ck ↦[client.Clerk :: "frontendCk"] #frontendCk ∗

  "HconfigCk_own" ∷ config.is_Clerk γ.(config_gn) configCk (λ _, True) (λ _, True)
.

End client_proof.
End client.
