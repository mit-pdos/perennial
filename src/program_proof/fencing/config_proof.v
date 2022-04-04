From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.fencing Require Import frontend.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.memkv Require Export urpc_lib urpc_proof urpc_spec.
From Perennial.program_proof.fencing Require Export ctr_proof.
From iris.base_logic Require Import mono_nat.

Section config_proof.
Context `{!heapGS Σ}.

Record config_names :=
  {

  }.

Implicit Type γ:config_names.

Definition is_config_host γ (host:u64) : iProp Σ.
Admitted.

Definition own_ConfigClerk γ (ck:loc) : iProp Σ.
Admitted.

Lemma wp_MakeClerk γ host :
  is_config_host γ host -∗
  {{{
        True
  }}}
    config.MakeClerk #host
  {{{
        (ck:loc), RET #ck; own_ConfigClerk γ ck
  }}}.
Proof.
Admitted.

End config_proof.
