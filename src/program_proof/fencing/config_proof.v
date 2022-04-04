From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.fencing Require Import frontend.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.memkv Require Export urpc_lib urpc_proof urpc_spec.
From Perennial.program_proof.fencing Require Export ctr_proof.
From iris.base_logic Require Import mono_nat.

Module config.
Section config_proof.
Context `{!heapGS Σ}.

Record names :=
  {

  }.

Context (γ:names).

Definition is_host (host:u64) (epoch_tok : u64 → iProp Σ) (host_inv:u64 → iProp Σ): iProp Σ.
Admitted.

Global Instance is_host_pers host epoch_tok host_inv : Persistent (is_host host epoch_tok host_inv).
Admitted.

Definition is_Clerk (ck:loc) : iProp Σ.
Admitted.

Global Instance is_Clerk_pers ck : Persistent (is_Clerk ck).
Admitted.


Lemma wp_MakeClerk host epoch_tok host_inv :
  is_host host epoch_tok host_inv -∗
  {{{
        True
  }}}
    config.MakeClerk #host
  {{{
        (ck:loc), RET #ck; is_Clerk ck
  }}}.
Proof.
Admitted.

Lemma wp_Clerk__AcquireEpoch ck host newHost epoch_tok host_inv :
  is_host host epoch_tok host_inv -∗
  is_Clerk ck -∗
  {{{
        True
  }}}
    config.Clerk__AcquireEpoch #ck #newHost
  {{{
        (epoch:u64), RET #epoch; epoch_tok epoch
  }}}.
Proof.
Admitted.

Lemma wp_Clerk__Get ck host epoch_tok host_inv :
  is_host host epoch_tok host_inv -∗
  is_Clerk ck -∗
  {{{
        True
  }}}
    config.Clerk__Get #ck
  {{{
        (v:u64), RET #host; host_inv v
  }}}.
Proof.
Admitted.

End config_proof.
End config.
