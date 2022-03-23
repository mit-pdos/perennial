From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.fencing Require Import ctr.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.memkv Require Export rpc_lib rpc_proof rpc_spec.

Section ctr_definitions.
Context `{!heapGS Σ}.

Record ctr_names :=
  {}.

Definition kv_ptsto_epoch (k e v:u64) : iProp Σ.
Admitted.

Definition kv_ptsto (k v:u64) : iProp Σ.
Admitted.

Definition own_Clerk : iProp Σ.
Admitted.


(* |={Eo,Ei}=> ∃ vold, kv_ptsto k vold ∗ (kv_ptsto k vnew ={Ei,Eo}=∗ Q) *)

Lemma wp_Clerk__Put (γ:ctr_names) (k e v:u64):
  {{{
      (∃ oldv, kv_ptsto_epoch k e oldv) ∗
      (∃ oldv2, kv_ptsto k oldv2)
  }}}
    Clerk__Put #v #e
  {{{
        RET #(); kv_ptsto k v
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
Admitted.

End ctr_definitions.
