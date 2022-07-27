From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Import state.
From Perennial.program_proof.simplepb Require Import pb_definitions.
From iris.base_logic Require Import ghost_map.

Section state_proof.

Context `{!heapGS Σ, !pbG Σ}.

Implicit Type σ : list (list u8).

Definition own_kvs (γkv:gname) σ : iProp Σ.
Admitted.

Definition sys_inv γ γkv : iProp Σ :=
  inv pbN ( ∃ σ, own_ghost γ σ ∗ own_kvs γkv σ).

Context `{!ghost_mapG Σ u64 (list u8)}.
Definition kv_ptsto γkv (k:u64) (v:list u8): iProp Σ :=
  k ↪[γkv] v.

Lemma wp_Clerk__FetchAndAppend ck γkv key val_sl value Φ:
  is_slice val_sl byteT 1 value -∗
  (|={⊤,∅}=> ∃ old_value, kv_ptsto γkv key old_value ∗
    (kv_ptsto γkv key (old_value ++ value) ={∅,⊤}=∗
  (∀ reply_sl, is_slice reply_sl byteT 1 old_value -∗
      Φ (slice_val reply_sl))))
  -∗
  WP state.Clerk__FetchAndAppend #ck #key (slice_val val_sl) @ ⊤ {{ Φ }}.
Proof.
  iIntros "Hval_sl Hupd".
  wp_call.
  wp_pures.

Admitted.

End state_proof.
