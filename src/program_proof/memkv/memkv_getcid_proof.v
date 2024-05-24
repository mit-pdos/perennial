From Perennial.Helpers Require Import ModArith.
From Perennial.program_proof Require Import grove_prelude std_proof.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.memkv Require Export memkv_shard_definitions memkv_marshal_getcid_proof memkv_shard_clerk_proof.

#[local] Set Universe Polymorphism.

Section memkv_getcid_proof.

Context `{!heapGS Σ, erpcG Σ, urpcregG Σ, kvMapG Σ}.

Lemma wp_GetCIDRPC (s:loc) γ :
  is_KVShardServer s γ -∗
  {{{
       True
  }}}
    KVShardServer__GetCIDRPC #s
  {{{
       cid, RET #cid; erpc_make_client_pre γ.(erpc_gn) cid
  }}}
.
Proof.
  iIntros "#Hmemkv !#" (Φ) "_ HΦ".
  wp_lam.
  iNamed "Hmemkv".
  wp_loadField.
  wp_apply wp_erpc_GetFreshCID; first done.
  done.
Qed.

End memkv_getcid_proof.
