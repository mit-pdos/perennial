From Perennial.Helpers Require Import ModArith.
From Goose.github_com.mit_pdos.gokv Require Import connman.
From Perennial.program_proof Require Import grove_prelude std_proof.
From Perennial.program_proof Require Import marshal_proof.
From Perennial.algebra Require Import auth_map.
From Perennial.program_proof.memkv Require Import rpc_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

Section connman_proof.

Context `{!rpcregG Σ}.
Context `{hG: !heapGS Σ}.
Definition connmanN := nroot .@ "connman".
Definition own_ConnMan (c_ptr:loc) : iProp Σ := True.
Definition is_ConnMan (c_ptr:loc) : iProp Σ :=
  ∃ mu,
  "#Hmu" ∷ readonly (c_ptr ↦[ConnMan :: "mu"] mu) ∗
  "#Hinv" ∷ is_lock connmanN mu (own_ConnMan c_ptr)
.

Lemma wp_ConnMan__Call {X:Type} (x:X) γsmap (c_ptr:loc) (rpcid:u64) (host:u64) req rep_out_ptr
      (timeout_ms : u64) dummy_sl_val (reqData:list u8) Pre Post :
  is_ConnMan c_ptr -∗
  {{{
      is_slice req byteT 1 reqData ∗
      rep_out_ptr ↦[slice.T byteT] dummy_sl_val ∗
      handler_is γsmap X host rpcid Pre Post ∗
      □(▷ Pre x reqData)
  }}}
      ConnMan__CallAtLeastOnce #c_ptr #host #rpcid (slice_val req) #rep_out_ptr #timeout_ms
    {{{
      RET #();
      is_slice req byteT 1 reqData ∗
      ∃ rep_sl (repData:list u8),
        rep_out_ptr ↦[slice.T byteT] (slice_val rep_sl) ∗
        typed_slice.is_slice rep_sl byteT 1 repData ∗
        (▷ Post x reqData repData)
    }}}
    .
Proof.
  iIntros "#Hconn !#" (Φ) "Hpre HΦ".
  iNamed "Hconn".
  Opaque rpc.RPCClient.
  Opaque zero_val.
  wp_lam.
  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (cl) "Hcl".
  wp_pures.
  wp_loadField.
  wp_apply (acquire_spec with "Hinv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
Admitted.

End connman_proof.
