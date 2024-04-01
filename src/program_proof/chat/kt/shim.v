From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import urpc.
From Goose.github_com.mit_pdos.secure_chat.kt Require Import kt_shim.

From Perennial.program_proof.grove_shared Require Import urpc_proof.

Section crypto.
Context `{!heapGS Σ}.

Definition own_sk (sk:loc) (P:list u8 → iProp Σ) (hon:bool) : iProp Σ.
Admitted.

Definition is_vk (vk:loc) (P:list u8 → iProp Σ) (hon:bool) : iProp Σ.
Admitted.

#[global]
Instance is_vk_persistent vk P hon : Persistent (is_vk vk P hon).
Proof. Admitted.

Lemma wp_MakeKeys P hon :
  {{{
    "%Hpersis" ∷ ⌜∀ l, Persistent (P l)⌝
  }}}
  MakeKeys #()
  {{{
    sk vk, RET (#sk, #vk);
    "Hsk" ∷ own_sk sk P hon ∗
    "#Hvk" ∷ is_vk vk P hon
  }}}.
Proof. Admitted.

Lemma wp_Sign sk P hon sl_data data :
  {{{
    "Hsk" ∷ own_sk sk P hon ∗
    "HP" ∷ P data ∗
    "Hdata" ∷ own_slice_small sl_data byteT 1 data
  }}}
  SignerT__Sign #sk (slice_val sl_data)
  {{{
    sl_sig (sig:list u8), RET (slice_val sl_sig);
    "Hsk" ∷ own_sk sk P hon ∗
    "Hdata" ∷ own_slice_small sl_data byteT 1 data ∗
    "Hsig" ∷ own_slice_small sl_sig byteT 1 sig
  }}}.
Proof. Admitted.

Lemma wp_Verify vk P hon sl_sig (sig:list u8) sl_data (data:list u8) :
  {{{
    "#Hvk" ∷ is_vk vk P hon ∗
    "Hsig" ∷ own_slice_small sl_sig byteT 1 sig ∗
    "Hdata" ∷ own_slice_small sl_data byteT 1 data
  }}}
  VerifierT__Verify #vk (slice_val sl_sig) (slice_val sl_data)
  {{{
    (err:u64), RET #err;
    "Hsig" ∷ own_slice_small sl_sig byteT 1 sig ∗
    "Hdata" ∷ own_slice_small sl_data byteT 1 data ∗
    if bool_decide (err = 0) && hon then
      "HP" ∷ P data
    else True%I
  }}}.
Proof. Admitted.

End crypto.

Section rpc.
Context `{!heapGS Σ}.

Definition own_rpc_cli (ptr:loc) : iProp Σ.
Admitted.

Lemma wp_rpc_MakeClient (addr:u64) :
  {{{ True }}}
  MakeClient #addr
  {{{
    ptr, RET #ptr;
    "Hurpc" ∷ own_rpc_cli ptr
  }}}.
Proof. Admitted.

Lemma wp_rpc_Call cli (id:u64) sl_in (inB:list u8) sl_out (time:u64) :
  {{{
    "Hrpc" ∷ own_rpc_cli cli ∗
    "Hin" ∷ own_slice_small sl_in byteT 1 inB
  }}}
  Client__Call #cli #id (slice_val sl_in) (slice_val sl_out) #time
  {{{
    err (out:list u8), RET #err;
    "Hrpc" ∷ own_rpc_cli cli ∗
    "Hin" ∷ own_slice_small sl_in byteT 1 inB ∗
    if bool_decide (err = 0) then
      "Hout" ∷ own_slice_small sl_out byteT 1 out
    else True%I
  }}}.
Proof. Admitted.

End rpc.
