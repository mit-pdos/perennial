From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import urpc.
From Goose.github_com.mit_pdos.secure_chat.full2 Require Import shared fc_ffi_shim.

From Perennial.program_proof.grove_shared Require Import urpc_proof.
From Perennial.program_proof.chat.full2 Require Import encoding.

Section crypto.
Context `{!heapGS Σ}.

Definition is_sk (sk : loc) (P : list u8 → iProp Σ) : iProp Σ.
Admitted.

Definition is_vk (vk : loc) (P : list u8 → iProp Σ) : iProp Σ.
Admitted.

#[global]
Instance is_vk_persistent vk P : Persistent (is_vk vk P).
Proof. Admitted.

Lemma wp_crypto_make cp c P :
  {{{
    "Hcrypto" ∷ cp ↦[struct.t CryptoT] c
  }}}
  CryptoT__MakeKeys #cp
  {{{
    sk vk err, RET (#sk, #vk, #(fc_errno err));
    match err with
    | Some ErrSome => True
    | None =>
      "Hsk" ∷ is_sk sk P ∗
      "#Hvk" ∷ is_vk vk P
    end
  }}}.
Proof. Admitted.

Lemma wp_sign sk P data ldata q :
  {{{
    "His_sk" ∷ is_sk sk P ∗
    "#HP" ∷ □ P ldata ∗
    "Hsl" ∷ own_slice_small data byteT q ldata
  }}}
  SignerT__Sign #sk (slice_val data)
  {{{
    (sig:Slice.t) (lsig:list u8) err, RET (slice_val sig, #(fc_errno err));
    "His_sk" ∷ is_sk sk P ∗
    "Hsl" ∷ own_slice_small data byteT q ldata ∗
    match err with
    | Some ErrSome => True
    | None =>
      "Hsig" ∷ own_slice_small sig byteT 1 lsig
    end
  }}}.
Proof. Admitted.

Lemma wp_verify vk P sig q1 (lsig:list u8) data q2 (ldata:list u8) :
  {{{
    "#His_vk" ∷ is_vk vk P ∗
    "Hsig_sl" ∷ own_slice_small sig byteT q1 lsig ∗
    "Hdata_sl" ∷ own_slice_small data byteT q2 ldata
  }}}
  VerifierT__Verify #vk (slice_val sig) (slice_val data)
  {{{
    err, RET #(fc_errno err);
    "#His_vk" ∷ is_vk vk P ∗
    "Hsig_sl" ∷ own_slice_small sig byteT q1 lsig ∗
    "Hdata_sl" ∷ own_slice_small data byteT q2 ldata ∗
    match err with
    | Some ErrSome => True
    | None =>
      "#HP" ∷ □ P ldata
    end
  }}}.
Proof. Admitted.

End crypto.

Section rpc.
Context `{!heapGS Σ}.

Definition is_uRPCClient (clp:loc) : iProp Σ.
Admitted.

Lemma wp_urpc_make srv :
  {{{ True }}}
  MakeClient #srv
  {{{
    cli_p, RET #cli_p;
    "Hurpc" ∷ is_uRPCClient cli_p
  }}}.
Proof. Admitted.

Lemma wp_call cli_p arg_in q1 (larg_in:list u8) arg_out q2 (larg_out:list u8) id time :
  {{{
    "Hurpc" ∷ is_uRPCClient cli_p ∗
    "Hin" ∷ own_slice_small arg_in byteT q1 larg_in ∗
    "Hout" ∷ own_slice_small arg_out byteT q2 larg_out
  }}}
  Client__Call #cli_p #id (slice_val arg_in) (slice_val arg_out) #time
  {{{
    err (new_out:list u8), RET #(call_errno err);
    "Hurpc" ∷ is_uRPCClient cli_p ∗
    match err with
    | Some CallErrTimeout => True
    | Some CallErrDisconnect => True
    | None =>
      "Hout" ∷ own_slice_small arg_out byteT q2 new_out
    end
  }}}.
Proof. Admitted.

End rpc.
