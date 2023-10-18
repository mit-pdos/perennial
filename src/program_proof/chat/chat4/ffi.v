From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.secure_chat Require Import chat4.

Section ffi.
Context `{!heapGS Σ}.

Definition valid_sk (sk : loc) (P : list u8 → iProp Σ) : iProp Σ.
Admitted.

Definition valid_vk (vk : loc) (P : list u8 → iProp Σ) : iProp Σ.
Admitted.

Lemma wp_makeKeys P:
  {{{
    True
  }}}
  makeKeys #()
  {{{
    sk vk, RET (#sk, #vk);
    valid_sk sk P ∗
    valid_vk vk P
  }}}.
Proof. Admitted.

Lemma wp_sign P sk p_sl l_bytes:
  {{{
    "Hsk" ∷ valid_sk sk P ∗
    "Hsl" ∷ own_slice_small p_sl byteT 1 l_bytes ∗
    "HP" ∷ P l_bytes
  }}}
  signerT__sign #sk (slice_val p_sl)
  {{{
    (sig : Slice.t) (sig_bytes : list u8), RET (slice_val sig);
    own_slice sig byteT 1 sig_bytes
  }}}.
Proof. Admitted.

Lemma wp_verify P vk sl_data sl_sig (l_data : list u8) (l_sig : list u8):
  {{{
    "Hvk" ∷ valid_vk vk P ∗
    "Hsld" ∷ own_slice_small sl_data byteT 1 l_data ∗
    "Hsls" ∷ own_slice_small sl_sig byteT 1 l_sig
  }}}
  verify #vk (slice_val sl_data) (slice_val sl_sig)
  {{{
    (err : bool), RET #err;
    if err then True else P l_data
  }}}.
Proof. Admitted.

Lemma wp_rpcCall rpcId sl_in sl_out (l_any : list u8):
  {{{
    "Hslo" ∷ own_slice_small sl_out byteT 1 l_any
  }}}
  rpcCall #rpcId (slice_val sl_in) (slice_val sl_out)
  {{{
    (l_some : list u8), RET #();
    own_slice_small sl_out byteT 1 l_some
  }}}.
Proof. Admitted.

End ffi.
