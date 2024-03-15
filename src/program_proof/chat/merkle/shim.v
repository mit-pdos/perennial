From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.secure_chat.merkle Require Import merkle_shim.

Section crypto.
Context `{!heapGS Σ}.

Definition is_hash (data hash:list u8) : iProp Σ.
Proof. Admitted.

#[global]
Instance is_hash_persistent data hash : Persistent (is_hash data hash).
Proof. Admitted.

Lemma hash_is_func d h1 h2 :
  is_hash d h1 -∗ is_hash d h2 -∗ ⌜h1 = h2⌝.
Proof. Admitted.

Lemma hash_inj d1 d2 h :
  is_hash d1 h -∗ is_hash d2 h -∗ ⌜d1 = d2⌝.
Proof. Admitted.

Lemma wp_Hash sl_data data :
  {{{
    "Hdata" ∷ own_slice_small sl_data byteT 1 data
  }}}
  Hash (slice_val sl_data)
  {{{
    sl_hash hash, RET (slice_val sl_hash);
    "Hdata" ∷ own_slice_small sl_data byteT 1 data ∗
    "Hhash" ∷ own_slice_small sl_hash byteT 1 hash ∗
    "#His_hash" ∷ is_hash data hash
  }}}.
Proof. Admitted.

End crypto.
