From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import cryptoffi.

Section proof.
Context `{!heapGS Σ}.

(* Hashing. *)

Definition is_hash (data hash : list u8) : iProp Σ.
Proof. Admitted.

#[global]
Instance is_hash_persistent data hash : Persistent (is_hash data hash).
Proof. Admitted.

#[global]
Instance is_hash_timeless data hash : Timeless (is_hash data hash).
Proof. Admitted.

Lemma hash_is_func d h1 h2 :
  is_hash d h1 -∗ is_hash d h2 -∗ ⌜h1 = h2⌝.
Proof. Admitted.

Lemma hash_inj d1 d2 h :
  is_hash d1 h -∗ is_hash d2 h -∗ ⌜d1 = d2⌝.
Proof. Admitted.

Lemma hash_len d h :
  is_hash d h -∗ ⌜length h = 32%nat⌝.
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

(* Signing and verifying. *)

Definition own_sk (sk : Slice.t) (P : list u8 → iProp Σ) (hon : bool) : iProp Σ.
Admitted.

Definition is_pk (pk : Slice.t) (P : list u8 → iProp Σ) (hon : bool) : iProp Σ.
Admitted.

#[global]
Instance is_pk_persistent pk P hon : Persistent (is_pk pk P hon).
Proof. Admitted.

Lemma wp_MakeKeys P hon :
  {{{
    "%Hpersis" ∷ ⌜∀ l, Persistent (P l)⌝
  }}}
  MakeKeys #()
  {{{
    sk pk, RET ((slice_val sk), (slice_val pk));
    "Hsk" ∷ own_sk sk P hon ∗
    "#Hpk" ∷ is_pk pk P hon
  }}}.
Proof. Admitted.

Lemma wp_Sign sk P hon sl_data data :
  {{{
    "Hsk" ∷ own_sk sk P hon ∗
    "HP" ∷ P data ∗
    "Hdata" ∷ own_slice_small sl_data byteT 1 data
  }}}
  Sign (slice_val sk) (slice_val sl_data)
  {{{
    sl_sig (sig : list u8), RET (slice_val sl_sig);
    "Hsk" ∷ own_sk sk P hon ∗
    "Hdata" ∷ own_slice_small sl_data byteT 1 data ∗
    "Hsig" ∷ own_slice_small sl_sig byteT 1 sig
  }}}.
Proof. Admitted.

Lemma wp_Verify pk P hon sl_sig (sig : list u8) sl_data (data : list u8) :
  {{{
    "#Hpk" ∷ is_pk pk P hon ∗
    "Hsig" ∷ own_slice_small sl_sig byteT 1 sig ∗
    "Hdata" ∷ own_slice_small sl_data byteT 1 data
  }}}
  Verify (slice_val pk) (slice_val sl_data) (slice_val sl_sig)
  {{{
    (err : bool), RET #err;
    "Hsig" ∷ own_slice_small sl_sig byteT 1 sig ∗
    "Hdata" ∷ own_slice_small sl_data byteT 1 data ∗
    if negb err && hon then
      "HP" ∷ P data
    else True%I
  }}}.
Proof. Admitted.

End proof.
