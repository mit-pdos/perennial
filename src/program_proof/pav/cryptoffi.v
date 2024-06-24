From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import cryptoffi.

Section proof.
Context `{!heapGS Σ}.

(* Hashes. *)

Definition is_hash (data hash : list w8) : iProp Σ.
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
    "Hdata" ∷ own_slice_small sl_data byteT (DfracOwn 1) data
  }}}
  Hash (slice_val sl_data)
  {{{
    sl_hash hash, RET (slice_val sl_hash);
    "Hdata" ∷ own_slice_small sl_data byteT (DfracOwn 1) data ∗
    "Hhash" ∷ own_slice_small sl_hash byteT (DfracOwn 1) hash ∗
    "#His_hash" ∷ is_hash data hash
  }}}.
Proof. Admitted.

(* Signatures. *)

Definition own_sk (sk : Slice.t) (P : list w8 → iProp Σ) (hon : bool) : iProp Σ.
Admitted.

Definition is_pk (pk : Slice.t) (P : list w8 → iProp Σ) (hon : bool) : iProp Σ.
Admitted.

#[global]
Instance is_pk_persistent pk P hon : Persistent (is_pk pk P hon).
Proof. Admitted.

Lemma wp_GenerateKey P hon :
  {{{
    "%Hpersis" ∷ ⌜∀ l, Persistent (P l)⌝
  }}}
  GenerateKey #()
  {{{
    pk sk, RET ((slice_val pk), (slice_val sk));
    "#Hpk" ∷ is_pk pk P hon ∗
    "Hsk" ∷ own_sk sk P hon
  }}}.
Proof. Admitted.

Lemma wp_Sign sk P hon sl_msg msg :
  {{{
    "Hsk" ∷ own_sk sk P hon ∗
    "HP" ∷ P msg ∗
    "Hmsg" ∷ own_slice_small sl_msg byteT (DfracOwn 1) msg
  }}}
  PrivateKey__Sign (slice_val sk) (slice_val sl_msg)
  {{{
    sl_sig (sig : list w8), RET (slice_val sl_sig);
    "Hsk" ∷ own_sk sk P hon ∗
    "Hmsg" ∷ own_slice_small sl_msg byteT (DfracOwn 1) msg ∗
    "Hsig" ∷ own_slice_small sl_sig byteT (DfracOwn 1) sig
  }}}.
Proof. Admitted.

Lemma wp_Verify pk P hon sl_sig (sig : list w8) sl_msg (msg : list w8) :
  {{{
    "#Hpk" ∷ is_pk pk P hon ∗
    "Hsig" ∷ own_slice_small sl_sig byteT (DfracOwn 1) sig ∗
    "Hmsg" ∷ own_slice_small sl_msg byteT (DfracOwn 1) msg
  }}}
  PublicKey__Verify (slice_val pk) (slice_val sl_msg) (slice_val sl_sig)
  {{{
    (err : bool), RET #err;
    "Hsig" ∷ own_slice_small sl_sig byteT (DfracOwn 1) sig ∗
    "Hmsg" ∷ own_slice_small sl_msg byteT (DfracOwn 1) msg ∗
    if negb err && hon then
      "HP" ∷ P msg
    else True%I
  }}}.
Proof. Admitted.

End proof.
