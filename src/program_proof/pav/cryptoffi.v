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

Lemma hash_deterministic d h1 h2 :
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

(* own_sk only stores the sk ptr. the actual sk never leaves the ffi.
this prevents code from accidentally leaking it.
need to connect sk with pk for is_sig. *)
Definition own_sk (sk : Slice.t) (pk : list w8) (P : list w8 → iProp Σ) : iProp Σ.
Admitted.

Definition is_pk (pk : list w8) (P : list w8 → iProp Σ) : iProp Σ.
Admitted.

#[global]
Instance is_pk_persistent pk P : Persistent (is_pk pk P).
Proof. Admitted.

(* witness that we ran the sign op and got back sig. *)
Definition is_sig (pk msg sig : list w8) : iProp Σ.
Admitted.

#[global]
Instance is_sig_persistent pk msg sig : Persistent (is_sig pk msg sig).
Proof. Admitted.

Lemma wp_GenerateKey P :
  {{{
    "%Hpersis" ∷ ⌜∀ l, Persistent (P l)⌝
  }}}
  GenerateKey #()
  {{{
    sl_pk pk sl_sk, RET ((slice_val sl_pk), (slice_val sl_sk));
    "Hsl_pk" ∷ own_slice_small sl_pk byteT (DfracOwn 1) pk ∗
    "#Hpk" ∷ is_pk pk P ∗
    "Hsk" ∷ own_sk sl_sk pk P
 }}}.
Proof. Admitted.

Lemma wp_Sign sl_sk pk P sl_msg msg d0 :
  {{{
    "Hsk" ∷ own_sk sl_sk pk P ∗
    "HP" ∷ P msg ∗
    "Hmsg" ∷ own_slice_small sl_msg byteT d0 msg
  }}}
  PrivateKey__Sign (slice_val sl_sk) (slice_val sl_msg)
  {{{
    sl_sig (sig : list w8), RET (slice_val sl_sig);
    "Hsk" ∷ own_sk sl_sk pk P ∗
    "Hmsg" ∷ own_slice_small sl_msg byteT d0 msg ∗
    "Hsl_sig" ∷ own_slice_small sl_sig byteT (DfracOwn 1) sig ∗
    "#Hsig" ∷ is_sig pk msg sig
  }}}.
Proof. Admitted.

Lemma wp_Verify P sl_pk pk sl_sig sl_msg (sig msg : list w8) d0 d1 d2 :
  {{{
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗
    "Hsl_sig" ∷ own_slice_small sl_sig byteT d1 sig ∗
    "Hsl_msg" ∷ own_slice_small sl_msg byteT d2 msg
  }}}
  PublicKey__Verify (slice_val sl_pk) (slice_val sl_msg) (slice_val sl_sig)
  {{{
    (ok : bool), RET #ok;
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗
    "Hsl_sig" ∷ own_slice_small sl_sig byteT d1 sig ∗
    "Hsl_msg" ∷ own_slice_small sl_msg byteT d2 msg ∗
    "His_sig" ∷ (is_sig pk msg sig -∗ ⌜ ok = true ⌝) ∗
    "Hok" ∷ (is_pk pk P -∗ if ok then P msg else True)
  }}}.
Proof. Admitted.

End proof.
