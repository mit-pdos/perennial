From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import cryptoffi.

Notation hash_len := (32%nat) (only parsing).

Section proof.
Context `{!heapGS Σ}.

(* Hashes. *)

(* is_hash says that [data] will hash to [hash].
relative to the crypto model, it says the inputs are in the set of hashes. *)
Definition is_hash (data hash : list w8) : iProp Σ.
Proof. Admitted.

#[global]
Instance is_hash_persistent data hash : Persistent (is_hash data hash).
Proof. Admitted.

#[global]
Instance is_hash_timeless data hash : Timeless (is_hash data hash).
Proof. Admitted.

Lemma is_hash_det d h1 h2 :
  is_hash d h1 -∗ is_hash d h2 -∗ ⌜h1 = h2⌝.
Proof. Admitted.

Lemma is_hash_inj d1 d2 h :
  is_hash d1 h -∗ is_hash d2 h -∗ ⌜d1 = d2⌝.
Proof. Admitted.

Lemma is_hash_len d h :
  is_hash d h -∗ ⌜length h = hash_len⌝.
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

(* own_sig_sk says that an sk is in-distribution.
sk is a ptr bc the actual sk never leaves the ffi.
this prevents code from accidentally leaking it.
pk is a mathematical list bc it could potentially be shared,
altho our app doesn't make use of that. *)
Definition own_sig_sk (ptr_sk : loc) (pk : list w8) (P : list w8 → iProp Σ) : iProp Σ.
Admitted.

(* is_sig_pk says that a pk is in-distribution. *)
Definition is_sig_pk (pk : list w8) (P : list w8 → iProp Σ) : iProp Σ.
Admitted.

#[global]
Instance is_sig_pk_persistent pk P : Persistent (is_sig_pk pk P).
Proof. Admitted.

(* is_sig says that Verify will ret True on these inputs.
relative to the crypto model, it says the inputs are in the set of
memoized=True Verify inputs. *)
Definition is_sig (pk msg sig : list w8) : iProp Σ.
Admitted.

#[global]
Instance is_sig_persistent pk msg sig : Persistent (is_sig pk msg sig).
Proof. Admitted.

(* is_sig_to_pred has two cases:
1) the sig came from sign. P clearly holds.
2) an adversary forged the sig.
EUF-CMA guarantees that this only happens if the genuine key holder
signed the same msg in the past. P holds from the orig signing op. *)
Lemma is_sig_to_pred pk P msg sig :
  is_sig_pk pk P -∗ is_sig pk msg sig -∗ P msg.
Proof. Admitted.

Lemma wp_SigGenerateKey P :
  (∀ l, Persistent (P l)) →
  {{{
        True
  }}}
  SigGenerateKey #()
  {{{
    sl_pk pk ptr_sk, RET ((slice_val sl_pk), #ptr_sk);
    "Hsl_sig_pk" ∷ own_slice_small sl_pk byteT (DfracOwn 1) pk ∗
    "#His_sig_pk" ∷ is_sig_pk pk P ∗
    "Hown_sig_sk" ∷ own_sig_sk ptr_sk pk P
 }}}.
Proof. Admitted.

Lemma wp_SigPrivateKey__Sign ptr_sk pk P sl_msg msg d0 :
  {{{
    "Hown_sig_sk" ∷ own_sig_sk ptr_sk pk P ∗
    "HP" ∷ P msg ∗
    "Hsl_msg" ∷ own_slice_small sl_msg byteT d0 msg
  }}}
  SigPrivateKey__Sign #ptr_sk (slice_val sl_msg)
  {{{
    sl_sig (sig : list w8), RET (slice_val sl_sig);
    "Hown_sig_sk" ∷ own_sig_sk ptr_sk pk P ∗
    "Hmsg" ∷ own_slice_small sl_msg byteT d0 msg ∗
    "Hsl_sig" ∷ own_slice_small sl_sig byteT (DfracOwn 1) sig ∗
    "#His_sig" ∷ is_sig pk msg sig
  }}}.
Proof. Admitted.

Lemma wp_SigPublicKey__Verify P sl_pk pk sl_sig sl_msg (sig msg : list w8) d0 d1 d2 :
  {{{
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗
    "Hsl_sig" ∷ own_slice_small sl_sig byteT d1 sig ∗
    "Hsl_msg" ∷ own_slice_small sl_msg byteT d2 msg
  }}}
  SigPublicKey__Verify (slice_val sl_pk) (slice_val sl_msg) (slice_val sl_sig)
  {{{
    (err : bool), RET #err;
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗
    "Hsl_sig" ∷ own_slice_small sl_sig byteT d1 sig ∗
    "Hsl_msg" ∷ own_slice_small sl_msg byteT d2 msg ∗
    "Hgenie" ∷ (is_sig pk msg sig ∗-∗ ⌜ err = false ⌝) ∗
    (* TODO: remove. subsumed by is_sig_to_pred. *)
    "HP" ∷ (is_sig_pk pk P -∗ if negb err then P msg else True)
  }}}.
Proof. Admitted.

(* Verifiable Random Functions (VRFs).
our model omits the following, since they're not needed in KT.
- a data predicate. this allows the sk owner to prove that hashed
  data satisfies some properties.
- correctness.
- injectivity. *)

(* own_vrf_sk provides ownership of an sk from the VrfGenerateKey function. *)
Definition own_vrf_sk (ptr_sk : loc) : iProp Σ.
Admitted.

(* own_vrf_pk provides enough resources for pk_ptr, and says that
pk satisfies certain crypto checks.
however, pk might still be from outside the VrfGenerateKey distribution. *)
Definition own_vrf_pk (ptr_pk : loc) (pk : list w8) : iProp Σ.
Admitted.

(* is_vrf says that for a particular pk, data and hash are tied together,
through the Verify function. *)
Definition is_vrf (pk : list w8) (data : list w8) (hash : list w8) : iProp Σ.
Admitted.

#[global]
Instance is_vrf_persistent pk data hash : Persistent (is_vrf pk data hash).
Proof. Admitted.

Lemma is_vrf_det pk d h1 h2 :
  is_vrf pk d h1 -∗ is_vrf pk d h2 -∗ ⌜h1 = h2⌝.
Proof. Admitted.

Lemma wp_VrfGenerateKey :
  {{{ True }}}
  VrfGenerateKey #()
  {{{
    (ptr_pk ptr_sk : loc) (pk : list w8), RET (#ptr_pk, #ptr_sk);
    "Hown_vrf_pk" ∷ own_vrf_pk ptr_pk pk ∗
    "Hown_vrf_sk" ∷ own_vrf_sk ptr_sk
  }}}.
Proof. Admitted.

Lemma wp_VrfPrivateKey__Hash (ptr_sk : loc) sl_data (data : list w8) d0 :
  {{{
    "Hown_vrf_sk" ∷ own_vrf_sk ptr_sk ∗
    "Hsl_data" ∷ own_slice_small sl_data byteT d0 data
  }}}
  VrfPrivateKey__Hash #ptr_sk (slice_val sl_data)
  {{{
    sl_hash sl_proof (hash proof : list w8), RET (slice_val sl_hash, slice_val sl_proof);
    "Hown_vrf_sk" ∷ own_vrf_sk ptr_sk ∗
    "Hsl_data" ∷ own_slice_small sl_data byteT d0 data ∗
    "Hsl_hash" ∷ own_slice_small sl_hash byteT (DfracOwn 1) hash ∗
    "Hsl_proof" ∷ own_slice_small sl_proof byteT (DfracOwn 1) proof
  }}}.
Proof. Admitted.

Lemma wp_VrfPublicKey__Verify ptr_pk pk sl_data sl_proof (data proof : list w8) d0 d1 :
  {{{
    "Hown_vrf_pk" ∷ own_vrf_pk ptr_pk pk ∗
    "Hsl_data" ∷ own_slice_small sl_data byteT d0 data ∗
    "Hsl_proof" ∷ own_slice_small sl_proof byteT d1 proof
  }}}
  VrfPublicKey__Verify #ptr_pk (slice_val sl_data) (slice_val sl_proof)
  {{{
    sl_hash (hash : list w8) (err : bool), RET (slice_val sl_hash, #err);
    "Hown_vrf_pk" ∷ own_vrf_pk ptr_pk pk ∗
    "Hsl_data" ∷ own_slice_small sl_data byteT d0 data ∗
    "Hsl_proof" ∷ own_slice_small sl_proof byteT d1 proof ∗
    "Hsl_hash" ∷ own_slice_small sl_hash byteT (DfracOwn 1) hash ∗
    "#His_vrf" ∷ (if negb err then is_vrf pk data hash else True)
  }}}.
Proof. Admitted.

Lemma wp_VrfPublicKeyEncode ptr_pk pk :
  {{{
    "Hown_vrf_pk" ∷ own_vrf_pk ptr_pk pk
  }}}
  VrfPublicKeyEncode #ptr_pk
  {{{
    sl_enc, RET slice_val sl_enc;
    "Hsl_enc" ∷ own_slice_small sl_enc byteT (DfracOwn 1) pk
  }}}.
Proof. Admitted.

Lemma wp_VrfPublicKeyDecode sl_enc pk d0 :
  {{{
    "Hsl_enc" ∷ own_slice_small sl_enc byteT d0 pk
  }}}
  VrfPublicKeyDecode (slice_val sl_enc)
  {{{
    (ptr_pk : loc), RET #ptr_pk;
    "Hsl_enc" ∷ own_slice_small sl_enc byteT d0 pk ∗
    "Hown_vrf_pk" ∷ own_vrf_pk ptr_pk pk
  }}}.
Proof. Admitted.

End proof.
