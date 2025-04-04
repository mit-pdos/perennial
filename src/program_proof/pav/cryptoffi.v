From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import cryptoffi.

Notation hash_len := 32 (only parsing).

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

Lemma is_hash_det d h0 h1 :
  is_hash d h0 -∗ is_hash d h1 -∗ ⌜ h0 = h1 ⌝.
Proof. Admitted.

Lemma is_hash_inj d0 d1 h :
  is_hash d0 h -∗ is_hash d1 h -∗ ⌜ d0 = d1⌝.
Proof. Admitted.

Lemma is_hash_len d h :
  is_hash d h -∗ ⌜ Z.of_nat (length h) = hash_len ⌝.
Proof. Admitted.

Definition own_hasher (ptr : loc) (data : list w8) : iProp Σ. Admitted.

Lemma wp_NewHasher :
  {{{ True }}}
  NewHasher #()
  {{{
    ptr_hr, RET #ptr_hr;
    "Hown_hr" ∷ own_hasher ptr_hr []
  }}}.
Proof. Admitted.

Lemma wp_Hasher__Write sl_b ptr_hr data d0 b :
  {{{
    "Hown_hr" ∷ own_hasher ptr_hr data ∗
    "Hsl_b" ∷ own_slice_small sl_b byteT d0 b
  }}}
  Hasher__Write #ptr_hr (slice_val sl_b)
  {{{
    RET #();
    "Hown_hr" ∷ own_hasher ptr_hr (data ++ b) ∗
    "Hsl_b" ∷ own_slice_small sl_b byteT d0 b
  }}}.
Proof. Admitted.

Lemma wp_Hasher__Sum sl_b_in ptr_hr data b_in :
  {{{
    "Hown_hr" ∷ own_hasher ptr_hr data ∗
    "Hsl_b_in" ∷ own_slice sl_b_in byteT (DfracOwn 1) b_in
  }}}
  Hasher__Sum #ptr_hr (slice_val sl_b_in)
  {{{
    sl_b_out hash, RET (slice_val sl_b_out);
    "Hown_hr" ∷ own_hasher ptr_hr data ∗
    "Hsl_b_out" ∷ own_slice sl_b_out byteT (DfracOwn 1) (b_in ++ hash) ∗
    "#His_hash" ∷ is_hash data hash
  }}}.
Proof. Admitted.

(* Signatures. *)

(* is_sig_sk says that an sk is in-distribution.
furthermore, it came from calling the Generate fn,
and the underlying sk is enclosed in the ffi,
forcing all users to establish the sigpred.
pk is a mathematical list so it can leave the ffi and be sent
between parties. *)
Definition is_sig_sk (ptr_sk : loc) (pk : list w8) (P : list w8 → iProp Σ) : iProp Σ.
Admitted.

#[global]
Instance is_sig_sk_persistent ptr_sk pk P : Persistent (is_sig_sk ptr_sk pk P).
Proof. Admitted.

(* is_sig_pk says that pk is in-distribution.
also, that it came from the Generate fn,
tied by P to a corresponding sk in the ffi. *)
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

(* the proof for is_sig_to_pred splits into two cases:
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
    "#His_sig_sk" ∷ is_sig_sk ptr_sk pk P
 }}}.
Proof. Admitted.

Lemma wp_SigPrivateKey__Sign ptr_sk pk P sl_msg msg d0 :
  {{{
    "#His_sig_sk" ∷ is_sig_sk ptr_sk pk P ∗
    "HP" ∷ P msg ∗
    "Hsl_msg" ∷ own_slice_small sl_msg byteT d0 msg
  }}}
  SigPrivateKey__Sign #ptr_sk (slice_val sl_msg)
  {{{
    sl_sig (sig : list w8), RET (slice_val sl_sig);
    "Hmsg" ∷ own_slice_small sl_msg byteT d0 msg ∗
    "Hsl_sig" ∷ own_slice_small sl_sig byteT (DfracOwn 1) sig ∗
    "#His_sig" ∷ is_sig pk msg sig
  }}}.
Proof. Admitted.

Lemma wp_SigPublicKey__Verify sl_pk pk sl_sig sl_msg (sig msg : list w8) d0 d1 d2 :
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
    "Hgenie" ∷ (is_sig pk msg sig -∗ ⌜ err = false ⌝) ∗
    "Herr" ∷ (⌜ err = false ⌝ -∗ is_sig pk msg sig)
  }}}.
Proof. Admitted.

(* Verifiable Random Functions (VRFs).
we model "Full Uniqueness" (from the IETF spec) and correctness.
we omit "Full Collision Resistance", since it's not needed in KT. *)

(* is_vrf_sk provides ownership of an sk from the VrfGenerateKey function. *)
Definition is_vrf_sk (ptr_sk : loc) (pk : list w8) : iProp Σ.
Admitted.

#[global]
Instance is_vrf_sk_persistent ptr_sk pk : Persistent (is_vrf_sk ptr_sk pk).
Proof. Admitted.

(* is_vrf_pk says that pk satisfies certain mathematical crypto checks.
this is in contrast to is_sig_pk, which additionally says that
the corresponding sk never left the ffi. *)
Definition is_vrf_pk (ptr_pk : loc) (pk : list w8) : iProp Σ.
Admitted.

#[global]
Instance is_vrf_pk_persistent ptr_pk pk : Persistent (is_vrf_pk ptr_pk pk).
Proof. Admitted.

(* is_vrf says that for a particular pk, data and out are tied together,
through the Verify function. *)
Definition is_vrf (pk : list w8) (data : list w8) (out : list w8) : iProp Σ.
Admitted.

#[global]
Instance is_vrf_persistent pk data out : Persistent (is_vrf pk data out).
Proof. Admitted.

(* VRFs give deterministic outputs, aka, "Full Uniqueness" from IETF spec. *)
Lemma is_vrf_det pk d o1 o2 :
  is_vrf pk d o1 -∗ is_vrf pk d o2 -∗ ⌜o1 = o2⌝.
Proof. Admitted.

Lemma is_vrf_len pk d o :
  is_vrf pk d o -∗ ⌜ Z.of_nat (length o) = hash_len ⌝.
Proof. Admitted.

Lemma wp_VrfGenerateKey :
  {{{ True }}}
  VrfGenerateKey #()
  {{{
    (ptr_pk ptr_sk : loc) (pk : list w8), RET (#ptr_pk, #ptr_sk);
    "#His_vrf_pk" ∷ is_vrf_pk ptr_pk pk ∗
    "#His_vrf_sk" ∷ is_vrf_sk ptr_sk pk
  }}}.
Proof. Admitted.

Lemma wp_VrfPrivateKey__Prove ptr_sk pk sl_data (data : list w8) d0 :
  {{{
    "#His_vrf_sk" ∷ is_vrf_sk ptr_sk pk ∗
    "Hsl_data" ∷ own_slice_small sl_data byteT d0 data
  }}}
  VrfPrivateKey__Prove #ptr_sk (slice_val sl_data)
  {{{
    sl_out sl_proof (out proof : list w8), RET (slice_val sl_out, slice_val sl_proof);
    "Hsl_data" ∷ own_slice_small sl_data byteT d0 data ∗
    "Hsl_out" ∷ own_slice_small sl_out byteT (DfracOwn 1) out ∗
    "Hsl_proof" ∷ own_slice_small sl_proof byteT (DfracOwn 1) proof ∗
    "#His_vrf" ∷ is_vrf pk data out
  }}}.
Proof. Admitted.

Lemma wp_VrfPublicKey__Verify ptr_pk pk sl_data sl_proof (data proof : list w8) d0 d1 :
  {{{
    "#His_vrf_pk" ∷ is_vrf_pk ptr_pk pk ∗
    "Hsl_data" ∷ own_slice_small sl_data byteT d0 data ∗
    "Hsl_proof" ∷ own_slice_small sl_proof byteT d1 proof
  }}}
  VrfPublicKey__Verify #ptr_pk (slice_val sl_data) (slice_val sl_proof)
  {{{
    sl_out (out : list w8) (err : bool), RET (slice_val sl_out, #err);
    "Hsl_data" ∷ own_slice_small sl_data byteT d0 data ∗
    "Hsl_proof" ∷ own_slice_small sl_proof byteT d1 proof ∗
    "Hsl_out" ∷ own_slice_small sl_out byteT (DfracOwn 1) out ∗
    "Hgenie" ∷ (is_vrf pk data out -∗ ⌜ err = false ⌝) ∗
    "Herr" ∷ (⌜ err = false ⌝ -∗ is_vrf pk data out)
  }}}.
Proof. Admitted.

Lemma wp_VrfPublicKeyEncode ptr_pk pk :
  {{{
    "His_vrf_pk" ∷ is_vrf_pk ptr_pk pk
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
    "His_vrf_pk" ∷ is_vrf_pk ptr_pk pk
  }}}.
Proof. Admitted.

End proof.
