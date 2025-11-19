From New.generatedproof.github_com.sanjit_bhat.pav Require Import cryptoffi.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

From New.proof.crypto Require Import ed25519.

Module cryptoffi.

Definition hash_len := 32.
Lemma hash_len_unfold : hash_len = 32.
Proof. done. Qed.
#[global] Hint Rewrite hash_len_unfold : word.
#[global] Opaque hash_len.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit cryptoffi := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf cryptoffi := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop cryptoffi get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init ∗ is_go_context ∗ □ is_pkg_defined cryptoffi }}}
    cryptoffi.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init cryptoffi }}}.
Proof.
  intros Hinit. wp_start as "(Hown & #? & #Hdef)".
  wp_call. wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  wp_apply (ed25519.wp_initialize' with "[$Hown]") as "[Hown #?]".
  { naive_solver. }
  { iModIntro. iEval simpl_is_pkg_defined in "Hdef". iPkgInit. }
  wp_call.
  iEval (rewrite is_pkg_init_unfold /=).
  by iFrame "∗#".
Qed.

(** Hashes. *)

(* is_hash says that [data] will hash to [hash].
relative to the crypto model, it says the inputs are in the set of hashes. *)
Definition is_hash (data : option (list w8)) (hash : list w8) : iProp Σ.
Proof. Admitted.

#[global] Instance is_hash_pers data hash : Persistent (is_hash data hash).
Proof. Admitted.

Lemma is_hash_det data hash0 hash1 :
  is_hash (Some data) hash0 -∗ is_hash (Some data) hash1 -∗ ⌜hash0 = hash1⌝.
Proof. Admitted.

Lemma is_hash_inj data0 data1 hash :
  is_hash data0 hash -∗ is_hash data1 hash -∗ ⌜data0 = data1⌝.
Proof. Admitted.

Lemma is_hash_len data hash :
  is_hash data hash -∗ ⌜Z.of_nat $ length hash = hash_len⌝.
Proof. Admitted.

(* key feature of prophecy hash model.
TODO: this is missing some gnames to pin everything down. *)
Lemma is_hash_invert hash :
  Z.of_nat $ length hash = hash_len → ⊢
  ∃ data, is_hash data hash.
Proof. Admitted.

Definition own_Hasher (ptr : loc) (data : list w8) : iProp Σ.
Proof. Admitted.

Lemma wp_NewHasher :
  {{{ is_pkg_init cryptoffi }}}
  @! cryptoffi.NewHasher #()
  {{{
    ptr_hr, RET #ptr_hr;
    "Hown_hr" ∷ own_Hasher ptr_hr []
  }}}.
Proof. Admitted.

Lemma wp_Hasher_Write hr data sl_b d0 b :
  {{{
    is_pkg_init cryptoffi ∗
    "Hown_hr" ∷ own_Hasher hr data ∗
    "Hsl_b" ∷ sl_b ↦*{d0} b
  }}}
  hr @ (ptrT.id cryptoffi.Hasher.id) @ "Write" #sl_b
  {{{
    RET #();
    "Hown_hr" ∷ own_Hasher hr (data ++ b) ∗
    "Hsl_b" ∷ sl_b ↦*{d0} b
  }}}.
Proof. Admitted.

Lemma wp_Hasher_Sum sl_b_in hr data b_in :
  {{{
    is_pkg_init cryptoffi ∗
    "Hown_hr" ∷ own_Hasher hr data ∗
    "Hsl_b_in" ∷ sl_b_in ↦* b_in
  }}}
  hr @ (ptrT.id cryptoffi.Hasher.id) @ "Sum" #sl_b_in
  {{{
    sl_b_out hash, RET #sl_b_out;
    "Hown_hr" ∷ own_Hasher hr data ∗
    "Hsl_b_out" ∷ sl_b_out ↦* (b_in ++ hash) ∗
    "#His_hash" ∷ is_hash (Some data) hash
  }}}.
Proof. Admitted.

(** Signatures. *)

(* own_sig_sk says that an sk is in-distribution.
furthermore, it came from calling the Generate fn,
and the underlying sk is enclosed in the ffi,
forcing all users to establish the sigpred.
pk is a mathematical list so it can leave the ffi and be sent
between parties. *)
Definition own_sig_sk (ptr_sk : loc) (pk : list w8) (P : list w8 → iProp Σ) : iProp Σ.
Admitted.

(* think of this as DfracDiscarded. *)
#[global] Instance own_sig_sk_pers ptr_sk pk P :
  Persistent (own_sig_sk ptr_sk pk P).
Proof. Admitted.

(* is_sig_pk says that pk is in-distribution.
also, that it came from the Generate fn,
tied by P to a corresponding sk in the ffi. *)
Definition is_sig_pk (pk : list w8) (P : list w8 → iProp Σ) : iProp Σ.
Admitted.

#[global] Instance is_sig_pk_pers pk P : Persistent (is_sig_pk pk P).
Proof. Admitted.

Lemma own_sig_sk_to_pk ptr_sk pk P : own_sig_sk ptr_sk pk P -∗ is_sig_pk pk P.
Proof. Admitted.

(* is_sig says that Verify will ret True on these inputs.
relative to the crypto model, it says the inputs are in the set of
memoized=True Verify inputs. *)
Definition is_sig (pk msg sig : list w8) : iProp Σ.
Admitted.

#[global] Instance is_sig_pers pk msg sig : Persistent (is_sig pk msg sig).
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
  {{{ is_pkg_init cryptoffi }}}
  @! cryptoffi.SigGenerateKey #()
  {{{
    (sl_pk : cryptoffi.SigPublicKey.t) pk ptr_sk, RET (#sl_pk, #ptr_sk);
    "Hsl_sig_pk" ∷ sl_pk ↦* pk ∗
    "#His_sig_pk" ∷ is_sig_pk pk P ∗
    "#Hown_sig_sk" ∷ own_sig_sk ptr_sk pk P
 }}}.
Proof. Admitted.

Lemma wp_SigPrivateKey_Sign ptr_sk pk P sl_msg msg d0 :
  {{{
    is_pkg_init cryptoffi ∗
    "#Hown_sig_sk" ∷ own_sig_sk ptr_sk pk P ∗
    "Hsl_msg" ∷ sl_msg ↦*{d0} msg ∗
    "HP" ∷ P msg
  }}}
  ptr_sk @ (ptrT.id cryptoffi.SigPrivateKey.id) @ "Sign" #sl_msg
  {{{
    sl_sig (sig : list w8), RET #sl_sig;
    "Hsl_msg" ∷ sl_msg ↦*{d0} msg ∗
    "Hsl_sig" ∷ sl_sig ↦* sig ∗
    "#His_sig" ∷ is_sig pk msg sig
  }}}.
Proof. Admitted.

Lemma wp_SigPublicKey_Verify (sl_pk : cryptoffi.SigPublicKey.t) pk
    sl_msg msg sl_sig sig d0 d1 d2 :
  {{{
    is_pkg_init cryptoffi ∗
    "Hsl_sig_pk" ∷ sl_pk ↦*{d0} pk ∗
    "Hsl_msg" ∷ sl_msg ↦*{d1} msg ∗
    "Hsl_sig" ∷ sl_sig ↦*{d2} sig
  }}}
  sl_pk @ cryptoffi.SigPublicKey.id @ "Verify" #sl_msg #sl_sig
  {{{
    (err : bool), RET #err;
    "Hsl_sig_pk" ∷ sl_pk ↦*{d0} pk ∗
    "Hsl_msg" ∷ sl_msg ↦*{d1} msg ∗
    "Hsl_sig" ∷ sl_sig ↦*{d2} sig ∗
    "Hgenie" ∷
      match err with
      | true => ¬ is_sig pk msg sig
      | false =>
        "#His_sig" ∷ is_sig pk msg sig
      end
  }}}.
Proof. Admitted.

(** Verifiable Random Functions (VRFs).
IETF spec: https://www.rfc-editor.org/rfc/rfc9381.html.
we model correctness (is_vrf_proof), "Full Uniqueness" (is_vrf_out_det),
and "Full Collision Resistance" (is_vrf_out_inj). *)

(* own_vrf_sk provides ownership of an sk from the VrfGenerateKey function. *)
Definition own_vrf_sk (ptr_sk : loc) (pk : list w8) : iProp Σ.
Admitted.

(* think of this as DfracDiscarded. *)
#[global] Instance own_vrf_sk_pers ptr_sk pk : Persistent (own_vrf_sk ptr_sk pk).
Proof. Admitted.

(* is_vrf_pk says that pk satisfies certain mathematical crypto checks.
this is in contrast to is_sig_pk, which additionally says that
the corresponding sk never left the ffi. *)
Definition is_vrf_pk (pk : list w8) : iProp Σ.
Admitted.

#[global] Instance is_vrf_pk_pers pk : Persistent (is_vrf_pk pk).
Proof. Admitted.

(* own_vrf_pk just wraps is_vrf_pk with ownership of the heap resources
corresponding to the pk bytes. *)
Definition own_vrf_pk (ptr_pk : loc) (pk : list w8) : iProp Σ.
Admitted.

(* think of this as DfracDiscarded. *)
#[global] Instance own_vrf_pk_pers ptr_pk pk : Persistent (own_vrf_pk ptr_pk pk).
Proof. Admitted.

Lemma own_vrf_pk_valid ptr_pk pk : own_vrf_pk ptr_pk pk -∗ is_vrf_pk pk.
Proof. Admitted.

(* is_vrf_proof helps model correctness.
i.e., a caller gets this from Prove / Verify,
and uses it to prove that Verify should not return an error. *)
Definition is_vrf_proof (pk data proof : list w8) : iProp Σ.
Admitted.

#[global] Instance is_vrf_proof_pers pk data proof :
  Persistent (is_vrf_proof pk data proof).
Proof. Admitted.

(* is_vrf_out gets returned from Prove / Verify and abstracts out
the specific proof associated with a VRF computation.
this is convenient because the spec does not rule out multiple proofs
between the same pk, data, and output. *)
Definition is_vrf_out (pk data out : list w8) : iProp Σ.
Admitted.

#[global] Instance is_vrf_out_pers pk data out :
  Persistent (is_vrf_out pk data out).
Proof. Admitted.

(* is_vrf_out_det models "Full Uniqueness".
this always holds for ECVRF. *)
Lemma is_vrf_out_det pk data out0 out1 :
  is_vrf_out pk data out0 -∗ is_vrf_out pk data out1 -∗ ⌜ out0 = out1⌝.
Proof. Admitted.

(* is_vrf_out_inj models "Full Collision Resistance".
"Full" (as opposed to "Trusted") holds for ECVRF as long
as the `validate_key` parameter to `ECVRF_verify` is true.
key validation is done when running `VrfPublicKeyDecode`
on an adversarially-provided pk. *)
Lemma is_vrf_out_inj pk data0 data1 out :
  is_vrf_out pk data0 out -∗ is_vrf_out pk data1 out -∗ ⌜ data0 = data1 ⌝.
Proof. Admitted.

Lemma is_vrf_out_len pk data out :
  is_vrf_out pk data out -∗ ⌜ Z.of_nat (length out) = hash_len ⌝.
Proof. Admitted.

Lemma wp_VrfGenerateKey :
  {{{ is_pkg_init cryptoffi }}}
  @! cryptoffi.VrfGenerateKey #()
  {{{
    (ptr_pk ptr_sk : loc) (pk : list w8), RET (#ptr_pk, #ptr_sk);
    "#Hown_vrf_pk" ∷ own_vrf_pk ptr_pk pk ∗
    "#Hown_vrf_sk" ∷ own_vrf_sk ptr_sk pk
  }}}.
Proof. Admitted.

Lemma wp_VrfPrivateKey_Prove ptr_sk pk sl_data (data : list w8) d0 :
  {{{
    is_pkg_init cryptoffi ∗
    "#Hown_vrf_sk" ∷ own_vrf_sk ptr_sk pk ∗
    "Hsl_data" ∷ sl_data ↦*{d0} data
  }}}
  ptr_sk @ (ptrT.id cryptoffi.VrfPrivateKey.id) @ "Prove" #sl_data
  {{{
    sl_out sl_proof (out proof : list w8), RET (#sl_out, #sl_proof);
    "Hsl_data" ∷ sl_data ↦*{d0} data ∗
    "Hsl_out" ∷ sl_out ↦* out ∗
    "Hsl_proof" ∷ sl_proof ↦* proof ∗
    "#His_vrf_proof" ∷ is_vrf_proof pk data proof ∗
    "#His_vrf_out" ∷ is_vrf_out pk data out
  }}}.
Proof. Admitted.

Lemma wp_VrfPrivateKey_Evaluate ptr_sk pk sl_data (data : list w8) d0 :
  {{{
    is_pkg_init cryptoffi ∗
    "#Hown_vrf_sk" ∷ own_vrf_sk ptr_sk pk ∗
    "Hsl_data" ∷ sl_data ↦*{d0} data
  }}}
  ptr_sk @ (ptrT.id cryptoffi.VrfPrivateKey.id) @ "Evaluate" #sl_data
  {{{
    sl_out (out : list w8), RET #sl_out;
    "Hsl_data" ∷ sl_data ↦*{d0} data ∗
    "Hsl_out" ∷ sl_out ↦* out ∗
    "#His_vrf_out" ∷ is_vrf_out pk data out
  }}}.
Proof. Admitted.

Lemma wp_VrfPublicKey_Verify ptr_pk pk sl_data sl_proof (data proof : list w8) d0 d1 :
  {{{
    is_pkg_init cryptoffi ∗
    "#Hown_vrf_pk" ∷ own_vrf_pk ptr_pk pk ∗
    "Hsl_data" ∷ sl_data ↦*{d0} data ∗
    "Hsl_proof" ∷ sl_proof ↦*{d1} proof
  }}}
  ptr_pk @ (ptrT.id cryptoffi.VrfPublicKey.id) @ "Verify" #sl_data #sl_proof
  {{{
    sl_out (out : list w8) (err : bool), RET (#sl_out, #err);
    "Hsl_data" ∷ sl_data ↦*{d0} data ∗
    "Hsl_proof" ∷ sl_proof ↦*{d1} proof ∗
    "Hsl_out" ∷ sl_out ↦* out ∗
    "Hgenie" ∷
      match err with
      | true => ¬ is_vrf_proof pk data proof
      | false =>
        "#His_proof" ∷ is_vrf_proof pk data proof ∗
        "#His_out" ∷ is_vrf_out pk data out
      end
  }}}.
Proof. Admitted.

Lemma wp_VrfPublicKeyEncode ptr_pk pk :
  {{{
    is_pkg_init cryptoffi ∗
    "#Hown_vrf_pk" ∷ own_vrf_pk ptr_pk pk
  }}}
  @! cryptoffi.VrfPublicKeyEncode #ptr_pk
  {{{
    sl_enc, RET #sl_enc;
    "Hsl_enc" ∷ sl_enc ↦* pk ∗
    "#His_vrf_pk" ∷ is_vrf_pk pk
  }}}.
Proof. Admitted.

Lemma wp_VrfPublicKeyDecode sl_enc pk d0 :
  {{{
    is_pkg_init cryptoffi ∗
    "Hsl_enc" ∷ sl_enc ↦*{d0} pk
  }}}
  @! cryptoffi.VrfPublicKeyDecode #sl_enc
  {{{
    ptr_pk err, RET (#ptr_pk, #err);
    "Hsl_enc" ∷ sl_enc ↦*{d0} pk ∗
    "Hgenie" ∷
      match err with
      | true => ¬ is_vrf_pk pk
      | false =>
        "#Hown_vrf_pk" ∷ own_vrf_pk ptr_pk pk
      end
  }}}.
Proof. Admitted.

(** Cryptographic randomness. *)

Lemma wp_RandBytes (n : w64) :
  {{{ is_pkg_init cryptoffi }}}
  @! cryptoffi.RandBytes #n
  {{{
    sl_b (b : list w8), RET #sl_b;
    "Hsl_b" ∷ sl_b ↦* b ∗
    "%Hlen_b" ∷ ⌜length b = uint.nat n⌝
  }}}.
Proof. Admitted.

End proof.
End cryptoffi.
