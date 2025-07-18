From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From New.generatedproof.github_com.sanjit_bhat.pav Require Import cryptoffi.

Module cryptoffi.

Notation hash_len := 32 (only parsing).

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !goGlobalsGS Σ}.

#[global]
Program Instance is_pkg_init_cryptoffi : IsPkgInit cryptoffi := ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_cryptoffi.
#[local] Transparent is_pkg_init_cryptoffi.

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

Lemma is_hash_det data hash0 hash1 :
  is_hash data hash0 -∗ is_hash data hash1 -∗ ⌜ hash0 = hash1 ⌝.
Proof. Admitted.

Lemma is_hash_inj data0 data1 hash :
  is_hash data0 hash -∗ is_hash data1 hash -∗ ⌜ data0 = data1⌝.
Proof. Admitted.

Lemma is_hash_len data hash :
  is_hash data hash -∗ ⌜ Z.of_nat (length hash) = hash_len ⌝.
Proof. Admitted.

Definition own_Hasher (ptr : loc) (data : list w8) : iProp Σ. Proof. Admitted.

Lemma wp_NewHasher :
  {{{ is_pkg_init cryptoffi }}}
  cryptoffi @ "NewHasher" #()
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
  hr @ cryptoffi @ "Hasher'ptr" @ "Write" #sl_b
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
  hr @ cryptoffi @ "Hasher'ptr" @ "Sum" #sl_b_in
  {{{
    sl_b_out hash, RET #sl_b_out;
    "Hown_hr" ∷ own_Hasher hr data ∗
    "Hsl_b_out" ∷ sl_b_out ↦* (b_in ++ hash) ∗
    "#His_hash" ∷ is_hash data hash
  }}}.
Proof. Admitted.

End proof.
End cryptoffi.
