From Perennial.program_proof.pav Require Import prelude.
From Goose.github_com.mit_pdos.pav Require Import cryptoffi.

Notation hash_len := 32 (only parsing).

Section proof.
Context `{!heapGS Σ}.
Context `{!ghost_varG Σ (list (list w8 * list w8))}.

(* [hash_fun] is the hash function itself: [hash_fun v] is the hash of [v].
 *)
Definition hash_fun : list w8 -> list w8.
Admitted.

Lemma hash_fun_len data :
  Z.of_nat (length (hash_fun data)) = hash_len.
Admitted.


Record hash_gnames := {
  hash_namespace: namespace;
  hash_hist: gname;
  hash_proph: proph_id;
  hash_map: gmap (list w8) (list w8);
}.

Definition is_hash_history γ (h: list (list w8 * list w8)) : iProp Σ :=
  ghost_var (hash_hist γ) 1%Qp h.

Definition hash_pair_to_val (hp : list w8 * list w8) : val :=
  PairV (to_val (fst hp)) (to_val (snd hp)).

Definition is_hash_prophecy γ (p: list (list w8 * list w8)) : iProp Σ :=
  proph (hash_proph γ) (hash_pair_to_val <$> p).

Fixpoint proph_wf_filter (p: list (list w8 * list w8)) : list (list w8 * list w8) :=
  match p with
  | nil => nil
  | (data, hash) :: p' =>
    if decide ((hash_fun data) = hash) then
      (data, hash) :: proph_wf_filter p'
    else
      nil
  end.

Definition is_hash_map_inner γ : iProp Σ :=
  ∃ h p,
    is_hash_history γ h ∗
    is_hash_prophecy γ p ∗
    ⌜hash_map γ = list_to_map (h ++ (proph_wf_filter p))⌝.

Definition is_hash_model γ : iProp Σ :=
  "#Hinv" ∷ inv (hash_namespace γ) (is_hash_map_inner γ) ∗
  "%Hmwf" ∷ ⌜∀ data hash, hash_map γ !! hash = Some data -> hash = hash_fun data⌝.

(* [is_hash_map m] says that, for all of the hashes ever computed,
 * the hash value will be the key of [m] and the input value will
 * be the corresponding value in [m].
 *)
Definition is_hash_map γ (m : gmap (list w8) (list w8)) : iProp Σ :=
  "#Hmodel" ∷ is_hash_model γ ∗
  "%Hmeq" ∷ ⌜m = hash_map γ⌝.

#[global]
Instance is_hash_model_persistent γ : Persistent (is_hash_model γ).
Proof. refine _. Qed.

#[global]
Instance is_hash_map_persistent γ m : Persistent (is_hash_map γ m).
Proof. refine _. Qed.

Lemma is_hash_map_unique γ m0 m1 :
  is_hash_map γ m0 -∗ is_hash_map γ m1 -∗ ⌜m0 = m1⌝.
Proof.
  iNamedSuffix 1 "0". subst.
  iNamedSuffix 1 "1". subst.
  done.
Qed.

Lemma is_hash_model_wf γ :
  is_hash_model γ -∗
  ⌜∀ data hash, hash_map γ !! hash = Some data -> hash = hash_fun data⌝.
Proof.
  iNamed 1. done.
Qed.

(* [is_hash] says what hash computation produces [hash]: either it's
 * [Some data], in which case, [hash_fun data = hash], or [None], in
 * which case there's no other possible [is_hash] for the same [hash].
 *)
Definition is_hash γ (data : option (list w8)) (hash : list w8) : iProp Σ :=
  ∃ m,
    "#Hm" ∷ is_hash_map γ m ∗
    "%Hi" ∷ ⌜m !! hash = data⌝.

#[global]
Instance is_hash_persistent γ data hash : Persistent (is_hash γ data hash).
Proof. refine _. Qed.

Lemma is_hash_det γ data hash0 hash1 :
  is_hash γ (Some data) hash0 -∗
  is_hash γ (Some data) hash1 -∗
  ⌜ hash0 = hash1 ⌝.
Proof.
  iNamedSuffix 1 "0".
  iNamedSuffix 1 "1".
  iNamedSuffix "Hm0" "0".
  iNamedSuffix "Hm1" "1".
  subst.
  iDestruct (is_hash_model_wf with "Hmodel0") as "%Hm0".
  specialize (Hm0 _ _ Hi0).
  iDestruct (is_hash_model_wf with "Hmodel1") as "%Hm1".
  specialize (Hm1 _ _ Hi1).
  subst. done.
Qed.

(* [is_hash_inj] states that there's only one pre-image that leads
 * to [hash].  Note that here [data0] and [data1] are [option (list w8)],
 * meaning that if there's an [is_hash None hash] fact, there cannot be
 * another [is_hash (Some x) hash] fact for the same [hash].
 *)
Lemma is_hash_inj γ data0 data1 hash :
  is_hash γ data0 hash -∗
  is_hash γ data1 hash -∗
  ⌜ data0 = data1⌝.
Proof.
  iNamedSuffix 1 "0".
  iNamedSuffix 1 "1".
  iDestruct (is_hash_map_unique with "Hm0 Hm1") as "%". subst.
  iPureIntro. congruence.
Qed.

Lemma is_hash_len γ data hash :
  is_hash γ (Some data) hash -∗ ⌜ Z.of_nat (length hash) = hash_len ⌝.
Proof.
  iNamed 1.
  iNamed "Hm".
  iDestruct (is_hash_model_wf with "Hmodel") as "%Hm".
  subst.
  specialize (Hm _ _ Hi).
  subst. rewrite hash_fun_len. done.
Qed.

(* [is_hash_inv] says that, given a hash value, there's some
 * [option (list w8)] that corresponds to that hash value.
 * The [option] indicates that there's either some specific
 * [list w8] or there's no possible input that gives that hash.
 * This is the key lemma that builds on the prophecy model.
 *)
Lemma is_hash_inv γ hash :
  is_hash_model γ -∗
  ∃ data,
    is_hash γ data hash.
Proof.
  iIntros "#Hm".
  destruct (hash_map γ !! hash) as [data|] eqn:Hi.
  - iDestruct (is_hash_model_wf with "Hm") as "%Hm".
    specialize (Hm _ _ Hi).
    iFrame "#". eauto.
  - iFrame "#". eauto.
Qed.

Definition own_hasher (ptr : loc) (data : list w8) : iProp Σ :=
  ∃ sl,
    "Hhptr" ∷ ptr ↦[slice.T byteT] (slice_val sl) ∗
    "Hhsl" ∷ own_slice sl byteT (DfracOwn 1) data.

Lemma wp_NewHasher :
  {{{ True }}}
  NewHasher #()
  {{{
    ptr_hr, RET #ptr_hr;
    "Hown_hr" ∷ own_hasher ptr_hr []
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_rec.
  wp_apply wp_ref_of_zero; first by eauto.
  iIntros (ptr) "Hptr".
  rewrite zero_slice_val.
  iDestruct (own_slice_zero) as "Hsl".
  wp_pures.
  iModIntro. iApply "HΦ".
  iFrame "∗#".
Qed.

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
Proof.
  iIntros (Φ) "H HΦ".
  iNamed "H".
  iNamed "Hown_hr".
  wp_rec.
  wp_pures.
  wp_load.
  wp_apply (wp_SliceAppendSlice with "[$Hhsl $Hsl_b]"); first by eauto.
  iIntros (sl') "[Hhsl Hsl_b]".
  wp_store.
  iModIntro. iApply "HΦ".
  iFrame.
Qed.

Lemma wp_Hasher__Sum γ sl_b_in ptr_hr data b_in :
  {{{
    "Hown_hr" ∷ own_hasher ptr_hr data ∗
    "Hsl_b_in" ∷ own_slice sl_b_in byteT (DfracOwn 1) b_in ∗
    "Hhm" ∷ is_hash_model γ
  }}}
  Hasher__Sum #ptr_hr (slice_val sl_b_in)
  {{{
    sl_b_out hash, RET (slice_val sl_b_out);
    "Hown_hr" ∷ own_hasher ptr_hr data ∗
    "Hsl_b_out" ∷ own_slice sl_b_out byteT (DfracOwn 1) (b_in ++ hash) ∗
    "#His_hash" ∷ is_hash γ (Some data) hash
  }}}.
Proof.
  iIntros (Φ) "H HΦ".
  iNamed "H". iNamed "Hown_hr".
Admitted.

End proof.
