From New.generatedproof.github_com.sanjit_bhat.pav Require Import hashchain.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

From New.proof Require Import bytes.
From New.proof.github_com.goose_lang Require Import std.
From New.proof.github_com.sanjit_bhat.pav Require Import cryptoffi cryptoutil.

Module hashchain.
Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit hashchain := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf hashchain := build_get_is_pkg_init_wf.

(** impl / spec requirements for hashchain:
- allow for "bootstrapping", where a user starts following the hashchain
only after some epoch.
- injective lemma. if two hashchains have the same hash,
they commit to the same underlying values.
- optional correctness between Prover and Verifier.

observations:
- correctness requires the Verifier spec to determ give a new link.
- with two bootstrapped users, injectivity becomes annoying to state.
(e.g., the two hashchains are suffixes of each other.)
if you add in hash inversion, it reduces to simple equality.

observations on hash inversion:
- to invert, the predicate needs to cover all possible decoding states.
it's easiest to do that by having the predicate match on the decoding. *)

Inductive dec_chain :=
  | DecEmpty
  | DecLink (prevLink val : list w8)
  | DecInvalid.

Definition decode_link data : option (list w8 * list w8) :=
  let rem0 := data in
  match bool_decide (Z.of_nat $ length rem0 >= cryptoffi.hash_len) with
  | false => None
  | _ =>
    let prevLink := take (Z.to_nat cryptoffi.hash_len) rem0 in
    let val := drop (Z.to_nat cryptoffi.hash_len) rem0 in
    Some (prevLink, val)
  end.

Definition decode_chain data :=
  match data with
  | None => DecInvalid
  | Some d =>
    match d with
    | [] => DecEmpty
    | _ =>
      match decode_link d with
      | None => DecInvalid
      | Some x => DecLink x.1 x.2
      end
    end
  end.

(* in practice, limit should be length of list. *)
Fixpoint is_chain l h limit : iProp Σ :=
  ∃ d,
  "#His_hash" ∷ cryptoffi.is_hash d h ∗
  "#Hdecode" ∷
    match decode_chain d with
    | DecEmpty =>
      "%" ∷ ⌜l = []⌝
    | DecLink prevLink val =>
      match limit with
      | 0%nat =>
        "%" ∷ ⌜l = []⌝
      | S limit' =>
        ∃ l',
        "%" ∷ ⌜l = l' ++ [val]⌝ ∗
        "#Hrecur" ∷ is_chain l' prevLink limit'
      end
    | DecInvalid =>
      (* TODO: what object should represent invalid hash?
      do we need a list that terminates in a Cut?
      might need this if we want determ obj -> hash. *)
      "%" ∷ ⌜l = []⌝
    end.
(* #[global] Arguments is_chain !_. *)

Lemma is_chain_unfold l h limit :
  is_chain l h limit
  ⊣⊢
  ∃ d,
  "#His_hash" ∷ cryptoffi.is_hash d h ∗
  "#Hdecode" ∷
    match decode_chain d with
    | DecEmpty =>
      "%" ∷ ⌜l = []⌝
    | DecLink prevLink val =>
      match limit with
      | 0%nat =>
        "%" ∷ ⌜l = []⌝
      | S limit' =>
        ∃ l',
        "%" ∷ ⌜l = l' ++ [val]⌝ ∗
        "#Hrecur" ∷ is_chain l' prevLink limit'
      end
    | DecInvalid =>
      "%" ∷ ⌜l = []⌝
    end.
Proof. destruct limit; naive_solver. Qed.

#[global] Instance is_chain_pers l h limit : Persistent (is_chain l h limit).
Proof. Admitted.

Lemma is_chain_hash_len l h limit :
  is_chain l h limit -∗
  ⌜Z.of_nat $ length h = cryptoffi.hash_len⌝.
Proof.
  destruct limit; iNamed 1;
    by iDestruct (cryptoffi.is_hash_len with "His_hash") as %?.
Qed.

Lemma decode_link_inj d prevLink val :
  decode_chain d = DecLink prevLink val →
  d = Some $ prevLink ++ val ∧
    Z.of_nat $ length prevLink = cryptoffi.hash_len.
Proof. Admitted.

Lemma decode_link_det prevLink val :
  Z.of_nat $ length prevLink = cryptoffi.hash_len →
  decode_chain (Some $ prevLink ++ val) = DecLink prevLink val.
Proof. Admitted.

Lemma is_chain_invert h limit :
  Z.of_nat (length h) = cryptoffi.hash_len → ⊢
  ∃ l, is_chain l h limit.
Proof.
  revert h. induction limit as [? IH] using lt_wf_ind. intros.
  setoid_rewrite is_chain_unfold.
  iDestruct (cryptoffi.is_hash_invert h) as "[% $]"; [done|].
  repeat case_match; try naive_solver.
  opose proof (decode_link_inj _ _ _ _) as (_&?); [done|].
  ospecialize (IH n _); [lia|].
  iDestruct (IH prevLink) as "[% $]"; [done|].
  naive_solver.
Qed.

Lemma is_chain_inj l0 l1 h limit :
  is_chain l0 h limit -∗
  is_chain l1 h limit -∗
  ⌜l0 = l1⌝.
Proof.
  iInduction (limit) as [? IH] using lt_wf_ind forall (l0 l1 h);
    iEval (setoid_rewrite is_chain_unfold);
    iNamedSuffix 1 "0"; iNamedSuffix 1 "1";
    iDestruct (cryptoffi.is_hash_inj with "His_hash0 His_hash1") as %->;
    repeat case_match;
    iNamedSuffix "Hdecode0" "0"; iNamedSuffix "Hdecode1" "1";
    simplify_eq/=; try done.
  iSpecialize ("IH" $! n with "[]"); [word|].
  by iDestruct ("IH" with "Hrecur0 Hrecur1") as %->.
Qed.

Lemma is_chain_snoc l v prevLink nextLink ep :
  is_chain l prevLink ep -∗
  cryptoffi.is_hash (Some (prevLink ++ v)) nextLink -∗
  is_chain (l ++ [v]) nextLink (S ep).
Proof.
  iIntros "#His_chain #His_hash".
  iFrame "#". fold is_chain.
  iDestruct (is_chain_hash_len with "His_chain") as %?.
  rewrite decode_link_det; [|done].
  by iFrame "#".
Qed.

Lemma wp_GetEmptyLink :
  {{{ is_pkg_init hashchain }}}
  @! hashchain.GetEmptyLink #()
  {{{
    sl h, RET #sl;
    "Hsl_hash" ∷ sl ↦* h ∗
    "#His_chain" ∷ is_chain [] h 0%nat
  }}}.
Proof.
  wp_start.
  wp_apply (cryptoutil.wp_Hash _ inhabitant) as "* @".
  { iApply own_slice_nil. }
  iApply "HΦ".
  by iFrame "∗#".
Qed.

Lemma wp_GetNextLink sl_prevLink d0 prevLink sl_nextVal d1 nextVal l ep :
  {{{
    is_pkg_init hashchain ∗
    "Hsl_prevLink" ∷ sl_prevLink ↦*{d0} prevLink ∗
    "Hsl_nextVal" ∷ sl_nextVal ↦*{d1} nextVal ∗
    "#His_chain" ∷ is_chain l prevLink ep
  }}}
  @! hashchain.GetNextLink #sl_prevLink #sl_nextVal
  {{{
    sl_nextLink nextLink, RET #sl_nextLink;
    "Hsl_prevLink" ∷ sl_prevLink ↦*{d0} prevLink ∗
    "Hsl_nextVal" ∷ sl_nextVal ↦*{d1} nextVal ∗
    "Hsl_nextLink" ∷ sl_nextLink ↦* nextLink ∗
    "#His_chain" ∷ is_chain (l ++ [nextVal]) nextLink (S ep)
  }}}.
Proof.
  wp_start. iNamed "Hpre".
  wp_auto.
  wp_apply cryptoffi.wp_NewHasher as "* @".
  wp_apply (cryptoffi.wp_Hasher_Write with "[$Hown_hr $Hsl_prevLink]").
  iNamedSuffix 1 "0". wp_auto.
  wp_apply (cryptoffi.wp_Hasher_Write with "[$Hown_hr0 $Hsl_nextVal]").
  iNamedSuffix 1 "1". wp_auto.
  wp_apply (cryptoffi.wp_Hasher_Sum with "[$Hown_hr1]").
  { iApply own_slice_nil. }
  iIntros "*". iNamed 1.
  wp_auto.
  iApply "HΦ".
  iDestruct (is_chain_snoc with "His_chain His_hash") as "$".
  iFrame.
Qed.

Definition foo l v prev next : iProp Σ :=
  ∃ ep,
  is_chain l prev ep ∗
  is_chain (l ++ [v]) next (S ep).

Lemma foo_det l v prev next0 next1 :
  foo l v prev next0 -∗
  foo l v prev next1 -∗
  ⌜next0 = next1⌝.
Proof.
  iIntros "(%&#Hp0&#Hn0)(%&#Hp1&#Hn1)".
  iNamedSuffix "Hn0" "0".
  iNamedSuffix "Hn1" "1".
  fold is_chain.
  repeat case_match;
    iNamedSuffix "Hdecode0" "0";
    iNamedSuffix "Hdecode1" "1";
    try discriminate_list.

  rewrite H1 in H2.
  list_simplifier.
  (* need: for same list and limit, same link.
  but this not true bc invalid hash not pinned down! *)
Abort.

(* TODO: tie prevLink with newLink. *)
Definition wish_Verify (prevLink proof : list w8) (extLen : w64) (newVal newLink : list w8) : iProp Σ :=
  ∃ new_vals,
  "%Hsame_len_vals" ∷ ⌜Forall (λ x, Z.of_nat (length x) = cryptoffi.hash_len) new_vals⌝ ∗
  "%Henc_vals" ∷ ⌜proof = mjoin new_vals⌝ ∗
  "%HnewVal" ∷ ⌜newVal = default [] (last new_vals)⌝ ∗
  "%HextLen" ∷ ⌜uint.Z extLen = length new_vals⌝.
#[global] Opaque wish_Verify.
#[local] Transparent wish_Verify.

(* need [wish_Verify_det] for correctness.
to determ tie prevLink to newLink:
1) is_chain vals prevLink _. is_chain (vals ++ new_vals) newLink _.
and is_chain det property (see [foo_det]).
2) literally say that newLink is the chained hash from prevLink.
this is basically reverting to our old is_chain. *)
Lemma wish_Verify_det pL p e0 e1 nV0 nV1 nL0 nL1 :
  wish_Verify pL p e0 nV0 nL0 -∗
  wish_Verify pL p e1 nV1 nL1 -∗
  ⌜e0 = e1 ∧ nV0 = nV1 ∧ nL0 = nL1⌝.
Proof. Abort.

End proof.
End hashchain.
