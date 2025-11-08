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

Lemma decode_empty_inj d :
  decode_chain d = DecEmpty →
  d = Some $ [].
Proof. Admitted.

Lemma decode_link_inj d prevLink val :
  decode_chain d = DecLink prevLink val →
  d = Some $ prevLink ++ val ∧
    Z.of_nat $ length prevLink = cryptoffi.hash_len.
Proof. Admitted.

Lemma decode_link_det prevLink val :
  Z.of_nat $ length prevLink = cryptoffi.hash_len →
  decode_chain (Some $ prevLink ++ val) = DecLink prevLink val.
Proof. Admitted.

(* in practice, limit should be length of list. *)
Fixpoint is_chain l (cut : option $ list w8) h limit : iProp Σ :=
  ∃ d,
  "#His_hash" ∷ cryptoffi.is_hash d h ∗
  "#Hdecode" ∷
    match decode_chain d with
    | DecEmpty =>
      "(%&%)" ∷ ⌜l = [] ∧ cut = None⌝
    | DecLink prevLink val =>
      match limit with
      | 0%nat =>
        "(%&%)" ∷ ⌜l = [] ∧ cut = Some h⌝
      | S limit' =>
        ∃ l',
        "%" ∷ ⌜l = val :: l'⌝ ∗
        "#Hrecur" ∷ is_chain l' cut prevLink limit'
      end
    | DecInvalid =>
      "(%&%)" ∷ ⌜l = [] ∧ cut = Some h⌝
    end.

Lemma is_chain_unfold l cut h limit :
  is_chain l cut h limit
  ⊣⊢
  ∃ d,
  "#His_hash" ∷ cryptoffi.is_hash d h ∗
  "#Hdecode" ∷
    match decode_chain d with
    | DecEmpty =>
      "(%&%)" ∷ ⌜l = [] ∧ cut = None⌝
    | DecLink prevLink val =>
      match limit with
      | 0%nat =>
        "(%&%)" ∷ ⌜l = [] ∧ cut = Some h⌝
      | S limit' =>
        ∃ l',
        "%" ∷ ⌜l = val :: l'⌝ ∗
        "#Hrecur" ∷ is_chain l' cut prevLink limit'
      end
    | DecInvalid =>
      "(%&%)" ∷ ⌜l = [] ∧ cut = Some h⌝
    end.
Proof. destruct limit; naive_solver. Qed.

#[global] Instance is_chain_pers l c h limit : Persistent (is_chain l c h limit).
Proof. Admitted.

Lemma is_chain_hash_len l c h limit :
  is_chain l c h limit -∗
  ⌜Z.of_nat $ length h = cryptoffi.hash_len⌝.
Proof.
  destruct limit; iNamed 1;
    by iDestruct (cryptoffi.is_hash_len with "His_hash") as %?.
Qed.

Lemma is_chain_invert h limit :
  Z.of_nat (length h) = cryptoffi.hash_len → ⊢
  ∃ l cut, is_chain l cut h limit.
Proof.
  revert h. induction limit as [? IH] using lt_wf_ind. intros.
  setoid_rewrite is_chain_unfold.
  iDestruct (cryptoffi.is_hash_invert h) as "[% $]"; [done|].
  destruct (decode_chain _) eqn:Hdec; try case_match; try naive_solver.
  apply decode_link_inj in Hdec as [-> ?].
  ospecialize (IH n _); [lia|].
  iDestruct (IH prevLink) as "(%&%&$)"; [done|].
  naive_solver.
Qed.

Lemma is_chain_inj l0 l1 cut0 cut1 h limit :
  is_chain l0 cut0 h limit -∗
  is_chain l1 cut1 h limit -∗
  ⌜l0 = l1 ∧ cut0 = cut1⌝.
Proof.
  iInduction (limit) as [? IH] using lt_wf_ind forall (l0 l1 cut0 cut1 h).
  iEval (setoid_rewrite is_chain_unfold).
  iNamedSuffix 1 "0". iNamedSuffix 1 "1".
  iDestruct (cryptoffi.is_hash_inj with "His_hash0 His_hash1") as %->.
  destruct (decode_chain _) eqn:Hdec; try case_match;
    iNamedSuffix "Hdecode0" "0"; iNamedSuffix "Hdecode1" "1";
    simplify_eq/=; try done.
  iSpecialize ("IH" $! n with "[]"); [word|].
  by iDestruct ("IH" with "Hrecur0 Hrecur1") as %[-> ->].
Qed.

Lemma is_chain_det l cut h0 h1 limit limit' :
  is_chain l cut h0 limit -∗
  is_chain l cut h1 limit' -∗
  ⌜h0 = h1⌝.
Proof.
  iInduction (limit) as [? IH] using lt_wf_ind forall (l cut h0 h1 limit').
  iEval (setoid_rewrite is_chain_unfold).
  iNamedSuffix 1 "0". iNamedSuffix 1 "1".
  destruct (decode_chain d) eqn:Hdec0;
    destruct (decode_chain d0) eqn:Hdec1;
    repeat case_match;
    iNamedSuffix "Hdecode0" "0"; iNamedSuffix "Hdecode1" "1";
    simplify_eq/=; try done.
  - apply decode_empty_inj in Hdec0.
    apply decode_empty_inj in Hdec1.
    simplify_eq/=.
    by iDestruct (cryptoffi.is_hash_det with "His_hash0 His_hash1") as %->.
  - iDestruct ("IH" $! n with "[] Hrecur0 Hrecur1") as %->; [word|].
    apply decode_link_inj in Hdec0 as [-> _].
    apply decode_link_inj in Hdec1 as [-> _].
    by iDestruct (cryptoffi.is_hash_det with "His_hash0 His_hash1") as %->.
Qed.

Lemma is_chain_cons l v cut prevLink nextLink ep :
  is_chain l cut prevLink ep -∗
  cryptoffi.is_hash (Some (prevLink ++ v)) nextLink -∗
  is_chain (v :: l) cut nextLink (S ep).
Proof.
  iIntros "#His_chain #His_hash".
  iFrame "#". fold is_chain.
  iDestruct (is_chain_hash_len with "His_chain") as %?.
  rewrite decode_link_det; [|done].
  by iFrame "#".
Qed.

Definition hash_reln l0 l1 cut0 cut1 h : iProp Σ :=
  ∃ limit0 limit1,
  "#Hc0" ∷ is_chain l0 cut0 h limit0 ∗
  "#Hc1" ∷ is_chain l1 cut1 h limit1.

Lemma hash_reln_app l0 l1 vs cut0 cut1 h h0 h1 limit0 limit1 :
  hash_reln l0 l1 cut0 cut1 h -∗
  is_chain (vs ++ l0) cut0 h0 limit0 -∗
  is_chain (vs ++ l1) cut1 h1 limit1 -∗
  ⌜h0 = h1⌝.
Proof.
  iInduction (vs) as [] forall (h0 h1 limit0 limit1);
    iIntros "@ #Hc0' #Hc1'".
  { iDestruct (is_chain_det with "Hc0 Hc0'") as %->.
    by iDestruct (is_chain_det with "Hc1 Hc1'") as %->. }
  iEval (rewrite is_chain_unfold) in "Hc0' Hc1'".
  iNamedSuffix "Hc0'" "0".
  iNamedSuffix "Hc1'" "1".
  destruct (decode_chain d) eqn:Hdec0;
    destruct (decode_chain d0) eqn:Hdec1;
    repeat case_match;
    iNamedSuffix "Hdecode0" "0";
    iNamedSuffix "Hdecode1" "1";
    try done.
  simplify_eq/=.
  iDestruct ("IHvs" with "[] Hrecur0 Hrecur1") as %->.
  { iFrame "#". }
  apply decode_link_inj in Hdec0 as [-> _].
  apply decode_link_inj in Hdec1 as [-> _].
  by iDestruct (cryptoffi.is_hash_det with "His_hash0 His_hash1") as %->.
Qed.

Lemma wp_GetEmptyLink :
  {{{ is_pkg_init hashchain }}}
  @! hashchain.GetEmptyLink #()
  {{{
    sl h, RET #sl;
    "Hsl_hash" ∷ sl ↦* h ∗
    "#His_chain" ∷ is_chain [] None h 0%nat
  }}}.
Proof.
  wp_start.
  wp_apply (cryptoutil.wp_Hash _ inhabitant) as "* @".
  { iApply own_slice_nil. }
  iApply "HΦ".
  by iFrame "∗#".
Qed.

Lemma wp_GetNextLink sl_prevLink d0 prevLink sl_nextVal d1 nextVal l cut ep :
  {{{
    is_pkg_init hashchain ∗
    "Hsl_prevLink" ∷ sl_prevLink ↦*{d0} prevLink ∗
    "Hsl_nextVal" ∷ sl_nextVal ↦*{d1} nextVal ∗
    "#His_chain" ∷ is_chain l cut prevLink ep
  }}}
  @! hashchain.GetNextLink #sl_prevLink #sl_nextVal
  {{{
    sl_nextLink nextLink, RET #sl_nextLink;
    "Hsl_prevLink" ∷ sl_prevLink ↦*{d0} prevLink ∗
    "Hsl_nextVal" ∷ sl_nextVal ↦*{d1} nextVal ∗
    "Hsl_nextLink" ∷ sl_nextLink ↦* nextLink ∗
    "#His_chain" ∷ is_chain (nextVal :: l) cut nextLink (S ep)
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
  iDestruct (is_chain_cons with "His_chain His_hash") as "$".
  iFrame.
Qed.

Definition wish_Verify (prevLink proof : list w8) (extLen : w64) (newVal newLink : list w8) : iProp Σ :=
  ∃ old_vals new_vals cut old_ep new_ep,
  "%Hsame_len_vals" ∷ ⌜Forall (λ x, length x = Z.to_nat cryptoffi.hash_len) new_vals⌝ ∗
  "%Henc_vals" ∷ ⌜proof = mjoin new_vals⌝ ∗
  "%HnewVal" ∷ ⌜newVal = default [] (last new_vals)⌝ ∗
  "%HextLen" ∷ ⌜uint.Z extLen = length new_vals⌝ ∗
  "#His_prevLink" ∷ is_chain old_vals cut prevLink old_ep ∗
  "#His_newLink" ∷ is_chain (new_vals ++ old_vals) cut newLink new_ep.
#[global] Opaque wish_Verify.
#[local] Transparent wish_Verify.

Lemma wish_Verify_det prevLink proof extLen0 extLen1 newVal0 newVal1 newLink0 newLink1 :
  wish_Verify prevLink proof extLen0 newVal0 newLink0 -∗
  wish_Verify prevLink proof extLen1 newVal1 newLink1 -∗
  ⌜extLen0 = extLen1 ∧ newVal0 = newVal1 ∧ newLink0 = newLink1⌝.
Proof.
  iNamedSuffix 1 "0".
  iNamedSuffix 1 "1".
  subst.
  opose proof (join_same_len_inj _ _ _ _ _ _ ltac:(done)) as ->;
    [|done..|]; [word|].
  replace extLen0 with extLen1 by word.
  repeat iSplit; [done..|].
  clear.
  iDestruct (hash_reln_app with "[] His_newLink0 His_newLink1") as %->.
  { iFrame "#". }
  done.
Qed.

End proof.
End hashchain.
