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
- injective lemma for security. if two hashchains have the same hash,
they commit to the same underlying values.
- optional correctness between Prover and Verifier.
Verify determ generates [newLink] from [prevLink] and [proof].

observations:
- with two bootstrapped users, injectivity becomes annoying to state.
(e.g., that two hashchains are suffixes of each other.)
if you add in hash inversion, it reduces to simple equality.

observations on hash inversion:
- to invert, the hashchain predicate needs to cover all possible decoding states.
it's easiest to do that if the predicate matches on the decoding.
i.e., normal representation predicates go from obj -> ptr (hash).
for inversion, we go from ptr -> obj.
- it's hard to have an inductive inversion proof without [limit].
there's nothing else to induct on! *)

Inductive dec_chain :=
  | DecEmpty
  | DecLink (prevLink val : list w8)
  | DecInvalid.

Local Definition decode_link data : option (list w8 * list w8) :=
  let rem0 := data in
  match bool_decide (Z.of_nat $ length rem0 >= cryptoffi.hash_len) with
  | false => None
  | _ =>
    let prevLink := take (Z.to_nat cryptoffi.hash_len) rem0 in
    let val := drop (Z.to_nat cryptoffi.hash_len) rem0 in
    Some (prevLink, val)
  end.

Local Definition decode_chain data :=
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

Local Lemma decode_empty_inj d :
  decode_chain d = DecEmpty →
  d = Some $ [].
Proof.
  rewrite /decode_chain. intros.
  case_match; [|done].
  case_match; [done|].
  by case_match.
Qed.

Local Lemma decode_link_inj_aux d x :
  decode_link d = Some x →
  d = x.1 ++ x.2 ∧
    Z.of_nat $ length x.1 = cryptoffi.hash_len.
Proof.
  rewrite /decode_link. intros.
  case_bool_decide; [|done].
  simplify_eq/=.
  remember d as rem0.

  rewrite take_drop.
  split; [done|len].
Qed.

Lemma decode_link_inj d prevLink val :
  decode_chain d = DecLink prevLink val →
  d = Some $ prevLink ++ val ∧
    Z.of_nat $ length prevLink = cryptoffi.hash_len.
Proof.
  rewrite /decode_chain. intros.
  case_match; [|done].
  case_match; [done|].
  case_match; [|done].
  opose proof (decode_link_inj_aux _ _ _) as [Heq ?]; [done|].
  rewrite Heq.
  by simplify_eq/=.
Qed.

Local Lemma decode_link_det_aux prevLink val :
  Z.of_nat $ length prevLink = cryptoffi.hash_len →
  decode_link (prevLink ++ val) = Some (prevLink, val).
Proof.
  intros. rewrite /decode_link.
  case_bool_decide.
  2: { autorewrite with len in *. word. }
  rewrite take_app_length'; [|word].
  rewrite drop_app_length'; [|word].
  done.
Qed.

Local Lemma decode_link_det prevLink val :
  Z.of_nat $ length prevLink = cryptoffi.hash_len →
  decode_chain (Some $ prevLink ++ val) = DecLink prevLink val.
Proof.
  intros. simpl.
  case_match eqn:Heq.
  { apply (f_equal length) in Heq.
    autorewrite with len in *. word. }
  rewrite -{}Heq.
  by rewrite decode_link_det_aux.
Qed.

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
        "%" ∷ ⌜l = l' ++ [val]⌝ ∗
        "#Hrecur" ∷ is_chain l' cut prevLink limit'
      end
    | DecInvalid =>
      "(%&%)" ∷ ⌜l = [] ∧ cut = Some h⌝
    end.
#[global] Opaque is_chain.
#[local] Transparent is_chain.

Local Lemma is_chain_unfold l cut h limit :
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
        "%" ∷ ⌜l = l' ++ [val]⌝ ∗
        "#Hrecur" ∷ is_chain l' cut prevLink limit'
      end
    | DecInvalid =>
      "(%&%)" ∷ ⌜l = [] ∧ cut = Some h⌝
    end.
Proof. destruct limit; naive_solver. Qed.

#[global] Instance is_chain_pers l c h limit : Persistent (is_chain l c h limit).
Proof.
  revert l h. induction limit as [? IH] using lt_wf_ind. intros.
  setoid_rewrite is_chain_unfold.
  apply exist_persistent. intros.
  repeat case_match; try apply _.
  ospecialize (IH n _); [lia|].
  apply _.
Qed.

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

(* [is_chain_det] is used in correctness proofs to go from
lists equal to hashes equal.
proving [is_chain_det] requires the Cut hash to be visible.
hashchains are over lists, so unlike merkle trees, there's only one place
(the list bottom) where Cuts can show up.
using that observation, we make Cut an [is_chain] arg,
so that we can use a normal list for the remaining object. *)
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
    simplify_eq/=; try done; try discriminate_list.
  - apply decode_empty_inj in Hdec0.
    apply decode_empty_inj in Hdec1.
    simplify_eq/=.
    by iDestruct (cryptoffi.is_hash_det with "His_hash0 His_hash1") as %->.
  - list_simplifier.
    iDestruct ("IH" $! n with "[] Hrecur0 Hrecur1") as %->; [word|].
    apply decode_link_inj in Hdec0 as [-> _].
    apply decode_link_inj in Hdec1 as [-> _].
    by iDestruct (cryptoffi.is_hash_det with "His_hash0 His_hash1") as %->.
Qed.

Local Lemma is_chain_snoc l v cut prevLink nextLink len :
  is_chain l cut prevLink len -∗
  cryptoffi.is_hash (Some (prevLink ++ v)) nextLink -∗
  is_chain (l ++ [v]) cut nextLink (S len).
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
    "#His_chain" ∷ is_chain [] None h 0%nat
  }}}.
Proof.
  wp_start.
  wp_apply (cryptoutil.wp_Hash _ inhabitant) as "* @".
  { iApply own_slice_nil. }
  iApply "HΦ".
  by iFrame "∗#".
Qed.

Lemma wp_GetNextLink sl_prevLink d0 prevLink sl_nextVal d1 nextVal l cut len :
  {{{
    is_pkg_init hashchain ∗
    "Hsl_prevLink" ∷ sl_prevLink ↦*{d0} prevLink ∗
    "Hsl_nextVal" ∷ sl_nextVal ↦*{d1} nextVal ∗
    "#His_chain" ∷ is_chain l cut prevLink len
  }}}
  @! hashchain.GetNextLink #sl_prevLink #sl_nextVal
  {{{
    sl_nextLink nextLink, RET #sl_nextLink;
    "Hsl_prevLink" ∷ sl_prevLink ↦*{d0} prevLink ∗
    "Hsl_nextVal" ∷ sl_nextVal ↦*{d1} nextVal ∗
    "Hsl_nextLink" ∷ sl_nextLink ↦* nextLink ∗
    "#His_chain" ∷ is_chain (l ++ [nextVal]) cut nextLink (S len)
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

Definition own (ptr : loc) (vals : list $ list w8) (d : dfrac) : iProp Σ :=
  ∃ sl_predLastLink predLastLink sl_lastLink lastLink sl_enc enc,
  "Hstruct" ∷ ptr ↦{d} (hashchain.HashChain.mk sl_predLastLink sl_lastLink sl_enc) ∗

  "#Hsl_predLastLink" ∷ sl_predLastLink ↦*□ predLastLink ∗
  "#His_chain_pred" ∷ (∀ x vals',
    ⌜vals = vals' ++ [x]⌝ -∗
    is_chain vals' None predLastLink (length vals')) ∗

  "#Hsl_lastLink" ∷ sl_lastLink ↦*□ lastLink ∗
  "#His_chain" ∷ is_chain vals None lastLink (length vals) ∗

  "Hsl_enc" ∷ sl_enc ↦*{d} enc ∗
  "Hsl_enc_cap" ∷ own_slice_cap w8 sl_enc d ∗
  "%" ∷ ⌜enc = mjoin vals⌝ ∗
  "%Hsame_len" ∷ ⌜Forall (λ x, length x = Z.to_nat cryptoffi.hash_len) vals⌝.
#[global] Opaque own.
#[local] Transparent own.

#[global] Instance own_dfractional ptr vs :
  DFractional (λ d, own ptr vs d).
Proof.
  rewrite /own. split.
  - intros ??. iSplit.
    + iNamed 1.
      iDestruct "Hstruct" as "[? ?]".
      iDestruct "Hsl_enc" as "[? ?]".
      iDestruct "Hsl_enc_cap" as "[? ?]".
      by iFrame "∗#".
    + iIntros "[H0 H1]".
      iNamedSuffix "H0" "0".
      iNamedSuffix "H1" "1".
      iCombine "Hstruct0 Hstruct1" as "Hstruct" gives %[_ ?].
      simplify_eq/=.
      iCombine "Hsl_enc0 Hsl_enc1" as "Hsl_enc".
      iCombine "Hsl_enc_cap0 Hsl_enc_cap1" as "Hsl_enc_cap".
      by iFrame "∗#".
  - apply _.
  - intros ?. iNamed 1.
    iPersist "Hstruct Hsl_enc Hsl_enc_cap".
    iModIntro. by iFrame "Hstruct #".
Qed.

Lemma wp_New :
  {{{ is_pkg_init hashchain }}}
  @! hashchain.New #()
  {{{ ptr, RET #ptr; "Hown_HashChain" ∷ own ptr [] 1 }}}.
Proof.
  wp_start.
  wp_apply wp_GetEmptyLink as "* @".
  iPersist "Hsl_hash".
  wp_apply wp_alloc as "* H0".
  iApply "HΦ".
  iFrame "∗#".
  iDestruct own_slice_nil as "$".
  iDestruct own_slice_nil as "$".
  iDestruct own_slice_cap_nil as "$".
  iSplit; [|done].
  iIntros (???).
  discriminate_list.
Qed.

Lemma wp_HashChain_Append ptr_c vals sl_val d0 val :
  {{{
    is_pkg_init hashchain ∗
    "Hown_HashChain" ∷ own ptr_c vals 1 ∗
    "Hsl_val" ∷ sl_val ↦*{d0} val ∗
    "%Hlen_val" ∷ ⌜Z.of_nat $ length val = cryptoffi.hash_len⌝
  }}}
  ptr_c @ (ptrT.id hashchain.HashChain.id) @ "Append" #sl_val
  {{{
    sl_newLink newLink, RET #sl_newLink;
    "Hown_HashChain" ∷ own ptr_c (vals ++ [val]) 1 ∗
    "Hsl_val" ∷ sl_val ↦*{d0} val ∗
    "#Hsl_newLink" ∷ sl_newLink ↦*□ newLink ∗
    "#His_chain" ∷ is_chain (vals ++ [val]) None newLink (S $ length vals)
  }}}.
Proof.
  wp_start. iNamed "Hpre". iNamed "Hown_HashChain".
  wp_auto.
  iDestruct (own_slice_len with "Hsl_val") as %?.
  wp_apply wp_Assert.
  { iPureIntro. apply bool_decide_eq_true. word. }
  wp_apply (wp_GetNextLink with "[Hsl_val]").
  { iFrame "∗#". }
  iIntros "*". iNamedSuffix 1 "_n".
  iPersist "Hsl_prevLink_n Hsl_nextLink_n".
  wp_auto.
  wp_apply (wp_slice_append with "[$Hsl_enc $Hsl_enc_cap $Hsl_nextVal_n]")
    as "* (Hsl_enc & Hsl_enc_cap & Hsl_nextVal_n)".
  iApply "HΦ".
  iFrame "∗#".
  repeat iSplit.
  - iIntros (?? Heq).
    apply app_inj_tail in Heq as [-> ->].
    iFrame "#".
  - iExactEq "His_chain_n". rewrite /named. repeat f_equal. len.
  - iPureIntro. subst. rewrite join_app. by list_simplifier.
  - iPureIntro. apply Forall_snoc. split; [done|word].
Qed.

(* unlike most other pav wishes, [wish_Proof] doesn't tie down all
inputs and outputs of [hashchain.Verify].
it only says that [proof] deterministically decodes to [new_vals].
the remaining input is [prevLink].
it's not referenced because it's client-tracked.
the outputs ([extLen], [newVal], [newLink]) aren't referenced
because they deterministically derive from [prevLink] and [new_vals]. *)
Definition wish_Proof (proof : list w8) new_vals :=
  Forall (λ x, length x = Z.to_nat cryptoffi.hash_len) new_vals ∧
  proof = mjoin new_vals.
#[global] Opaque wish_Proof.
#[local] Transparent wish_Proof.

Lemma wish_Proof_det proof new_vals0 new_vals1 :
  wish_Proof proof new_vals0 →
  wish_Proof proof new_vals1 →
  new_vals0 = new_vals1.
Proof.
  intros (?&?) (?&?).
  subst.
  opose proof (join_same_len_inj _ _ _ _ _ _ ltac:(done)) as ->; [|done..].
  word.
Qed.

Lemma wp_Verify sl_prevLink d0 prevLink sl_proof d1 proof old_vals cut len :
  {{{
    is_pkg_init hashchain ∗
    "Hsl_prevLink" ∷ sl_prevLink ↦*{d0} prevLink ∗
    "Hsl_proof" ∷ sl_proof ↦*{d1} proof ∗
    "#His_chain" ∷ is_chain old_vals cut prevLink len
  }}}
  @! hashchain.Verify #sl_prevLink #sl_proof
  {{{
    (extLen : w64) sl_newVal newVal sl_newLink newLink err,
    RET (#extLen, #sl_newVal, #sl_newLink, #err);
    "Hsl_newVal" ∷ sl_newVal ↦*{d1} newVal ∗
    "Hsl_newLink" ∷ sl_newLink ↦*{d0} newLink ∗
    "Hgenie" ∷
      match err with
      | true => ¬ ∃ new_vals, ⌜wish_Proof proof new_vals⌝
      | false =>
        ∃ new_vals,
        "%Hwish_chain" ∷ ⌜wish_Proof proof new_vals⌝ ∗
        "%HextLen" ∷ ⌜uint.Z extLen = length new_vals⌝ ∗
        "%HnewVal" ∷ ⌜newVal = default [] (last new_vals)⌝ ∗
        "#His_chain" ∷ is_chain (old_vals ++ new_vals) cut newLink (len + (length new_vals))
      end
  }}}.
Proof.
  wp_start. iNamed "Hpre".
  wp_auto.
  iDestruct (is_chain_hash_len with "His_chain") as %?.
  iDestruct (own_slice_valid with "Hsl_prevLink") as %Ht.
  { by rewrite go_type_size_unseal. }
  destruct Ht as [|Ht].
  2: { apply (f_equal length) in Ht. simpl in *. word. }
  iDestruct (own_slice_len with "Hsl_proof") as %[? ?].

  wp_if_destruct.
  2: {
    iApply "HΦ".
    iDestruct own_slice_nil as "$".
    iDestruct own_slice_nil as "$".
    iFrame.
    iIntros ((?&Hsame_len&?)).
    apply join_same_len_length in Hsame_len.
    word. }
  iPersist "extLen".
  remember (word.divu _ _) as extLen.

  iAssert (
    ∃ (i : w64) sl_proof sl_newLink newLink sl_newVal newVal new_vals,
    "i" ∷ i_ptr ↦ i ∗
    "%Hlt_i" ∷ ⌜uint.Z i ≤ uint.Z extLen⌝ ∗

    "proof" ∷ proof_ptr ↦ sl_proof ∗
    "newVal" ∷ newVal_ptr ↦ sl_newVal ∗
    "newLink" ∷ newLink_ptr ↦ sl_newLink ∗

    "Hsl_proof" ∷ sl_proof ↦*{d1} drop (Z.to_nat (uint.Z i * cryptoffi.hash_len)) proof ∗
    "Hsl_newVal" ∷ sl_newVal ↦*{d1} newVal ∗
    "Hsl_newLink" ∷ sl_newLink ↦*{d0} newLink ∗

    "(%Hsame_len&%Henc)" ∷ ⌜wish_Proof
      (take (Z.to_nat (uint.Z i * cryptoffi.hash_len)) proof)
      new_vals⌝ ∗
    "%" ∷ ⌜length new_vals = uint.nat i⌝ ∗
    "->" ∷ ⌜newVal = default [] (last new_vals)⌝ ∗
    "#His_chain" ∷ is_chain (old_vals ++ new_vals) cut newLink (len + (length new_vals))
  )%I with "[$i $newLink $newVal $proof Hsl_prevLink Hsl_proof]" as "IH".
  { iDestruct own_slice_nil as "?".
    iFrame "∗#".
    iExists [].
    list_simplifier.
    ereplace (?[x] + 0)%nat with (?x) by lia.
    iFrame "#".
    rewrite take_0'; [|word].
    repeat iSplit; try done.
    word. }
  iClear "His_chain".
  wp_for "IH".
  case_bool_decide.

  2: {
    wp_auto.
    rewrite take_ge in Henc; [|word].
    iApply "HΦ".
    replace i with extLen in * by word.
    iFrame "∗#".
    repeat iSplit; try done.
    word. }

  rewrite -wp_fupd.
  iRename "Hsl_newVal" into "Hsl_newVal_old".
  wp_auto.
  iDestruct (own_slice_wf with "Hsl_proof") as %?.
  iDestruct (own_slice_len with "Hsl_proof") as %[Hlen_proof ?].
  rewrite length_drop in Hlen_proof.
  wp_apply (wp_slice_slice with "[$Hsl_proof]"); [word|].
  iIntros "(_&Hsl_newVal&Hsl_proof)".
  wp_auto.
  wp_pure; [word|].
  wp_auto.
  wp_apply (wp_GetNextLink with "[$Hsl_newLink $Hsl_newVal $His_chain]") as "{His_chain} * @".
  iMod (own_slice_update_to_dfrac d0 with "Hsl_nextLink") as "Hsl_nextLink"; [done|].
  iModIntro.
  wp_for_post.
  iFrame "newLink ∗".

  iEval (rewrite drop_drop) in "Hsl_proof".
  replace (uint.Z (word.add _ _)) with (uint.Z i + 1) by word.
  replace (Z.to_nat (uint.Z i * cryptoffi.hash_len) + sint.nat (W64 32))%nat
    with (Z.to_nat ((uint.Z i + 1) * cryptoffi.hash_len))%nat by word.
  iFrame "Hsl_proof".

  rewrite subslice_from_start.
  Opaque is_chain.
  list_simplifier.
  iExists _. repeat iSplit; try iPureIntro.
  6: { iExactEq "His_chain". rewrite /named. repeat f_equal. len. }
  - word.
  - apply Forall_snoc. split; [done|len].
  - rewrite join_app.
    rewrite (take_subslice (Z.to_nat (uint.Z i * cryptoffi.hash_len))); [|word].
    f_equal; [done|].
    rewrite subslice_take_drop'.
    list_simplifier.
    repeat f_equal. word.
  - len.
  - rewrite last_snoc /=. f_equal; word.
Qed.

Lemma wp_HashChain_Prove c vals d (prevLen : w64) :
  {{{
    is_pkg_init hashchain ∗
    "Hown_HashChain" ∷ own c vals d ∗
    "%Hlt_prevLen" ∷ ⌜uint.Z prevLen <= length vals⌝
  }}}
  c @ (ptrT.id hashchain.HashChain.id) @ "Prove" #prevLen
  {{{
    sl_proof proof, RET #sl_proof;
    let new_vals := drop (uint.nat prevLen) vals in
    "Hown_HashChain" ∷ own c vals d ∗
    "Hsl_proof" ∷ sl_proof ↦* proof ∗

    "%Hwish" ∷ ⌜wish_Proof proof new_vals⌝
  }}}.
Proof.
  wp_start. iNamed "Hpre". iNamed "Hown_HashChain".
  wp_auto.
  iDestruct (own_slice_len with "Hsl_enc") as %?.
  apply join_same_len_length in Hsame_len as ?.
  wp_apply (wp_slice_slice with "[$Hsl_enc]") as "(Hsl0 & Hsl1 & Hsl2)"; [word|].
  wp_apply (bytes.wp_Clone with "[$Hsl1]") as "* @".
  iDestruct (own_slice_f with "[$Hsl0 $Hsl_b $Hsl2]") as "?"; [word|].

  iApply "HΦ".
  iFrame "∗#%".
  iPureIntro. split.
  { by apply Forall_drop. }
  subst.
  opose proof (join_same_len_subslice (uint.nat prevLen) (length vals)
    (Z.to_nat cryptoffi.hash_len) vals ltac:(word) Hsame_len) as Heq.
  rewrite subslice_to_end in Heq; [|done].
  rewrite Heq.
  f_equal; word.
Qed.

Lemma wp_HashChain_Bootstrap c vals d old_vals last_val :
  {{{
    is_pkg_init hashchain ∗
    "Hown_HashChain" ∷ own c vals d ∗
    "->" ∷ ⌜vals = old_vals ++ [last_val]⌝
  }}}
  c @ (ptrT.id hashchain.HashChain.id) @ "Bootstrap" #()
  {{{
    sl_bootLink bootLink sl_proof proof, RET (#sl_bootLink, #sl_proof);
    "Hown_HashChain" ∷ own c vals d ∗
    "#Hsl_bootLink" ∷ sl_bootLink ↦*□ bootLink ∗
    "Hsl_proof" ∷ sl_proof ↦* proof ∗

    "#His_bootLink" ∷ is_chain old_vals None bootLink (length old_vals) ∗
    "%Hwish" ∷ ⌜wish_Proof proof [last_val]⌝
  }}}.
Proof.
  wp_start. iNamed "Hpre". iNamed "Hown_HashChain". wp_auto.
  iDestruct (own_slice_len with "Hsl_enc") as %?.
  apply join_same_len_length in Hsame_len as Hlen.
  rewrite app_length /= in Hlen.
  wp_apply (wp_slice_slice with "[$Hsl_enc]") as "(Hsl0 & Hsl1 & Hsl2)"; [word|].
  wp_apply (bytes.wp_Clone with "[$Hsl1]") as "* @".
  iDestruct (own_slice_f with "[$Hsl0 $Hsl_b $Hsl2]") as "?"; [word|].

  iApply "HΦ".
  iDestruct ("His_chain_pred" with "[//]") as "?".
  iFrame "∗#%".
  iPureIntro. split.
  - apply Forall_snoc in Hsame_len as [??].
    by rewrite Forall_singleton.
  - replace (sint.nat (word.sub _ _)) with
      ((length old_vals + 0) * (Z.to_nat cryptoffi.hash_len))%nat by word.
    replace (sint.nat _) with
      ((length old_vals + 1) * (Z.to_nat cryptoffi.hash_len))%nat by word.
    subst.
    rewrite -join_same_len_subslice; [|len|done].
    rewrite subslice_app_length.
    by list_simplifier.
Qed.

End proof.
End hashchain.
