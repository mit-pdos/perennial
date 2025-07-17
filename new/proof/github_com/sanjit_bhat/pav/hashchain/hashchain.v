From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From Perennial Require Import base.
From New.generatedproof.github_com.sanjit_bhat.pav Require Import hashchain.
From Perennial.Helpers Require Import NamedProps.

From New.proof.github_com.sanjit_bhat.pav Require Import cryptoffi cryptoutil.
From New.proof.github_com.goose_lang Require Import std.
From New.proof Require Import bytes.

Module hashchain.
Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !goGlobalsGS Σ}.

#[global]
Program Instance is_pkg_init_hashchain : IsPkgInit hashchain := ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_hashchain.
#[local] Transparent is_pkg_init_hashchain.

Local Fixpoint is_chain_rev (boot : list w8) (l : list $ list w8) (h : list w8) : iProp Σ :=
  match l with
  | [] =>
    "->" ∷ ⌜ boot = h ⌝ ∗
    "%Hlen" ∷ ⌜ Z.of_nat $ length h = cryptoffi.hash_len ⌝
  | x :: l' =>
    ∃ h',
    "#Hrecur" ∷ is_chain_rev boot l' h' ∗
    "#His_hash" ∷ cryptoffi.is_hash (h' ++ x) h
  end.
#[global] Opaque is_chain_rev.
#[local] Transparent is_chain_rev.

#[global]
Instance is_chain_rev_pers b l h : Persistent (is_chain_rev b l h).
Proof. revert h. induction l; apply _. Qed.

Lemma is_chain_rev_len b l h :
  is_chain_rev b l h -∗
  ⌜ Z.of_nat $ length h = cryptoffi.hash_len ⌝.
Proof.
  destruct l; simpl; iNamed 1.
  - done.
  - by iDestruct (cryptoffi.is_hash_len with "His_hash") as %?.
Qed.

Notation is_chain_aux b l h := (is_chain_rev b (reverse l) h).

(* a full chain. *)
Definition is_chain l h : iProp Σ :=
  ∃ he,
  "#He" ∷ cryptoffi.is_hash [] he ∗
  "#His_chain" ∷ is_chain_aux he l h.

(* a bootstrapped chain. *)
Definition is_chain_boot l h : iProp Σ :=
  ∃ boot,
  "#His_chain" ∷ is_chain_aux boot l h.

(* we can't prove inj bw two bootstrapped chains bc of cycles.
i.e., when Hash(boot, v) = boot, which makes
Chain(boot, []) look indistinguishable from Chain(boot, [v...]).
one fix is to track a max list limit (XXX: pin down core logic).
this takes a different approach, stating inj with a "complete"
chain, which prevents cycles by starting with an empty pre-img. *)
Local Lemma is_chain_inj_aux he l0 l1 b h :
  cryptoffi.is_hash [] he -∗
  is_chain_rev he l0 h -∗
  is_chain_rev b l1 h -∗
  ⌜ l1 `prefix_of` l0 ⌝.
Proof.
  iIntros "#He".
  iInduction l0 as [|??] forall (l1 h); destruct l1; simpl;
    iNamedSuffix 1 "0"; iNamedSuffix 1 "1"; [done|..].
  - iDestruct (is_chain_rev_len with "Hrecur1") as %?.
    iDestruct (cryptoffi.is_hash_inj with "He His_hash1") as %Heq.
    apply (f_equal length) in Heq.
    autorewrite with len in *.
    word.
  - iPureIntro. apply prefix_nil.
  - iDestruct (is_chain_rev_len with "Hrecur0") as %?.
    iDestruct (is_chain_rev_len with "Hrecur1") as %?.
    iDestruct (cryptoffi.is_hash_inj with "His_hash0 His_hash1") as %Heq.
    opose proof (app_inj_1 _ _ _ _ _ Heq) as [-> ->]; [lia|].
    iDestruct ("IHl0" with "Hrecur0 Hrecur1") as %?.
    iPureIntro. by apply prefix_cons.
Qed.

Lemma is_chain_inj l0 l1 h :
  is_chain l0 h -∗
  is_chain_boot l1 h -∗
  ⌜ l1 `suffix_of` l0 ⌝.
Proof.
  iNamedSuffix 1 "0". iNamedSuffix 1 "1".
  iDestruct (is_chain_inj_aux with "He0 His_chain0 His_chain1") as %?.
  iPureIntro. by apply suffix_prefix_reverse.
Qed.

(* not sure if we'll need this. *)
Local Lemma is_chain_inj0 l0 l1 h :
  is_chain l0 h -∗
  is_chain l1 h -∗
  ⌜ l0 = l1 ⌝.
Proof.
  iNamedSuffix 1 "0". iNamedSuffix 1 "1".
  iDestruct (is_chain_inj with "[$He0 $His_chain0] [$His_chain1]") as %?.
  iDestruct (is_chain_inj with "[$He1 $His_chain1] [$His_chain0]") as %?.
  iPureIntro.
  apply suffix_length_eq; [done|].
  by apply suffix_length.
Qed.

Lemma wp_GetEmptyLink :
  {{{ is_pkg_init hashchain }}}
  hashchain @ "GetEmptyLink" #()
  {{{
    sl h, RET #sl;
    "Hsl_hash" ∷ sl ↦* h ∗
    "#His_chain" ∷ is_chain [] h
  }}}.
Proof.
  wp_start.
  wp_apply (cryptoutil.wp_Hash _ inhabitant) as "* @".
  { iApply own_slice_nil. }
  iDestruct (cryptoffi.is_hash_len with "His_hash") as %?.
  iApply "HΦ". by iFrame "∗#".
Qed.

Lemma wp_GetNextLink sl_prevLink d0 prevLink sl_nextVal d1 nextVal b l :
  {{{
    is_pkg_init hashchain ∗
    "Hsl_prevLink" ∷ sl_prevLink ↦*{d0} prevLink ∗
    "Hsl_nextVal" ∷ sl_nextVal ↦*{d1} nextVal ∗
    "#His_chain" ∷ is_chain_aux b l prevLink
  }}}
  hashchain @ "GetNextLink" #sl_prevLink #sl_nextVal
  {{{
    sl_nextLink nextLink, RET #sl_nextLink;
    "Hsl_prevLink" ∷ sl_prevLink ↦*{d0} prevLink ∗
    "Hsl_nextVal" ∷ sl_nextVal ↦*{d1} nextVal ∗
    "Hsl_nextLink" ∷ sl_nextLink ↦* nextLink ∗
    "#His_chain" ∷ is_chain_aux b (l ++ [nextVal]) nextLink
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
  rewrite reverse_snoc.
  iFrame "∗#".
Qed.

(* [wish_Verify] says that new_vals encodes to proof. *)
Definition wish_Verify (proof : list w8) new_vals : iProp Σ :=
  "%Hlen_vals" ∷ ⌜ Forall (λ x, Z.of_nat (length x) = cryptoffi.hash_len) new_vals ⌝ ∗
  "%Henc_vals" ∷ ⌜ proof = mjoin new_vals ⌝.

Local Lemma wish_Verify_impl_eq_len proof new_vals :
  wish_Verify proof new_vals -∗
  ⌜ Z.of_nat (length proof) = (length new_vals * cryptoffi.hash_len)%Z ⌝.
Proof.
  iNamed 1. iPureIntro.
  subst. rewrite length_join.
  rewrite (sum_list_fmap_same (Z.to_nat (cryptoffi.hash_len))); [word|].
  apply (list.Forall_impl _ _ _ Hlen_vals).
  lia.
Qed.

Local Lemma wish_Verify_impl_mod_len proof new_vals :
  wish_Verify proof new_vals -∗
  ⌜ Z.of_nat (length proof) `mod` cryptoffi.hash_len = 0 ⌝.
Proof.
  iIntros "H".
  iDestruct (wish_Verify_impl_eq_len with "H") as %?.
  word.
Qed.

Lemma wish_Verify_det proof vs0 vs1 :
  wish_Verify proof vs0 -∗
  wish_Verify proof vs1 -∗
  ⌜ vs0 = vs1 ⌝.
Proof.
  iNamedSuffix 1 "0". iNamedSuffix 1 "1".
  subst. iPureIntro.
  eapply (list_join_inj (Z.to_nat $ cryptoffi.hash_len)); [lia|..|done].
  - eapply list.Forall_impl; [done|].
    intuition. lia.
  - eapply list.Forall_impl; [done|].
    intuition. lia.
Qed.

Local Lemma wish_Verify_next_val i proof vs :
  i >= 0 →
  let startp := Z.to_nat $ i * cryptoffi.hash_len in
  let endp := Z.to_nat $ (i + 1) * cryptoffi.hash_len in
  endp ≤ length proof →
  wish_Verify (take startp proof) vs -∗
  wish_Verify (take endp proof) (vs ++ [subslice startp endp proof]).
Proof.
  simpl. iIntros (??) "@".
  iPureIntro. split.
  { apply Forall_snoc.
    split; [done|].
    rewrite subslice_length; lia. }
  rewrite (take_subslice (Z.to_nat $ i * 32)); [|lia].
  rewrite join_app.
  f_equal; [done|].
  by list_simplifier.
Qed.

Definition own (l : loc) (vals : list $ list w8) : iProp Σ :=
  ∃ sl_predLastLink predLastLink sl_lastLink lastLink sl_enc enc,
  "Hstruct" ∷ l ↦ (hashchain.HashChain.mk sl_predLastLink sl_lastLink sl_enc) ∗

  "#Hsl_predLastLink" ∷ sl_predLastLink ↦*□ predLastLink ∗
  "#His_chain_pred" ∷ (∀ x vals', ⌜ vals = vals' ++ [x] ⌝ -∗
    is_chain vals' predLastLink) ∗

  "#Hsl_lastLink" ∷ sl_lastLink ↦*□ lastLink ∗
  "#His_chain" ∷ is_chain vals lastLink ∗

  "Hsl_enc" ∷ sl_enc ↦* enc ∗
  "Hsl_enc_cap" ∷ own_slice_cap w8 sl_enc ∗
  "#Henc" ∷ wish_Verify enc vals.

Lemma wp_New :
  {{{ is_pkg_init hashchain }}}
  hashchain @ "New" #()
  {{{ l, RET #l; "Hown_HashChain" ∷ own l [] }}}.
Proof.
  wp_start.
  wp_apply wp_GetEmptyLink as "* @".
  iPersist "Hsl_hash".
  wp_apply wp_alloc as "* H0".
  iApply "HΦ".
  iDestruct (own_slice_nil (DfracOwn 1)) as "H1".
  iDestruct (own_slice_nil DfracDiscarded) as "H2".
  iDestruct own_slice_cap_nil as "H3".
  iFrame "∗#".
  iSplit; [|naive_solver].
  iIntros (?? Heq).
  apply (f_equal length) in Heq.
  rewrite app_length in Heq.
  list_simplifier. lia.
Qed.

Lemma wp_HashChain_Append c vals sl_val d0 val :
  {{{
    is_pkg_init hashchain ∗
    "Hown_HashChain" ∷ own c vals ∗
    "Hsl_val" ∷ sl_val ↦*{d0} val ∗
    "%Hlen_val" ∷ ⌜ Z.of_nat $ length val = cryptoffi.hash_len ⌝
  }}}
  c @ hashchain @ "HashChain'ptr" @ "Append" #sl_val
  {{{
    sl_newLink newLink, RET #sl_newLink;
    "Hown_HashChain" ∷ own c (vals ++ [val]) ∗
    "Hsl_val" ∷ sl_val ↦*{d0} val ∗
    "#Hsl_newLink" ∷ sl_newLink ↦*□ newLink ∗
    "#His_chain" ∷ is_chain (vals ++ [val]) newLink
  }}}.
Proof.
  wp_start. iNamed "Hpre". iNamed "Hown_HashChain".
  wp_auto.
  iDestruct (own_slice_len with "Hsl_val") as %?.
  wp_apply wp_Assert.
  { iPureIntro. apply bool_decide_eq_true. word. }
  iNamed "His_chain".
  wp_apply (wp_GetNextLink with "[Hsl_val]").
  { iFrame "∗#". }
  iIntros "*". iNamedSuffix 1 "_n".
  iPersist "Hsl_prevLink_n Hsl_nextLink_n".
  wp_auto.
  wp_apply (wp_slice_append with "[$Hsl_enc $Hsl_enc_cap $Hsl_nextVal_n]") as "* (Hsl_enc & Hsl_enc_cap & Hsl_nextVal_n)".
  iApply "HΦ".
  iFrame "∗#".
  iSplit.
  - iIntros (?? Heq).
    apply app_inj_tail in Heq as [-> ->].
    iFrame "#".
  - iNamed "Henc". iPureIntro. split.
    + rewrite Forall_snoc. split; [done|word].
    + rewrite join_app. f_equal; [done|]. by list_simplifier.
Qed.

Lemma wp_HashChain_Prove c vals (prevLen : w64) :
  {{{
    is_pkg_init hashchain ∗
    "Hown_HashChain" ∷ own c vals ∗
    "%Hlt_prevLen" ∷ ⌜ uint.Z prevLen <= length vals ⌝
  }}}
  c @ hashchain @ "HashChain'ptr" @ "Prove" #prevLen
  {{{
    sl_proof proof, RET #sl_proof;
    "Hown_HashChain" ∷ own c vals ∗
    "Hsl_proof" ∷ sl_proof ↦* proof ∗
    "#Hwish" ∷ wish_Verify proof (drop (uint.nat prevLen) vals)
  }}}.
Proof.
  wp_start. iNamed "Hpre". iNamed "Hown_HashChain".
  wp_auto.
  Search slice.slice.
  iDestruct (own_slice_len with "Hsl_enc") as %?.
  wp_apply (wp_slice_slice with "[$Hsl_enc]") as "(Hsl0 & Hsl1 & Hsl2)".
  { iDestruct (wish_Verify_impl_eq_len with "Henc") as %?. word. }
Admitted.

Lemma wp_Verify sl_prevLink prevLink sl_proof proof l :
  {{{
    is_pkg_init hashchain ∗
    "Hsl_prevLink" ∷ sl_prevLink ↦* prevLink ∗
    "#Hsl_proof" ∷ sl_proof ↦*□ proof ∗
    "#His_chain" ∷ is_chain_boot l prevLink
  }}}
  hashchain @ "Verify" #sl_prevLink #sl_proof
  {{{
    (extLen : w64) sl_newVal newVal sl_newLink newLink err,
    RET (#extLen, #sl_newVal, #sl_newLink, #err);
    "#Hsl_newVal" ∷ sl_newVal ↦*□ newVal ∗
    "Hsl_newLink" ∷ sl_newLink ↦* newLink ∗
    "Hgenie" ∷ (⌜ err = false ⌝ ∗-∗ ∃ new_vals, wish_Verify proof new_vals) ∗
    "Herr" ∷ (∀ new_vals, wish_Verify proof new_vals -∗
      (* TODO(goose): stdpp things like [last] that shadow Stdlib things
      have extremely brittle imports in Perennial.
      see my external notes on fixing. *)
      "->" ∷ ⌜ newVal = default [] (list.last new_vals) ⌝ ∗
      "#His_chain" ∷ is_chain_boot (l ++ new_vals) newLink)
  }}}.
Proof.
  wp_start. iNamed "Hpre".
  wp_auto.
  iPersist "proof".
  iDestruct (own_slice_len with "Hsl_proof") as %?.
  wp_if_destruct.
  2: {
    wp_auto.
    iApply "HΦ".
    (* TODO(goose): could "nil ownership" be automated? *)
    iDestruct (own_slice_nil (DfracOwn 1)) as "?".
    iDestruct (own_slice_nil DfracDiscarded) as "?".
    iFrame "∗#". iSplit.
    - iSplit. { by iIntros (?). }
      iNamed 1.
      iDestruct (wish_Verify_impl_mod_len with "[//]") as %?.
      word.
    - (* TODO: repetitive genie structure. how to fix?
      in both cases, if had wish, contra. *)
      iIntros (?) "@".
      iDestruct (wish_Verify_impl_mod_len with "[//]") as %?.
      word. }
  wp_auto.
  iPersist "extLen".

  remember (word.divu _ _) as extLen.
  iAssert (
    ∃ (i : w64) sl_newLink newLink sl_newVal newVal new_vals,
    "i" ∷ i_ptr ↦ i ∗
    "newLink" ∷ newLink_ptr ↦ sl_newLink ∗
    "newVal" ∷ newVal_ptr ↦ sl_newVal ∗
    "Hsl_newLink" ∷ sl_newLink ↦* newLink ∗
    "#Hsl_newVal" ∷ sl_newVal ↦*□ newVal ∗

    "%Hlt_i" ∷ ⌜ uint.Z i ≤ uint.Z extLen ⌝ ∗
    "#Hwish" ∷ wish_Verify
      (take (Z.to_nat (uint.Z i * cryptoffi.hash_len)) proof) new_vals ∗
    "->" ∷ ⌜ newVal = default [] (stdpp.list_basics.list.last new_vals) ⌝ ∗
    "#His_chain" ∷ is_chain_boot (l ++ new_vals) newLink
  )%I with "[i newLink newVal Hsl_prevLink]" as "IH".
  { iDestruct own_slice_nil as "?".
    iFrame "∗#".
    iExists [].
    list_simplifier.
    (* TODO(goose): [is_pkg_init] gets unfolded after [list_simplifier]. *)
    iFrame "#".
    rewrite take_0'; [|word].
    iPureIntro.
    split; [word|].
    naive_solver. }
  iClear "His_chain".
  wp_for "IH".
  case_bool_decide.

  2: {
    wp_auto.
    rewrite take_ge; [|word].
    iApply "HΦ".
    iFrame "∗#".
    iSplit. { iSplit; [|done]. iIntros "_". iFrame "#". }
    iIntros (?) "Hwish0".
    iDestruct (wish_Verify_det with "Hwish Hwish0") as %->.
    by iFrame "#". }

  wp_auto.
  wp_apply (wp_slice_slice with "[$Hsl_proof]"); [word|].
  iIntros "(_&#Hsub&_)".
  wp_auto.
  iNamed "His_chain".
  wp_apply (wp_GetNextLink with "[$Hsl_newLink $Hsub $His_chain]") as "*".
  iNamedSuffix 1 "_n".
  iClear "His_chain".
  wp_auto.
  wp_for_post.
  iFrame.
  iDestruct (wish_Verify_next_val with "Hwish") as "#Hwish_n"; [word..|].
  iClear "Hwish".
  replace (uint.Z (word.add _ _)) with (uint.Z i + 1) by word.
  iFrame "#".
  repeat iSplit.
  - word.
  - rewrite last_snoc /=. iPureIntro. f_equal; word.
  - iExists _.
    iExactEq "His_chain_n".
    rewrite /named.
    list_simplifier.
    repeat f_equal; word.
Qed.

End proof.
End hashchain.
