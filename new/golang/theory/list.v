From Perennial.Helpers Require Import List.
From Perennial.goose_lang Require Export lifting.
From New.golang.defn Require Export typing list.
From New.golang.theory Require Import exception.
From New.golang.theory Require Import proofmode.

Set Default Proof Using "Type".

Section wps.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!IntoVal V}.

Global Instance to_val_list : IntoVal (list V) :=
  {|
    to_val_def := fix go (l : list V) :=
        match l with
        | [] => InjLV #()
        | h :: tl => (InjRV (#h, go tl))
        end
  |}.

Global Instance wp_Cons (v : V) (l : list V) :
  PureWp True (list.Cons #v #l) #(v :: l).
Proof.
  rewrite list.Cons_unseal.
  intros ?????. iIntros "Hwp". wp_call_lc "?".
  simpl.
  repeat rewrite to_val_unseal /=.
  by iApply "Hwp".
Qed.

Global Instance wp_Cons_Nil (v : V) :
  PureWp True (list.Cons #v list.Nil) #(v :: nil).
Proof.
  rewrite list.Cons_unseal list.Nil_unseal.
  intros ?????. iIntros "Hwp". wp_call_lc "?".
  simpl.
  rewrite /list.Nil_def.
  repeat rewrite to_val_unseal /=.
  by iApply "Hwp".
Qed.

Global Instance wp_list_Match (l : list V) (handleNil handleCons : val) :
  PureWp True
    (list.Match #l handleNil handleCons)
    (match l with
     | nil => (handleNil #())%V
     | cons v l => (handleCons #v #l)%V
     end).
Proof.
  rewrite list.Match_unseal.
  intros ?????. iIntros "Hwp".
  rewrite [in #l]to_val_unseal.
  destruct l; wp_call_lc "?".
  - by iApply "Hwp".
  - repeat rewrite to_val_unseal /=.
    by iApply "Hwp".
Qed.

Lemma wp_list_Length {stk E} (l : list V) :
  {{{ True }}}
    (list.Length #l) @ stk ; E
  {{{ RET #(W64 (length l)); ⌜ length l = sint.nat (W64 (length l)) ⌝ }}}.
Proof.
  iIntros (?) "_ HΦ".
  iInduction l as [] "IH" forall (Φ).
  - wp_call. by iApply "HΦ".
  - wp_call.
    wp_apply "IH".
    iIntros "%".
    wp_pures.
    destruct bool_decide eqn:Hle.
    + wp_pures.
      apply bool_decide_eq_true_1 in Hle.
      simpl.
      replace (W64 (S $ length l)) with (word.add (W64 1) (W64 (length l))) by word.
      iApply "HΦ".
      word.
    + iClear "HΦ IH".
      wp_pures. iLöb as "IH". wp_pures. done.
Qed.

Lemma wp_list_Get {stk E} (l : list V) (i: w64) (v: V) :
  l !! (uint.nat i) = Some v →
  {{{ True }}}
    (list.Get #l #i) @ stk ; E
  {{{ RET #v; True }}}.
Proof.
  intros Hget.
  iIntros (?) "_ HΦ".
  iInduction l as [] "IH" forall (Φ v i Hget).
  - rewrite lookup_nil in Hget. congruence.
  - wp_call.
    destruct (bool_decide_reflect (i = W64 0)); wp_pures.
    + subst. change (uint.nat (W64 0)) with 0%nat in Hget.
      simpl in Hget. replace a with v by congruence.
      by iApply "HΦ".
    + replace (uint.nat i) with (S (uint.nat (word.sub i (W64 1)))) in Hget by word.
      simpl in Hget.
      wp_apply "IH".
      { eauto. }
      by iApply "HΦ".
Qed.

Lemma wp_list_Insert {stk E} (l : list V) (i: w64) (v': V) :
  is_Some (l !! (uint.nat i)) →
  {{{ True }}}
    (list.Insert #l #i #v') @ stk ; E
  {{{ RET #(<[uint.nat i := v']> l); True }}}.
Proof.
  intros [v Hget].
  iIntros (?) "_ HΦ".
  iInduction l as [] "IH" forall (Φ v i Hget).
  - rewrite lookup_nil in Hget. congruence.
  - wp_call.
    destruct (bool_decide_reflect (i = W64 0)); wp_pures.
    + subst. change (uint.nat (W64 0)) with 0%nat in Hget.
      simpl in Hget. replace a with v by congruence.
      by iApply "HΦ".
    + replace (uint.nat i) with (S (uint.nat (word.sub i (W64 1)))) in * by word.
      simpl in Hget.
      wp_apply "IH".
      { eauto. }
      wp_pures.
      simpl.
      by iApply "HΦ".
Qed.

Lemma wp_random_int (n: w64) :
  0 < uint.Z n →
  {{{ True }}}
    list.list.random_int #n
  {{{ (x: w64), RET #x; ⌜uint.Z x < uint.Z n⌝ }}}.
Proof.
  intros H.
  iIntros (?) "_ HΦ".
  wp_call. wp_apply wp_ArbitraryInt.
  iIntros (x) "_".
  replace (LitV x) with (#x).
  { wp_pures. iApply "HΦ". word. }
  rewrite to_val_unseal //.
Qed.

#[local] Lemma wp_list_shuffle_helper (l : list V) (len_w: w64) (remaining: w64) :
  {{{ ⌜length l = uint.nat len_w ∧ uint.Z remaining ≤ uint.Z len_w⌝ }}}
    list.list.shuffle_helper #l #len_w #remaining
  {{{ (l': list V), RET #l'; ⌜l ≡ₚ l'⌝ }}}.
Proof.
  iIntros (Φ) "%Hbound HΦ".
  iLöb as "IH" forall (l len_w remaining Hbound).
  wp_call.
  change (uint.Z (W64 0)) with 0.
  destruct (bool_decide_reflect (uint.Z remaining ≤ 0)); wp_pures.
  - iApply "HΦ". done.
  - wp_apply wp_random_int.
    { word. }
    iIntros (idx) "%Hidx_bound".
    wp_pures.
    destruct (lookup_lt_is_Some_2 l (uint.nat idx)) as [v Hget].
    { word. }
    wp_apply wp_list_Get; first by eauto.
    wp_pures.
    destruct (lookup_lt_is_Some_2 l (uint.nat (word.sub remaining (W64 1)))) as [v_last Hget_last].
    { word. }
    wp_apply wp_list_Get; first by eauto.
    wp_pures.
    wp_apply wp_list_Insert.
    { eauto. }
    wp_pures.
    wp_apply wp_list_Insert.
    { apply lookup_lt_is_Some_2.
      rewrite length_insert. word. }
    wp_pure.
    wp_pure.
    wp_apply "IH".
    { rewrite !length_insert; word. }
    iIntros (l') "%Hperm".
    iApply "HΦ".
    iPureIntro.
    rewrite -Hperm.
    rewrite Permutation_insert_swap; eauto.
Qed.

Lemma wp_list_Shuffle (l : list V) :
  {{{ True }}}
    list.Shuffle #l
  {{{ (l': list V), RET #l'; ⌜l ≡ₚ l'⌝ }}}.
Proof.
  iIntros (?) "_ HΦ".
  wp_call. wp_apply wp_list_Length. iIntros "%Hlen".
  wp_pures.
  wp_apply wp_list_shuffle_helper.
  { word. }
  iIntros (l') "%Hperm".
  iApply "HΦ".
  done.
Qed.

Global Instance wp_alist_cons (k : go_string) (l : list (go_string * val)) (v : val) :
  PureWp  True
    (list.Cons (PairV #k v) (alist_val l))
    (alist_val ((pair k v) :: l)).
Proof.
  iIntros (?????) "HΦ".
  rewrite alist_val_unseal list.Cons_unseal.
  wp_call_lc "?". by iApply "HΦ".
Qed.

Global Instance wp_alist_lookup (k : go_string) (l : list (go_string * val)) :
  PureWp True
    (alist_lookup #k (alist_val l))
    (match (alist_lookup_f k l) with | None => InjLV #() | Some v => InjRV v end).
Proof.
  iIntros (?????) "HΦ".
  rewrite alist_val_unseal.
  iInduction l as [|[]] "IH" forall (Φ); [refine ?[base]| refine ?[cons]].
  [base]:{
    simpl. wp_call. rewrite list.Match_unseal.
    wp_call_lc "?". rewrite to_val_unseal. by iApply "HΦ".
  }
  [cons]: {
    wp_call_lc "?".
    rewrite list.Match_unseal /=.
    wp_call.
    destruct bool_decide eqn:Heqb; wp_pures.
    {
      rewrite bool_decide_eq_true in Heqb.
      subst.
      rewrite ByteString.eqb_refl.
      by iApply "HΦ".
    }
    {
      rewrite bool_decide_eq_false in Heqb.
      wp_pures.
      iApply "IH".
      rewrite ByteString.eqb_ne //.
    }
  }
Qed.

End wps.
