From Perennial.goose_lang Require Export lifting.
From New.golang.defn Require Export typing list.
From New.golang.theory Require Import exception.
From New.golang.theory Require Import proofmode.

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
  {{{ RET #(W64 (length l)); ⌜ length l = uint.nat (W64 (length l)) ⌝ }}}.
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
    wp_call_lc "?". by iApply "HΦ".
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
