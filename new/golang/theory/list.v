From Perennial.goose_lang Require Export lifting.
From New.golang.defn Require Export list.
From New.golang.theory Require Import exception.
From New.golang.theory Require Import proofmode.

Section wps.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Global Instance pure_cons (v : val) (l : list val) :
  PureWp True (list.Cons v (list.val l)) (list.val (v :: l)).
Proof.
  rewrite list.Cons_unseal list.val_unseal.
  intros ?????. iIntros "Hwp". wp_call_lc "?". by iApply "Hwp".
Qed.

Global Instance wp_list_Match (l : list val) (handleNil handleCons : val) :
  PureWp True
    (list.Match (list.val l) handleNil handleCons)
    (match l with
     | nil => (handleNil #())%V
     | cons a l => (handleCons a (list.val l))%V
     end)
.
Proof.
  rewrite list.Match_unseal list.val_unseal.
  intros ?????. iIntros "Hwp".
  destruct l; wp_call_lc "?"; by iApply "Hwp".
Qed.

Lemma wp_list_Length {stk E} (l : list val) :
  {{{ True }}}
    (list.Length (list.val l)) @ stk ; E
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
      iPureIntro. word.
    + iClear "HΦ IH".
      wp_pures. iLöb as "IH". wp_pures. done.
Qed.

End wps.
