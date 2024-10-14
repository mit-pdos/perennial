From Perennial.goose_lang Require Export lifting.
From New.golang.defn Require Export list.
From New.golang.theory Require Import exception.

Section wps.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Global Instance pure_cons (v : val) (l : list val) :
  PureWpVal True (list.Cons v (list.val l)) (list.val (v :: l)).
Proof.
  rewrite list.Cons_unseal list.val_unseal.
  intros ????. iIntros "HΦ".
  wp_rec. wp_pures. iApply "HΦ".
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
  destruct l; wp_rec; wp_pures; iFrame.
Qed.

Lemma wp_list_Length {stk E} (l : list val) :
  {{{ True }}}
    (list.Length (list.val l)) @ stk ; E
  {{{ RET #(W64 (length l)); ⌜ length l = uint.nat (W64 (length l)) ⌝ }}}.
Proof.
  iIntros (?) "_ HΦ".
  iInduction l as [] "IH" forall (Φ).
  - wp_rec; wp_pures. by iApply "HΦ".
  - wp_rec. wp_pures.
    wp_apply "IH".
    iIntros "%".
    wp_pures. wp_if_destruct.
    {
      simpl.
      replace (W64 (S $ length l)) with (word.add (W64 1) (W64 (length l))) by word.
      iApply "HΦ".
      iPureIntro. word.
    }
    {
      iClear "HΦ IH".
      wp_pure. iLöb as "IH". wp_pure. done.
    }
Qed.

End wps.
