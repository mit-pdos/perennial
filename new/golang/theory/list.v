From Perennial.goose_lang Require Export proofmode lifting.
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

Global Instance wp_list_Length (l : list val) :
  PureWp True
    (list.Length (list.val l))
    #(W64 (length l))
.
Proof.
  rewrite /list.Length.
  intros ?????. iIntros "Hwp".
  iInduction l as [] "IH" forall (K Φ).
  - wp_rec; wp_pures; iFrame.
  - wp_rec. wp_pure. fold list.Length. wp_pures.
    wp_bind (list.Length _).
    wp_apply ("IH" $! []).
    wp_pures. wp_pures. simpl.
    replace (W64 (S $ length l)) with (word.add (W64 1) (W64 (length l))) by word.
    wp_apply "Hwp".
Qed.

End wps.
