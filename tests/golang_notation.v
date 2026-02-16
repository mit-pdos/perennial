From New.proof Require Import proof_prelude.
From New.proof Require Import grove_prelude.
From New.golang Require Import theory.

Section proof.
Context `{!heapGS Σ}.
Context {sem : go.Semantics}.

Check "pointsto_print".
Lemma pointsto_print (l1 l2 : loc) (v1 : bool) (v2 : slice.t) dq :
  l1 ↦ v1 ∗ l2 ↦{dq} v2 ∗ l1 ↦□ v1 ⊢ True.
Proof.
  Show.
Abort.

Check "tuple print".
Lemma tuple_print (l : loc) :
  {{{ True }}}
    (λ: <>, #())
  {{{ RET (#true, #true); True }}}.
Proof.
  Show.
Abort.

End proof.
