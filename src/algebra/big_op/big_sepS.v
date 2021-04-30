From iris.algebra Require Export big_op.
From iris.proofmode Require Import tactics.
From Perennial.base_logic Require Import ncfupd.

Section sep_intro.
  Context {PROP:bi}.
  Context `{Countable K}.


  Lemma big_sepS_intro_emp `{!BiAffine PROP} (m: gset K) :
    ⊢ [∗ set] x ∈ m, (emp : PROP).
  Proof. iApply big_sepS_forall. eauto. Qed.

End sep_intro.
