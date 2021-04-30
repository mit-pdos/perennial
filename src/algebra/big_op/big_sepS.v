From iris.algebra Require Export big_op.
From iris.proofmode Require Import tactics.
From Perennial.base_logic Require Import ncfupd.

Section sep_intro.
  Context {PROP:bi}.
  Context `{Countable K}.


  Lemma big_sepS_intro_emp (m: gset K) :
    ⊢ [∗ set] x ∈ m, (emp : PROP).
  Proof.
    iInduction m as [] "IH" using set_ind_L.
    { rewrite big_sepS_empty //. }
    { rewrite big_sepS_union; last set_solver. iFrame "IH".
      rewrite big_sepS_singleton //. }
  Qed.

End sep_intro.
