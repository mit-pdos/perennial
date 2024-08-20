From iris.proofmode Require Import proofmode.

Section lemmas.
  Context `{SemiSet A C}.

  Lemma set_Forall_subseteq (P : A -> Prop) (X Y : C) :
    X ⊆ Y ->
    set_Forall P Y ->
    set_Forall P X.
  Proof. intros Hsubseteq HY x Hx. apply HY. set_solver. Qed.

End lemmas.
