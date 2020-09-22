From iris.algebra Require Import frac_agree.
From iris.base_logic Require Export ghost_var.
From Perennial.algebra Require Import own_discrete.
From iris.proofmode Require Import tactics.

Section lemmas.
  Context `{!ghost_varG Σ A}.
  Implicit Types (a : A) (q : Qp).

  Global Instance ghost_var_discrete γ q a : Discretizable (ghost_var γ q a).
  Proof. rewrite /ghost_var. apply _. Qed.

  (* TODO: upstream this *)
  Lemma frac_agree_op q1 q2 (a : leibnizO A) :
    to_frac_agree (q1 + q2) a ≡ to_frac_agree q1 a ⋅ to_frac_agree q2 a.
  Proof. rewrite /to_frac_agree -pair_op agree_idemp //. Qed.
  Lemma ghost_var_update_2 b γ a1 q1 a2 q2 :
    (q1 + q2 = 1)%Qp →
    ghost_var γ q1 a1 ∗ ghost_var γ q2 a2 ==∗ ghost_var γ q1 b ∗ ghost_var γ q2 b.
  Proof.
    iIntros (Hq) "[H1 H2]".
    iDestruct (ghost_var_op_valid with "H1 H2") as %[_ ->].
    iCombine "H1 H2" as "H". rewrite Hq.
    iMod (ghost_var_update with "H") as "H".
    rewrite -Hq. iApply ghost_var_split. done.
  Qed.
  Lemma ghost_var_update_halves b γ a1 a2 :
    ghost_var γ (1/2) a1 ∗ ghost_var γ (1/2) a2 ==∗ ghost_var γ (1/2) b ∗ ghost_var γ (1/2) b.
  Proof. iApply ghost_var_update_2. apply Qp_half_half. Qed.

End lemmas.
