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
  Lemma ghost_var_agree γ a1 q1 a2 q2 :
    ghost_var γ q1 a1 -∗ ghost_var γ q2 a2 -∗ ⌜a1 = a2⌝.
  Proof.
    iIntros "Hvar1 Hvar2".
    iDestruct (ghost_var_op_valid with "Hvar1 Hvar2") as %[_ ?]. done.
  Qed.
  Lemma frac_agree_op q1 q2 (a : leibnizO A) :
    to_frac_agree (q1 + q2) a ≡ to_frac_agree q1 a ⋅ to_frac_agree q2 a.
  Proof. rewrite /to_frac_agree -pair_op agree_idemp //. Qed.
  Lemma ghost_var_update_2 b γ a1 q1 a2 q2 :
    (q1 + q2 = 1)%Qp →
    ghost_var γ q1 a1 -∗ ghost_var γ q2 a2 ==∗ ghost_var γ q1 b ∗ ghost_var γ q2 b.
  Proof.
    iIntros (Hq) "H1 H2".
    iDestruct (ghost_var_op_valid with "H1 H2") as %[_ ->].
    iCombine "H1 H2" as "H". rewrite Hq.
    iMod (ghost_var_update with "H") as "H".
    rewrite -Hq. iApply ghost_var_split. done.
  Qed.
  Lemma ghost_var_update_halves b γ a1 a2 :
    ghost_var γ (1/2) a1 -∗ ghost_var γ (1/2) a2 ==∗ ghost_var γ (1/2) b ∗ ghost_var γ (1/2) b.
  Proof. iApply ghost_var_update_2. apply Qp_half_half. Qed.

End lemmas.


From iris.proofmode Require Import coq_tactics intro_patterns spec_patterns.
From iris.proofmode Require Import tactics.
From stdpp Require Import hlist pretty.

(* This tactic searches for own H (● (Excl' x)) and own H (◯ (Excl' y)) in the context and
   uses ghost_var_agree to prove that x = y. *)
Tactic Notation "unify_ghost_var" constr(γ) :=
  match goal with
  | [ |- context[ environments.Esnoc _ (INamed ?auth_name) (ghost_var γ _ ?x)] ] =>
    match goal with
    | [ |- context[ environments.Esnoc _ (INamed ?frag_name) (ghost_var γ _ ?z)] ] =>
      (* make sure these are two different names *)
      let eq := constr:(bool_decide (auth_name = frag_name)) in
      match (eval hnf in eq) with
      | true => fail 1 (* backtrack to next match *)
      | false =>
        let pat := constr:([(SIdent (INamed auth_name) nil); (SIdent (INamed frag_name) nil)]) in
        (* TODO: can we write this with a fresh variable rather than Hp, and using
        inversion Hp; subst; clear Hp (which is less buggy than
        inversion_clear)? *)
        (iDestruct (ghost_var_agree with pat) as %Hp; inversion_clear Hp; subst; [])
      end
    end
  end.
