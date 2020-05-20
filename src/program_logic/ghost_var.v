From iris.algebra Require Import auth excl.
From iris.proofmode Require Import base tactics classes.
From iris.program_logic Require Import weakestpre.
Unset Implicit Arguments.

Definition ghostR (A: ofeT) := (authR (optionUR (exclR A))).

Section ghost_var_helpers.
Context {A: ofeT} `{@LeibnizEquiv _ A.(ofe_equiv)} `{OfeDiscrete A}.
Context {Σ} {Hin: inG Σ (ghostR A)}.

Lemma ghost_var_alloc (a: A) :
  ⊢ |==> ∃ γ, own γ (● (Excl' a)) ∗ own γ (◯ (Excl' a)).
Proof.
  iMod (own_alloc (● (Excl' a) ⋅ ◯ (Excl' a))) as (γ) "[H1 H2]".
  { apply auth_both_valid; split; eauto. econstructor. }
  iModIntro. iExists γ. iFrame.
Qed.

Lemma ghost_var_agree γ (a1 a2: A) :
  own γ (● (Excl' a1)) -∗ own γ (◯ (Excl' a2)) -∗ ⌜ a1 = a2 ⌝.
Proof.
  iIntros "Hγ1 Hγ2".
  iDestruct (own_valid_2 with "Hγ1 Hγ2") as "H".
  iDestruct "H" as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid.
  done.
Qed.

Lemma ghost_var_frac_agree γ q (a1 a2: A) :
  own γ (●{q} (Excl' a1)) -∗ own γ (◯ (Excl' a2)) -∗ ⌜ a1 = a2 ⌝.
Proof.
  iIntros "Hγ1 Hγ2".
  iDestruct (own_valid_2 with "Hγ1 Hγ2") as "H".
  iDestruct "H" as %(_&<-%Excl_included%leibniz_equiv&_)%auth_both_frac_valid.
  done.
Qed.

Lemma ghost_var_frac_frac_agree γ q1 q2 (a1 a2: A) :
  own γ (●{q1} (Excl' a1)) -∗ own γ (●{q2} (Excl' a2)) -∗ ⌜ a1 = a2 ⌝.
Proof.
  iIntros "Hγ1 Hγ2".
  iDestruct (own_valid_2 with "Hγ1 Hγ2") as "H".
  iDestruct "H" as %Hvalid%auth_auth_frac_op_inv%leibniz_equiv.
  by inversion Hvalid.
Qed.

Lemma ghost_var_update γ (a1' a1 a2 : A) :
  own γ (● (Excl' a1)) -∗ own γ (◯ (Excl' a2)) ==∗
    own γ (● (Excl' a1')) ∗ own γ (◯ (Excl' a1')).
Proof.
  iIntros "Hγ● Hγ◯".
  iMod (own_update_2 _ _ _ (● Excl' a1' ⋅ ◯ Excl' a1') with "Hγ● Hγ◯") as "[$$]".
  { by apply auth_update, option_local_update, exclusive_local_update. }
  done.
Qed.

End ghost_var_helpers.

From iris.proofmode Require Import coq_tactics intro_patterns spec_patterns.
From iris.proofmode Require Import tactics.
From stdpp Require Import hlist pretty.

(* This tactic searches for own H (● (Excl' x)) and own H (◯ (Excl' y)) in the context and
   uses ghost_var_agree to prove that x = y. *)
Ltac unify_ghost :=
  match goal with
  | [ |- context[ environments.Esnoc _ (INamed ?auth_name) (own ?y (● (Excl' ?x)))] ] =>
    match goal with
    | [ |- context[ own y (◯ (Excl' x))] ] => fail 1
    | [ |- context[ environments.Esnoc _ (INamed ?frag_name) (own y (◯ (Excl' ?z)))] ] =>
      let pat := constr:([(SIdent (INamed auth_name) nil); (SIdent (INamed frag_name) nil)]) in
      (* TODO: can we write this with a fresh variable rather than Hp, and using
      inversion Hp; subst; clear Hp (which is less buggy than
      inversion_clear)? *)
      (iDestruct (ghost_var_agree with pat) as %Hp; inversion_clear Hp; subst; [])
    end
  end.
