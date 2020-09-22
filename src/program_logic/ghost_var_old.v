From iris.algebra Require Export lib.excl_auth proofmode_classes.
From iris.proofmode Require Import base tactics classes.
From iris.program_logic Require Import weakestpre.
Unset Implicit Arguments.

Set Default Goal Selector "!".
Set Default Proof Using "Type".

Definition ghostR (A: ofeT) := excl_authR A.

Section ghost_var_helpers.
Context {A: ofeT} `{Hleibniz: @LeibnizEquiv _ A.(ofe_equiv)} {Hdiscrete: OfeDiscrete A}.
Context {Σ} {Hin: inG Σ (ghostR A)}.

Lemma ghost_var_alloc (a: A) :
  ⊢ |==> ∃ γ, own γ (●E a) ∗ own γ (◯E a).
Proof.
  iMod (own_alloc (●E a ⋅ ◯E a)) as (γ) "[H1 H2]".
  { apply excl_auth_valid. }
  iModIntro. eauto with iFrame.
Qed.

Lemma ghost_var_agree γ (a1 a2: A) :
  own γ (●E a1) -∗ own γ (◯E a2) -∗ ⌜ a1 = a2 ⌝.
Proof using Hleibniz Hdiscrete.
  iIntros "Hγ1 Hγ2".
  iDestruct (own_valid_2 with "Hγ1 Hγ2") as "H".
  by iDestruct "H" as %->%excl_auth_agree%leibniz_equiv.
Qed.

Lemma ghost_var_frac_agree γ q (a1 a2: A) :
  own γ (●{q} (Excl' a1)) -∗ own γ (◯E a2) -∗ ⌜ a1 = a2 ⌝.
Proof using Hleibniz Hdiscrete.
  iIntros "Hγ1 Hγ2".
  iDestruct (own_valid_2 with "Hγ1 Hγ2") as "H".
  iDestruct "H" as %(_&<-%Excl_included%leibniz_equiv&_)%auth_both_frac_valid.
  done.
Qed.

Lemma ghost_var_frac_frac_agree γ q1 q2 (a1 a2: A) :
  own γ (●{q1} (Excl' a1)) -∗ own γ (●{q2} (Excl' a2)) -∗ ⌜ a1 = a2 ⌝.
Proof using Hleibniz Hdiscrete.
  iIntros "Hγ1 Hγ2".
  iDestruct (own_valid_2 with "Hγ1 Hγ2") as "H".
  iDestruct "H" as %Hvalid%auth_auth_frac_op_inv%leibniz_equiv.
  by inversion Hvalid.
Qed.

Lemma ghost_var_update γ (a1' a1 a2 : A) :
  own γ (●E a1) -∗ own γ (◯E a2) ==∗
    own γ (●E a1') ∗ own γ (◯E a1').
Proof.
  iIntros "Hγ● Hγ◯".
  iMod (own_update_2 _ _ _ (●E a1' ⋅ ◯E a1') with "Hγ● Hγ◯") as "[$$]".
  { apply excl_auth_update. }
  done.
Qed.

(* this makes [●E a] splittable into [●{1/2} Excl' a ∗ ●{1/2} Excl' a] *)
Global Instance is_op_excl_auth_frac (q1 q2: Qp) (a:A) :
  IsOp 1%Qp q1 q2 →
  IsOp' (●E a) (●{q1} Excl' a) (●{q2} Excl' a).
Proof.
  rewrite /excl_auth_auth.
  apply _.
Qed.

End ghost_var_helpers.

From iris.proofmode Require Import coq_tactics intro_patterns spec_patterns.
From iris.proofmode Require Import tactics.
From stdpp Require Import hlist pretty.

(* This tactic searches for own H (● (Excl' x)) and own H (◯ (Excl' y)) in the context and
   uses ghost_var_agree to prove that x = y. *)
Ltac unify_ghost :=
  match goal with
  | [ |- context[ environments.Esnoc _ (INamed ?auth_name) (own ?y (●E ?x))] ] =>
    match goal with
    | [ |- context[ own y (◯E x)] ] => fail 1
    | [ |- context[ environments.Esnoc _ (INamed ?frag_name) (own y (◯E ?z))] ] =>
      let pat := constr:([(SIdent (INamed auth_name) nil); (SIdent (INamed frag_name) nil)]) in
      (* TODO: can we write this with a fresh variable rather than Hp, and using
      inversion Hp; subst; clear Hp (which is less buggy than
      inversion_clear)? *)
      (iDestruct (ghost_var_agree with pat) as %Hp; inversion_clear Hp; subst; [])
    end
  end.
