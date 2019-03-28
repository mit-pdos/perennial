From iris.algebra Require Import auth.
Require Export CSL.Refinement CSL.NamedDestruct ExMach.WeakestPre CSL.ProofModeClasses.
Unset Implicit Arguments.

(* TODO: move *)
Section ghost_var_helpers.
Context {A: ofeT} `{@LeibnizEquiv _ A.(ofe_equiv)} `{OfeDiscrete A}.
Context {Σ} {Hin: inG Σ (authR (optionUR (exclR A)))}.

Lemma ghost_var_alloc (a: A) :
  (|==> ∃ γ, own γ (● (Excl' a)) ∗ own γ (◯ (Excl' a)))%I.
Proof.
  iMod (own_alloc (● (Excl' a) ⋅ ◯ (Excl' a))) as (γ) "[H1 H2]".
  { apply auth_valid_discrete_2; split; eauto. econstructor. }
  iModIntro. iExists γ. iFrame.
Qed.

Lemma ghost_var_agree γ (a1 a2: A) :
  own γ (● (Excl' a1)) -∗ own γ (◯ (Excl' a2)) -∗ ⌜ a1 = a2 ⌝.
Proof.
  iIntros "Hγ1 Hγ2".
  iDestruct (own_valid_2 with "Hγ1 Hγ2") as "H".
  iDestruct "H" as %[<-%Excl_included%leibniz_equiv _]%auth_valid_discrete_2.
  done.
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

Lemma named_ghost_var_update γ (a1' a1 a2 : A) i1 i2 :
  named i1 (own γ (● (Excl' a1))) -∗ named i2 (own γ (◯ (Excl' a2)))
        ==∗ named i1 (own γ (● (Excl' a1'))) ∗ named i2 (own γ (◯ (Excl' a1'))).
Proof. unbundle_names; apply ghost_var_update. Qed.

End ghost_var_helpers.

Instance from_exist_left_sep {Σ} {A} (Φ : A → iProp Σ) Q :
  FromExist ((∃ a, Φ a) ∗ Q) (λ a, Φ a ∗ Q)%I .
Proof. rewrite /FromExist. iIntros "H". iDestruct "H" as (?) "(?&$)". iExists _; eauto. Qed.

  (* Extends the iExist tactic to make it easier to re-prove invariants after steps *)
Instance from_exist_left_sep_later {Σ} {A} (Φ : A → iProp Σ) Q :
  FromExist (▷ (∃ a, Φ a) ∗ Q) (λ a, ▷ Φ a ∗ Q)%I .
Proof. rewrite /FromExist. iIntros "H". iDestruct "H" as (?) "(?&$)". iExists _; eauto. Qed.

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
      (iDestruct (ghost_var_agree with pat) as %Hp; inversion_clear Hp; subst; [])
    end
  end.
