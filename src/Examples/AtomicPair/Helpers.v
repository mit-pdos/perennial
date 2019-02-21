From iris.algebra Require Import auth.
Require Export CSL.Refinement ExMach.WeakestPre.
Unset Implicit Arguments.

(* TODO: move *)
Section ghost_var_helpers.
Context {A: ofeT} `{@LeibnizEquiv _ A.(ofe_equiv)} `{OfeDiscrete A}.
Context {Σ} {Hin: inG Σ (authR (optionUR (exclR A)))}.

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
End ghost_var_helpers.

  (* Extends the iExist tactic to make it easier to re-prove invariants after steps *)
Instance from_exist_left_sep {Σ} {A} (Φ : A → iProp Σ) Q :
  FromExist (▷ (∃ a, Φ a) ∗ Q) (λ a, ▷ Φ a ∗ Q)%I .
Proof. rewrite /FromExist. iIntros "H". iDestruct "H" as (?) "(?&$)". iExists _; eauto. Qed.

