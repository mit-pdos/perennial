From iris.proofmode Require Import proofmode.

Section fin_set.
  Context `{FinSet A C}.
  Implicit Types X Y : C.

  Lemma size_empty_iff_L `{!LeibnizEquiv C} X : size X = 0 ↔ X = ∅.
  Proof. unfold_leibniz. apply size_empty_iff. Qed.

  Lemma size_non_empty_iff_L `{!LeibnizEquiv C} X : size X ≠ 0 ↔ X ≠ ∅.
  Proof. unfold_leibniz. apply size_non_empty_iff. Qed.

  Lemma filter_subseteq_impl X (P Q : A → Prop) `{!∀ x, Decision (P x)} `{!∀ x, Decision (Q x)} :
    (∀ x, P x -> Q x) ->
    filter P X ⊆ filter Q X.
  Proof. set_solver. Qed.

  Lemma filter_subseteq_mono X Y (P : A -> Prop) `{!∀ x, Decision (P x)} :
    X ⊆ Y ->
    filter P X ⊆ filter P Y.
  Proof. set_solver. Qed.

End fin_set.
