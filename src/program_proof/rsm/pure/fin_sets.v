From iris.proofmode Require Import proofmode.

Section fin_set.
  Context `{FinSet A C}.
  Implicit Types X Y : C.

  Lemma size_empty_iff_L `{!LeibnizEquiv C} X : size X = 0 ↔ X = ∅.
  Proof. unfold_leibniz. apply size_empty_iff. Qed.
  Lemma size_non_empty_iff_L `{!LeibnizEquiv C} X : size X ≠ 0 ↔ X ≠ ∅.
  Proof. unfold_leibniz. apply size_non_empty_iff. Qed.

End fin_set.
