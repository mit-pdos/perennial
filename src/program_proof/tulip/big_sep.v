From iris.algebra Require Export big_op.
From iris.proofmode Require Import proofmode.
From Perennial.Helpers Require Import ipm.
From Perennial.program_proof.rsm Require Import big_sep.

Open Scope Z_scope.

(* TODO: move *)
Section big_sepS_cprod.
  Context {PROP : bi}.
  Implicit Types (P Q : PROP).
  Implicit Types (A : Type).

  Lemma big_sepS_gset_cprod `{Countable A} `{Countable B}
    `{!BiAffine PROP} (Φ: A → B → PROP) (ma: gset A) (mb : gset B) :
    ([∗ set] xy ∈ gset_cprod ma mb, Φ xy.1 xy.2) ⊢ ([∗ set] x ∈ ma, [∗ set] y ∈ mb, Φ x y).
  Proof.
    iIntros "H".
    unshelve (iDestruct (big_sepS_partition_1 _ (gset_cprod ma mb)
                 ma
                 (λ ab a, fst ab = a)
                with "H") as "H").
    { intros (a&b) => /=. apply _. }
    { intros (a&b) a1 a2 => /=. congruence. }
    iApply (big_sepS_mono with "H").
    iIntros (a Hina) "H".
    unshelve (iDestruct (big_sepS_partition_1 _ _
                 mb
                 (λ ab b, snd ab = b)
                with "H") as "H").
    { intros (a'&b) => /=. apply _. }
    { intros (a'&b) a1 a2 => /=. congruence. }
    iApply (big_sepS_mono with "H").
    iIntros (b Hinb) "H".
    iAssert ([∗ set] x ∈ {[(a, b)]}, Φ x.1 x.2)%I with "[H]" as "H".
    { iExactEq "H". f_equal. apply gset_leibniz. intros (a'&b'). set_unfold. naive_solver. }
    rewrite big_sepS_singleton.
    auto.
  Qed.

  Lemma big_sepS_gset_cprod' `{Countable A} `{Countable B}
    `{!BiAffine PROP} (Φ: A * B → PROP) (ma: gset A) (mb : gset B) :
    ([∗ set] xy ∈ gset_cprod ma mb, Φ xy) ⊢ ([∗ set] x ∈ ma, [∗ set] y ∈ mb, Φ (x, y)).
  Proof.
    iIntros "H".
    iApply (big_sepS_gset_cprod (λ a b, Φ (a, b))).
    iApply (big_sepS_mono with "H").
    iIntros ((?&?) ?) => //.
  Qed.

End big_sepS_cprod.
