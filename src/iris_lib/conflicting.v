From iris.proofmode Require Import tactics.

Set Default Proof Using "Type".

Section bi.
Context {PROP:bi}.

(* TODO: logically equivalent to say P0 a v0 -∗ P1 a v1 -∗ False (with decidable
equality on A) *)

Class ConflictsWith {L V} (P0 P1 : L -> V -> PROP) := conflicts_with :
  ∀ a0 v0 a1 v1,
    P0 a0 v0 -∗ P1 a1 v1 -∗ ⌜ a0 ≠ a1 ⌝.

Lemma big_sepM_disjoint_pred {L V} {P0 P1 : L -> V -> PROP} `{!EqDecision L} `{!Countable L}
  `{!∀ l v, Absorbing (P0 l v)}
  `{!∀ l v, Absorbing (P1 l v)}
  `{!ConflictsWith P0 P1}
  (m0 m1 : gmap L V) :
  ( ( [∗ map] a↦v ∈ m0, P0 a v ) -∗
    ( [∗ map] a↦v ∈ m1, P1 a v ) -∗
    ⌜ m0 ##ₘ m1 ⌝ ).
Proof.
  iIntros "H0 H1".
  iIntros (i).
  unfold option_relation.
  destruct (m0 !! i) eqn:He; destruct (m1 !! i) eqn:H1; try solve [ iPureIntro; auto ].
  iDestruct (big_sepM_lookup with "H0") as "H0"; eauto.
  iDestruct (big_sepM_lookup with "H1") as "H1"; eauto.
  iDestruct (conflicts_with with "H0 H1") as %Hcc.
  congruence.
Qed.

Class Conflicting {L V} (P: L → V → PROP) := conflicting : ConflictsWith P P.

Instance conflicting_conflicts_with `(P: L → V → PROP) `{H: !ConflictsWith P P} :
  Conflicting P.
Proof. exact H. Qed.

End bi.
