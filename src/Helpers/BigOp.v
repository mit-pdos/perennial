From iris.proofmode Require Import coq_tactics reduction.
From iris.algebra Require Import auth gmap frac agree excl vector.
From Perennial.goose_lang Require Import proofmode.

Lemma big_sepM2_lookup_1_some
    (PROP : bi) (K : Type) (EqDecision0 : EqDecision K) (H : Countable K)
    (A B : Type) (Φ : K → A → B → PROP) (m1 : gmap K A) (m2 : gmap K B)
    (i : K) (x1 : A)
    (_ : forall x2 : B, Absorbing (Φ i x1 x2)) :
  m1 !! i = Some x1 ->
    ( ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) -∗
        ⌜∃ x2, m2 !! i = Some x2⌝ )%I.
Proof.
  intros.
  iIntros "H".
  iDestruct (big_sepM2_lookup_1 with "H") as (x2) "[% _]"; eauto.
Qed.

Lemma big_sepM2_lookup_2_some
    (PROP : bi) (K : Type) (EqDecision0 : EqDecision K) (H : Countable K)
    (A B : Type) (Φ : K → A → B → PROP) (m1 : gmap K A) (m2 : gmap K B)
    (i : K) (x2 : B)
    (_ : forall x1 : A, Absorbing (Φ i x1 x2)) :
  m2 !! i = Some x2 ->
    ( ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) -∗
        ⌜∃ x1, m1 !! i = Some x1⌝ )%I.
Proof.
  intros.
  iIntros "H".
  iDestruct (big_sepM2_lookup_2 with "H") as (x1) "[% _]"; eauto.
Qed.

Lemma big_sepM2_lookup_1_none
    (PROP : bi) (K : Type) (EqDecision0 : EqDecision K) (H : Countable K)
    (A B : Type) (Φ : K → A → B → PROP) (m1 : gmap K A) (m2 : gmap K B)
    (i : K)
    (_ : forall (x1 : A) (x2 : B), Absorbing (Φ i x1 x2)) :
  m1 !! i = None ->
    ( ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) -∗
        ⌜m2 !! i = None⌝ )%I.
Proof.
  case_eq (m2 !! i); auto.
  iIntros (? ? ?) "H".
  iDestruct (big_sepM2_lookup_2 with "H") as (x2) "[% _]"; eauto; congruence.
Qed.

Lemma big_sepM2_lookup_2_none
    (PROP : bi) (K : Type) (EqDecision0 : EqDecision K) (H : Countable K)
    (A B : Type) (Φ : K → A → B → PROP) (m1 : gmap K A) (m2 : gmap K B)
    (i : K)
    (_ : forall (x1 : A) (x2 : B), Absorbing (Φ i x1 x2)) :
  m2 !! i = None ->
    ( ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) -∗
        ⌜m1 !! i = None⌝ )%I.
Proof.
  case_eq (m1 !! i); auto.
  iIntros (? ? ?) "H".
  iDestruct (big_sepM2_lookup_1 with "H") as (x1) "[% _]"; eauto; congruence.
Qed.
