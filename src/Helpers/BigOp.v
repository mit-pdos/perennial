From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import iprop.
From Perennial.goose_lang Require Import lang.

Lemma big_sepM2_lookup_1_some
    (PROP : bi) (K : Type) (EqDecision0 : EqDecision K) (H : Countable K)
    (A B : Type) (Φ : K → A → B → PROP) (m1 : gmap K A) (m2 : gmap K B)
    (i : K) (x1 : A)
    (_ : forall x2 : B, Absorbing (Φ i x1 x2)) :
  m1 !! i = Some x1 ->
    ⊢ ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) -∗
        ⌜∃ x2, m2 !! i = Some x2⌝.
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
    ⊢ ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) -∗
        ⌜∃ x1, m1 !! i = Some x1⌝.
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
    ⊢ ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) -∗
        ⌜m2 !! i = None⌝.
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
    ⊢ ( [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ) -∗
        ⌜m1 !! i = None⌝.
Proof.
  case_eq (m1 !! i); auto.
  iIntros (? ? ?) "H".
  iDestruct (big_sepM2_lookup_1 with "H") as (x1) "[% _]"; eauto; congruence.
Qed.

Theorem heap_array_to_list {Σ} {A} l0 (vs: list A) (P: loc -> A -> iProp Σ) :
  ([∗ map] l↦v ∈ heap_array l0 vs, P l v) ⊣⊢
  ([∗ list] i↦v ∈ vs, P (l0 +ₗ i) v).
Proof.
  (iInduction (vs) as [| v vs] "IH" forall (l0)).
  - simpl.
    rewrite big_sepM_empty.
    auto.
  - simpl.
    rewrite loc_add_0.
    rewrite big_sepM_union.
    { rewrite big_sepM_singleton.
      setoid_rewrite loc_add_Sn.
      iSpecialize ("IH" $! (l0 +ₗ 1)).
      iSplit.
      + iIntros "($&Hm)".
        iApply ("IH" with "Hm").
      + iIntros "($&Hl)".
        iApply ("IH" with "Hl").
    }
    symmetry.
    apply heap_array_map_disjoint; intros.
    apply (not_elem_of_dom (D := gset loc)).
    rewrite dom_singleton elem_of_singleton loc_add_assoc.
    intros ?%loc_add_ne; auto; lia.
Qed.

Theorem big_sepL_impl {Σ} A (f g: nat -> A -> iProp Σ) (l: list A) :
  (forall i x, f i x -∗ g i x) ->
  ([∗ list] i↦x ∈ l, f i x) -∗
  ([∗ list] i↦x ∈ l, g i x).
Proof.
  intros Himpl.
  apply big_opL_gen_proper; auto.
  typeclasses eauto.
Qed.
