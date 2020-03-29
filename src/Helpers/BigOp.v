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

Definition Conflicting {Σ L V} (P0 P1 : L -> V -> iProp Σ) :=
  ∀ a0 v0 a1 v1,
    P0 a0 v0 -∗ P1 a1 v1 -∗ ⌜ a0 ≠ a1 ⌝.

Lemma big_sepM_disjoint_pred {Σ L V} {_ : EqDecision L} {_ : Countable L} (m0 m1 : gmap L V) (P0 P1 : L -> V -> iProp Σ) :
  Conflicting P0 P1 ->
  ( ( [∗ map] a↦v ∈ m0, P0 a v ) -∗
    ( [∗ map] a↦v ∈ m1, P1 a v ) -∗
    ⌜ m0 ##ₘ m1 ⌝ ).
Proof.
  iIntros (Hc) "H0 H1".
  iIntros (i).
  unfold option_relation.
  destruct (m0 !! i) eqn:H0; destruct (m1 !! i) eqn:H1; try solve [ iPureIntro; auto ].
  iDestruct (big_sepM_lookup with "H0") as "H0"; eauto.
  iDestruct (big_sepM_lookup with "H1") as "H1"; eauto.
  iDestruct (Hc with "H0 H1") as %Hcc.
  congruence.
Qed.


Definition big_sepML {Σ V LV} `{!EqDecision K} `{!Countable K}
                     (P : K -> V -> LV -> iProp Σ)
                     (m : gmap K V) (l : list LV) : iProp Σ :=
  ∃ lm,
    ⌜ l ≡ₚ map snd (map_to_list lm) ⌝ ∗
    [∗ map] k ↦ v;lvm ∈ m;lm, P k v lvm.

Notation "'[∗' 'maplist]' k ↦ x ; v ∈ m ; l , P" :=
  (big_sepML (λ k x v, P) m l)
  (at level 200, m, l at level 10, k, x, v at level 1, right associativity,
   format "[∗  maplist]  k ↦ x ; v  ∈  m ; l ,  P")
  : bi_scope.

Global Instance big_sepML_proper {Σ V LV} `{!EqDecision K} `{!Countable K} :
  Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (⊢)))
     ==> (=) ==> (Permutation) ==> (⊢))
         (big_sepML (Σ := Σ) (V := V) (LV := LV) (K := K)).
Proof.
  intros P0 P1 HP.
  intros m0 m Hm; subst.
  intros l0 l1 Hl.
  iIntros "Hml".
  iDestruct "Hml" as (lm) "[Hlm Hml]".
  rewrite Hl.
  iExists lm; iFrame.
  iApply big_sepM2_mono; iFrame.
  iIntros (k v lv ? ?) "H".
  iApply HP; iFrame.
Qed.

Theorem big_sepML_insert {Σ V LV} `{!EqDecision K} `{!Countable K}
                         (P : K -> V -> LV -> iProp Σ)
                         (m : gmap K V) (l : list LV)
                         k v lv :
  m !! k = None ->
  P k v lv ∗ big_sepML P m l -∗
  big_sepML P (<[k := v]> m) (lv :: l).
Proof.
  iIntros "% [Hp Hml]".
  iDestruct "Hml" as (lm) "[% Hml]".
  iDestruct (big_sepM2_lookup_1_none with "Hml") as %Hlmnone; eauto.
  iExists (<[k := lv]> lm).
  iSplitR.
  - iPureIntro.
    rewrite map_to_list_insert; eauto.
    rewrite /=.
    rewrite H0.
    reflexivity.
  - iApply big_sepM2_insert; eauto.
    iFrame.
Qed.

Theorem big_sepML_insert_app {Σ V LV} `{!EqDecision K} `{!Countable K}
                             (P : K -> V -> LV -> iProp Σ)
                             (m : gmap K V) (l : list LV)
                             k v lv :
  m !! k = None ->
  P k v lv ∗ big_sepML P m l -∗
  big_sepML P (<[k := v]> m) (l ++ [lv]).
Proof.
  iIntros "% [Hp Hml]".
  rewrite -Permutation_cons_append.
  iApply big_sepML_insert; eauto; iFrame.
Qed.

Lemma elem_of_map_list {A B} (l : list A) (f : A -> B) a :
  a ∈ map f l ->
  ∃ b, b ∈ l ∧ f b = a.
Proof.
  induction l; simpl; intros.
  - inversion H.
  - inversion H; subst; intuition.
    + exists a0; intuition. apply elem_of_list_here.
    + destruct H0 as [b H0].
      exists b. intuition.
      apply elem_of_list_further; eauto.
Qed.

Theorem big_sepML_delete {Σ V LV} `{!EqDecision K} `{!Countable K}
                         (P : K -> V -> LV -> iProp Σ)
                         (m : gmap K V) (l : list LV)
                         lv :
  big_sepML P m (lv :: l) -∗
  ∃ k v,
    ⌜ m !! k = Some v ⌝ ∗
    P k v lv ∗
    big_sepML P (delete k m) l.
Proof.
  iIntros "Hml".
  iDestruct "Hml" as (lm) "[% Hml]".
  assert (lv ∈ lv :: l) by apply elem_of_list_here.
  setoid_rewrite H in H0.
  apply elem_of_map_list in H0. destruct H0 as [[k lv0] H0].
  simpl in H0; intuition subst.
  apply elem_of_map_to_list in H1.
  iDestruct (big_sepM2_lookup_2_some with "Hml") as %[v Hmk]; eauto.
  iExists _, _.
  iSplitR; eauto.
  iDestruct (big_sepM2_delete with "Hml") as "[Hp Hml]"; eauto.
  iFrame.
  iExists _.
  iSplitR; last iFrame.
  iPureIntro.
  replace lm with (<[k := lv]> (delete k lm)) in H.
  2: {
    rewrite insert_delete.
    rewrite insert_id; eauto.
  }
  setoid_rewrite map_to_list_insert in H.
  2: apply lookup_delete.
  simpl in H.
  apply Permutation.Permutation_cons_inv in H.
  done.
Qed.
