From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import iprop.
From Perennial.algebra Require Import big_op.
From Perennial.goose_lang Require Import lang.

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
