From iris.proofmode Require Import proofmode.

Definition prefixes `{Countable A} {B : Type} (lbs ls : gmap A (list B)) :=
  ∀ x lb l, lbs !! x = Some lb -> ls !! x = Some l -> prefix lb l.

Section lemmas.
  Context `{FinMap K M}.

  Lemma map_intersection_subseteq {A : Type} (m1 m2 : M A) :
    m1 ∩ m2 ⊆ m1.
  Proof.
    rewrite !map_subseteq_spec. intros i x Hm.
    rewrite lookup_intersection_Some in Hm.
    by destruct Hm as [? _].
  Qed.

  Lemma map_intersection_difference_union {A : Type} (m1 m2 : M A) :
    m1 ∪ m2 ∖ (m2 ∩ m1) = m1 ∪ m2.
  Proof.
    apply map_eq. intros k.
    destruct (m1 !! k) as [x |] eqn:Hm1.
    { by rewrite 2!(lookup_union_Some_l _ _ _ _ Hm1). }
    rewrite 2!(lookup_union_r _ _ _ Hm1).
    by rewrite lookup_difference lookup_intersection Hm1 intersection_None_r.
  Qed.

  Lemma map_disjoint_difference_union {A : Type} (m1 m2 : M A) :
    m1 ##ₘ m2 ∖ (m2 ∩ m1).
  Proof.
    rewrite map_disjoint_spec.
    intros k x y Hm1 Hm2.
    rewrite lookup_difference lookup_intersection Hm1 intersection_Some_r in Hm2.
    by destruct (m2 !! k).
  Qed.

  Lemma lookup_alter_Some {A : Type} (f : A -> A) (m : M A) (i : K) (x : A) :
    m !! i = Some x ->
    alter f i m = <[i := f x]> m.
  Proof.
    intros Hmi.
    by rewrite -alter_insert_eq insert_id.
  Qed.

  Lemma lookup_alter_None {A : Type} (f : A -> A) (m : M A) (i : K) :
    m !! i = None ->
    alter f i m = m.
  Proof.
    intros Hmi. apply map_eq. intros j.
    by destruct (decide (i = j)); simplify_map_eq.
  Qed.

  Lemma map_Forall2_lookup_Some
    {A B : Type} (R : K → A → B → Prop) (m1 : M A) (m2 : M B) (i : K) (x1 : A) (x2 : B) :
    m1 !! i = Some x1 ->
    m2 !! i = Some x2 ->
    map_Forall2 R m1 m2 ->
    R i x1 x2.
  Proof.
    intros Hx1 Hx2 Hm1m2.
    specialize (Hm1m2 i).
    inv Hm1m2 as [x1' x2' HR Heq1 Heq2 | Heq1 Heq2].
    { rewrite Hx1 in Heq1. rewrite Hx2 in Heq2. by inv Heq1. }
    by rewrite Hx1 in Heq1.
  Qed.

  Lemma map_Forall2_size_filter
    {A B : Type}
    (P : K * A -> Prop) (Q : K * B -> Prop) `{!∀ kx, Decision (P kx)} `{!∀ ky, Decision (Q ky)}
    (m1 : M A) (m2 : M B) :
    map_Forall2 (λ k x y, P (k, x) ↔ Q (k, y)) m1 m2 ->
    size (filter (λ kx, P kx) m1) = size (filter (λ ky, Q ky) m2).
  Proof.
    revert m1 m2.
    induction m1 as [| k1 x1 m1' ? IH] using map_ind.
    - intros m2 ->%map_Forall2_empty_inv_l. rewrite !map_filter_empty !map_size_empty //.
    - intros m2 Hins%map_Forall2_insert_inv_l; last done.
      destruct Hins as (x2&m2'&->&Hnone&Hiff&Hforall).
      rewrite ?map_filter_insert.
      destruct (decide (P (k1, x1))); destruct (decide (Q (k1, x2))); try intuition.
      * rewrite ?map_size_insert_None ?IH ?map_lookup_filter_None; eauto.
      * rewrite ?delete_id //; eauto.
  Qed.

End lemmas.

Section lemmas.
  Context `{FinMapDom K M D}.
  Context `{!LeibnizEquiv D}.

  Lemma map_union_difference_union_L {A : Type} (m1 m2 m3 : M A) :
    dom m1 = dom m3 ->
    m1 ∪ m2 ∖ m3 = m1 ∪ m2.
  Proof.
    intros Hdom.
    apply map_eq. intros k.
    destruct (m1 !! k) as [x |] eqn:Hm1.
    { by rewrite 2!(lookup_union_Some_l _ _ _ _ Hm1). }
    rewrite 2!(lookup_union_r _ _ _ Hm1).
    rewrite -not_elem_of_dom Hdom not_elem_of_dom in Hm1.
    by rewrite lookup_difference Hm1.
  Qed.

  Lemma map_Forall2_forall
    {A B : Type} (R : K → A → B → Prop) (m1 : M A) (m2 : M B) :
    map_Forall2 R m1 m2 <->
    (∀ k x y, m1 !! k = Some x -> m2 !! k = Some y -> R k x y) ∧ dom m1 = dom m2.
  Proof.
    split.
    - intros Hm1m2.
      split; last by eapply map_Forall2_dom_L.
      intros k x y Hx Hy.
      by eapply map_Forall2_lookup_Some.
    - intros [HR Hdom] k.
      destruct (m1 !! k) as [x |] eqn:Hm1, (m2 !! k) as [y |] eqn:Hm2.
      + by apply Some_Forall2, HR.
      + apply elem_of_dom_2 in Hm1.
        apply not_elem_of_dom in Hm2.
        rewrite Hdom in Hm1.
        set_solver.
      + apply elem_of_dom_2 in Hm2.
        apply not_elem_of_dom in Hm1.
        rewrite Hdom in Hm1.
        set_solver.
      + apply None_Forall2.
  Qed.

  Lemma dom_eq_lookup {A : Type} {m1 m2 : M A} i :
    dom m1 = dom m2 ->
    (is_Some (m1 !! i) ∧ is_Some (m2 !! i)) ∨ (m1 !! i = None ∧ m2 !! i = None).
  Proof.
    intros Hdom.
    rewrite set_eq in Hdom.
    specialize (Hdom i).
    do 2 rewrite elem_of_dom in Hdom.
    destruct (decide (is_Some (m1 !! i))) as [? | Hm1]; first naive_solver.
    destruct (decide (is_Some (m2 !! i))) as [? | Hm2]; first naive_solver.
    rewrite -eq_None_not_Some in Hm1.
    rewrite -eq_None_not_Some in Hm2.
    by right.
  Qed.

End lemmas.

Section kmap_eq.
  Context `{FinMap K M} `{FinMap K1 M1} `{FinMap K2 M2}.

  Lemma lookup_kmap_eq_Some
    {A} (f1 : K1 -> K) `{!Inj (=) (=) f1} (f2 : K2 -> K) `{!Inj (=) (=) f2}
    (m1 : M1 A) (m2 : M2 A) i x :
    (kmap f1 m1 : M A) = kmap f2 m2 ->
    m1 !! i = Some x ->
    ∃ j, f1 i = f2 j ∧ m2 !! j = Some x.
  Proof.
    intros Hm1m2 Hx.
    rewrite map_eq_iff in Hm1m2.
    specialize (Hm1m2 (f1 i)).
    rewrite lookup_kmap Hx in Hm1m2.
    symmetry in Hm1m2.
    apply lookup_kmap_Some in Hm1m2 as (j & Hij & Hm2j); last apply _.
    by eauto.
  Qed.

  Lemma lookup_kmap_eq_None
    {A} (f1 : K1 -> K) `{!Inj (=) (=) f1} (f2 : K2 -> K) `{!Inj (=) (=) f2}
    (m1 : M1 A) (m2 : M2 A) i :
    (kmap f1 m1 : M A) = kmap f2 m2 ->
    m1 !! i = None ->
    ∀ j, f1 i = f2 j -> m2 !! j = None.
  Proof.
    intros Hm1m2 Hnone.
    rewrite map_eq_iff in Hm1m2.
    specialize (Hm1m2 (f1 i)).
    rewrite lookup_kmap Hnone in Hm1m2.
    symmetry in Hm1m2.
    by rewrite lookup_kmap_None in Hm1m2.
  Qed.

End kmap_eq.

