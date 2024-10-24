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
    by rewrite -alter_insert insert_id.
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

End lemmas.

Section lemmas.
  Context `{FinMapDom K M D}.
  Context `{!LeibnizEquiv D}.

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

End lemmas.
