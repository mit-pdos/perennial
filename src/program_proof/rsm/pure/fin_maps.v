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

End lemmas.
