From iris.proofmode Require Import proofmode.

Section lemmas.
  Context `{FinMap K M}.

  Lemma map_intersection_subseteq {A : Type} (m1 m2 : M A) :
    m1 ∩ m2 ⊆ m1.
  Proof.
    rewrite !map_subseteq_spec. intros i x Hm.
    rewrite lookup_intersection_Some in Hm.
    by destruct Hm as [? _].
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
