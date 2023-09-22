From Perennial.program_proof Require Import proof_prelude.

Section fin_maps.
  Context `{FinMap K M}.

  Lemma map_intersection_subseteq {A : Type} (m1 m2 : M A) :
    m1 ∩ m2 ⊆ m1.
  Proof using EqDecision0 H H0 H1 H2 H3 H4 H5 H6 K M.
    rewrite !map_subseteq_spec. intros i x Hm.
    rewrite lookup_intersection_Some in Hm.
    by destruct Hm as [? _].
  Qed.

  Lemma lookup_alter_Some {A : Type} (f : A -> A) (m : M A) (i : K) (x : A) :
    m !! i = Some x ->
    alter f i m = <[i := f x]> m.
  Proof using EqDecision0 H H0 H1 H2 H3 H4 H5 H6 K M.
    intros Hmi.
    by rewrite -alter_insert insert_id.
  Qed.

  Lemma lookup_alter_None {A : Type} (f : A -> A) (m : M A) (i : K) :
    m !! i = None ->
    alter f i m = m.
  Proof using EqDecision0 H H0 H1 H2 H3 H4 H5 H6 K M.
    intros Hmi. apply map_eq. intros j.
    by destruct (decide (i = j)); simplify_map_eq.
  Qed.

End fin_maps.
