From stdpp Require Import gmap.

From Perennial.Helpers Require Import Integers.
From Perennial.algebra Require Import big_sepM.
From Perennial.program_proof Require Import addr.addr_proof.

Lemma default_fmap `{Countable K} `{EqDecision K} {A B:Type} (m : option (gmap K A)) (f : A -> B) :
  (default ∅ (fmap (fun bm => f <$> bm) m)) =
  f <$> (default ∅ m).
Proof.
  destruct m; simpl; eauto.
  rewrite fmap_empty; eauto.
Qed.

Lemma filter_union_ignored {K A} `{EqDecision K} `{Countable K} (m m' : gmap K A) (P : K->Prop)
                         `{! ∀ k, Decision (P k)} :
  ( ∀ k a, m' !! k = Some a -> ¬ P k ) ->
  filter (λ v, P (fst v)) m = filter (λ v, P (fst v)) (m' ∪ m).
Proof.
  intros.
  apply map_eq; intros i.
  destruct (decide (P i)).
  2: { rewrite !map_filter_lookup_key_notin; eauto. }
  rewrite map_filter_lookup_key_in; eauto.
  rewrite map_filter_lookup_key_in; eauto.
  rewrite lookup_union_r; eauto.
  destruct (m' !! i) eqn:He; eauto.
  exfalso. eapply H1; eauto.
Qed.

Lemma filter_union_gmap_addr_by_block_ignored {A} (m m' : gmap addr A) (P : u64->Prop)
                         `{! ∀ k, Decision (P k)} :
  ( ∀ k a, m' !! k = Some a -> ¬ P (fst k) ) ->
  filter (λ v, P (fst v)) (gmap_addr_by_block m) = filter (λ v, P (fst v)) (gmap_addr_by_block (m' ∪ m)).
Proof.
  intros.
  apply map_eq; intros i.
  destruct (decide (P i)).
  2: { rewrite ?map_filter_lookup_key_notin; eauto. }
  rewrite map_filter_lookup_key_in; eauto.
  rewrite map_filter_lookup_key_in; eauto.
  rewrite /gmap_addr_by_block.
  destruct (gmap_uncurry m !! i) eqn:He.
  2: {
    symmetry.
    erewrite lookup_gmap_uncurry_None in He.
    erewrite lookup_gmap_uncurry_None. intros j. specialize (He j).
    specialize (H0 (i, j)). simpl in *.
    rewrite lookup_union_r; eauto.
    destruct (m' !! (i, j)) eqn:Hee; eauto. exfalso. eapply H0; eauto.
  }

  destruct (gmap_uncurry (m' ∪ m) !! i) eqn:He2.
  2: {
    exfalso.
    erewrite lookup_gmap_uncurry_None in He2.
    apply gmap_uncurry_non_empty in He as He'. apply map_choose in He'. destruct He' as [j [x He']].
    specialize (He2 j). rewrite lookup_union_r in He2.
    2: { destruct (m' !! (i, j)) eqn:Hee; eauto. exfalso. eapply H0; eauto. }
    rewrite -lookup_gmap_uncurry in He2. rewrite He /= in He2. congruence.
  }

  f_equal.
  apply map_eq.
  intros j.

  replace (g !! j) with (m !! (i, j)).
  2: { rewrite -lookup_gmap_uncurry. rewrite He. done. }

  replace (g0 !! j) with ((m' ∪ m) !! (i, j)).
  2: { rewrite -lookup_gmap_uncurry. rewrite He2. done. }

  rewrite lookup_union_r; eauto.
  destruct (m' !! (i, j)) eqn:Hee; eauto. exfalso. eapply H0; eauto.
Qed.
