From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From Perennial.Helpers Require Import NamedProps ipm gset.
From Perennial.algebra Require Import big_op liftable.

Set Default Proof Using "Type".
Set Default Goal Selector "!".

Section bi.
  Context {PROP:bi}.

  Context `{L : Type}.
  Context `{V : Type}.
  Context `{!EqDecision L}.
  Context `{!Countable L}.

  Implicit Types (mapsto: L → V → PROP).
  Implicit Types (P: (L → V → PROP) → PROP).
  Implicit Types (m: gmap L V) (d: gset L).

  Definition HoldsAt P mapsto1 d : PROP :=
    (∃ m,
      "%Hdom" ∷ <affine> ⌜dom _ m = d⌝ ∗
      "Hm" ∷ ([∗ map] a↦v ∈ m, mapsto1 a v) ∗
      "Hmapsto2" ∷
      ∀ mapsto2, (([∗ map] a↦v ∈ m, mapsto2 a v) -∗ P mapsto2))%I.

  Theorem liftable_holds_elim P `{!Liftable P} mapsto1 `{!Conflicting mapsto1} :
    P mapsto1 -∗ ∃ d, HoldsAt P mapsto1 d.
  Proof.
    iIntros "HP".
    iDestruct (liftable with "HP") as (m) "[Hm HP]".
    iExists (dom _ m).
    iExists m. iSplit; first by auto.
    iFrame.
  Qed.

  Theorem HoldsAt_weaken_wand P Q mapsto1 d :
    (∀ mapsto, P mapsto -∗ Q mapsto) -∗
    HoldsAt P mapsto1 d -∗ HoldsAt Q mapsto1 d.
  Proof.
    iIntros "Himpl HP".
    iNamed "HP".
    iExists m. iSplit; first by auto. iFrame.
    iIntros (mapsto2) "Hm".
    iApply "Himpl".
    iApply "Hmapsto2".
    iFrame.
  Qed.

  (* weaken HoldsAt_weaken_wand to state the implication in Coq rather than
  inside the Iris logic *)
  Theorem HoldsAt_weaken P Q mapsto1 d :
    (∀ mapsto, P mapsto ⊢ Q mapsto) →
    HoldsAt P mapsto1 d -∗ HoldsAt Q mapsto1 d.
  Proof.
    iIntros (Himpl) "HP".
    iApply (HoldsAt_weaken_wand with "[] HP").
    iIntros (?).
    iApply Himpl.
  Qed.

  (* if we don't care about the predicate, we can extract just the mapsto part
  of a HoldsAt (and since this drops P we assume the bi is affine) *)
  Theorem HoldsAt_elim_big_sepM `{!BiAffine PROP} P mapsto1 d :
    HoldsAt P mapsto1 d -∗
    ∃ m, ⌜dom _ m = d⌝ ∗ [∗ map] a↦v ∈ m, mapsto1 a v.
  Proof.
    iNamed 1.
    iExists m. iSplit; first by auto. iFrame.
  Qed.

  Theorem sep_holds_at_combine `{!BiAffine PROP} P Q mapsto1 `{!Conflicting mapsto1} d1 d2 :
    HoldsAt P mapsto1 d1 ∗ HoldsAt Q mapsto1 d2 -∗
    HoldsAt (fun mapsto => P mapsto ∗ Q mapsto)%I mapsto1 (d1 ∪ d2) ∗ ⌜d1 ## d2⌝.
  Proof.
    iIntros "[HP HQ]".
    iDestruct "HP" as (m1) "(<-&Hm1&Hmapsto1)".
    iDestruct "HQ" as (m2) "(<-&Hm2&Hmapsto2)".
    iDestruct (big_sepM_disjoint_pred with "Hm1 Hm2") as %Hdisjoint.
    iSplit; last first.
    { iPureIntro.
      apply map_disjoint_dom; auto. }
    iExists (m1 ∪ m2).
    iSplit.
    { rewrite dom_union_L.
      auto. }
    rewrite big_sepM_union //.
    iFrame "Hm1 Hm2".
    iIntros (?) "Hm".
    iDestruct (big_sepM_union with "Hm") as "[Hm1 Hm2]"; auto.
    iSplitL "Hmapsto1 Hm1".
    - iApply "Hmapsto1"; iFrame "%∗".
    - iApply "Hmapsto2"; iFrame "%∗".
    Grab Existential Variables.
    assumption.
  Qed.

  Theorem sep_holds_at_split `{!BiAffine PROP} P Q mapsto1 d `{!Conflicting mapsto1} `{!Liftable P, !Liftable Q}  :
    HoldsAt (fun mapsto => P mapsto ∗ Q mapsto)%I mapsto1 d -∗
    ∃ d1 d2, ⌜d1 ## d2 ∧ d = d1 ∪ d2⌝ ∗ HoldsAt P mapsto1 d1 ∗ HoldsAt Q mapsto1 d2.
  Proof.
    iNamed 1.
    (* XXX: we can't prove this, we need to swap an exists domain with the
    forall mapsto *)
  Abort.

  Theorem holds_at_empty P mapsto1 `{!Conflicting mapsto1} :
    HoldsAt P mapsto1 ∅ -∗ P mapsto1.
  Proof.
    iIntros "H"; iNamed "H".
    apply dom_empty_inv_L in Hdom; subst.
    setoid_rewrite big_sepM_empty.
    iApply "Hmapsto2"; auto.
  Qed.

  Theorem independent_holds_empty (P:PROP) mapsto1 :
    P -∗ HoldsAt (λ _, P) mapsto1 ∅.
  Proof.
    iIntros "HP".
    iExists ∅.
    rewrite dom_empty_L.
    iSplit; first by auto.
    rewrite big_sepM_empty left_id.
    iIntros (?).
    rewrite big_sepM_empty; iIntros "_".
    iFrame.
  Qed.

  Theorem exists_holds_at T Φ mapsto1 (x:T) d :
    HoldsAt (Φ x) mapsto1 d -∗
    HoldsAt (fun mapsto => ∃ x, Φ x mapsto)%I mapsto1 d.
  Proof.
    iIntros "H"; iNamed "H".
    iExists m.
    iSplit; first by auto.
    iFrame.
    iIntros (?) "Hm".
    iExists (x).
    iApply "Hmapsto2"; auto.
  Qed.

  Theorem singleton_holds_at mapsto a v :
    mapsto a v -∗ HoldsAt (fun mapsto => mapsto a v) mapsto {[a]}.
  Proof.
    iIntros "Ha".
    iExists {[a := v]}.
    rewrite dom_singleton_L.
    iSplit; first by auto.
    setoid_rewrite big_sepM_singleton.
    iFrame "Ha".
    iIntros (?) "$".
  Qed.

  Lemma dom_map_to_list m :
    dom (gset L) m = list_to_set (map_to_list m).*1.
  Proof.
    induction m as [|l v m] using map_ind.
    - rewrite dom_empty_L map_to_list_empty //.
    - rewrite map_to_list_insert //.
      rewrite dom_insert_L.
      rewrite fmap_cons /=.
      rewrite -IHm //.
  Qed.

  Lemma dom_singleton_inv m a :
    dom (gset _) m = {[a]} →
    ∃ v, m = {[a := v]}.
  Proof.
    intros.
    assert (∃ v, map_to_list m = [(a, v)]).
    { rewrite dom_map_to_list in H.
      generalize dependent (map_to_list m); intros es.
      destruct es; simpl.
      - intros H%(f_equal elements).
        rewrite elements_empty elements_singleton in H; congruence.
      - intros.
        destruct es.
        + simpl in H.
          rewrite right_id_L in H.
          destruct p; simpl in *.
          apply (f_equal elements) in H.
          rewrite !elements_singleton in H.
          inversion H; eauto.
        + (* this destruct is the wrong strategy; list_to_set could in principle have many duplicates *)
          admit.
    }
    rewrite -(list_to_map_to_list m).
    destruct H0 as [v ->].
    exists v; auto.
  Admitted.

  Theorem map_singleton_holds_at m Φ mapsto1 :
    ([∗ map] a↦v∈m, HoldsAt (Φ a v) mapsto1 {[a]}) -∗
    HoldsAt (fun mapsto => [∗ map] a ↦ v ∈ m, (Φ a v mapsto))%I mapsto1 (dom _ m).
  Proof.
    iIntros "Hm".
    iInduction m as [|l v m] "IH" using map_ind.
    - iExists ∅.
      iSplit; first by auto.
      rewrite !big_sepM_empty left_id.
      setoid_rewrite big_sepM_empty.
      by iIntros (?) "_".
    - setoid_rewrite big_sepM_insert; auto.
      iDestruct "Hm" as "[Hl Hm']".
      iNamed "Hl".
      apply dom_singleton_inv in Hdom as [v' ->].
      setoid_rewrite big_sepM_singleton.
      iDestruct ("IH" with "Hm'") as (m') "(%Hdom'&Hm'&Hmapsto2')".
      iExists (<[l:=v']> m').
      iSplitR; [ iPureIntro | ].
      { rewrite !dom_insert_L; congruence. }
      assert (m' !! l = None).
      { apply not_elem_of_dom. rewrite Hdom'. apply not_elem_of_dom.
        auto. }
      rewrite big_sepM_insert //.
      iFrame.
      iIntros (?) "Hm".
      rewrite !big_sepM_insert //.
      iDestruct "Hm" as "[Hl Hm']".
      iDestruct ("Hmapsto2" with "Hl") as "$".
      iApply "Hmapsto2'"; auto.
  Qed.

End bi.
