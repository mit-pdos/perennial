From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From Perennial.Helpers Require Import NamedProps ipm gset.
From Perennial.algebra Require Import big_op.

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

  Class Lifted P d := lifted :
      ∀ mapsto1, Conflicting mapsto1 →
    P mapsto1 -∗
      ∃ m, "%Hdom" ∷ <affine> ⌜dom _ m = d⌝ ∗
           "Hm" ∷ ([∗ map] a↦v ∈ m, mapsto1 a v) ∗
           "Hmapsto2" ∷
           ∀ mapsto2, <affine> ⌜Conflicting mapsto2⌝ -∗
                       (([∗ map] a↦v ∈ m, mapsto2 a v) -∗ P mapsto2).

  Theorem lifted_acc `{!Lifted P d} mapsto1 mapsto2 `{!Conflicting mapsto1, !Conflicting mapsto2} :
    Conflicting mapsto1 →
    Conflicting mapsto2 →
    P mapsto1 -∗
      ∃ m, ⌜dom _ m = d⌝ ∗
           ([∗ map] a↦v ∈ m, mapsto1 a v) ∗
           (([∗ map] a↦v ∈ m, mapsto2 a v) -∗ P mapsto2).
  Proof.
    iIntros (??) "HP".
    iApply lifted in "HP"; iNamed "HP".
    iExists m; iFrame "%∗".
    iSplitR; first by auto.
    iIntros "Hm".
    iApply "Hmapsto2"; iFrame "%∗".
  Qed.

  Theorem lifted_strong P d :
    (∃ Q m,
        ∀ mapsto, Conflicting mapsto →
              P mapsto ⊣⊢ Q ∗ <affine> ⌜dom _ m = d⌝ ∗ ([∗ map] a↦v ∈ m, mapsto a v)) →
    Lifted P d.
  Proof.
    destruct 1 as (Q&m&Hequiv).
    iIntros (mapsto ?) "HP".
    iExists m; iFrame "%∗".
    iDestruct (Hequiv with "HP") as "(HQ&%Hdom&Hm)".
    iFrame "%∗".
    iIntros (mapsto2 ?) "Hm".
    iApply Hequiv; iFrame "%∗".
  Qed.

  Global Instance Lifted_proper :
    Proper (pointwise_relation _ (⊣⊢) ==> (=) ==> (↔)) Lifted.
  Proof.
    intros P1 P2 ? d d2 <-.
    rewrite /Lifted. setoid_rewrite H. auto.
  Qed.

  Global Instance star_lifted `{!Lifted P d1, !Lifted Q d2} `{BiAffine PROP} :
    Lifted (fun mapsto => P mapsto ∗ Q mapsto)%I (d1 ∪ d2).
  Proof.
    rewrite /Lifted.
    iIntros (mapsto ?).
    rewrite (lifted (P:=P)) (lifted (P:=Q)).
    iIntros "[Hm1 Hm2]".
    iDestruct "Hm1" as (m1) "(%Hdom1&Hm1&Hm1_acc)".
    iDestruct "Hm2" as (m2) "(%Hdom2&Hm2&Hm2_acc)".
    iExists (m1 ∪ m2).
    iDestruct (big_sepM_disjoint_pred with "Hm1 Hm2") as %Hdisjoint.
    assert (d1 ## d2) as Hdom_disjoint.
    { apply map_disjoint_dom in Hdisjoint.
      rewrite -Hdom1 -Hdom2 //. }
    iSplit.
    { iPureIntro.
      rewrite dom_union_L; congruence. }
    rewrite big_sepM_union //; iFrame.
    iIntros (mapsto2 Hconflict) "Hm12".
    rewrite big_sepM_union //.
    iDestruct "Hm12" as "[Hm1 Hm2]".
    iSplitL "Hm1 Hm1_acc".
    - iApply "Hm1_acc"; iFrame "%∗".
    - iApply "Hm2_acc"; iFrame "%∗".

    Grab Existential Variables.
    assumption.
  Qed.

  Global Instance independent_lifted (P:PROP) :
    Lifted (fun _ => P) ∅.
  Proof.
    apply lifted_strong.
    exists P, ∅; intros.
    rewrite big_sepM_empty right_id.
    rewrite dom_empty_L.
    iSplit; auto.
    iIntros "[$ _]".
  Qed.

  Global Instance exists_lifted T Φ d :
    (forall x, Lifted (Φ x) d) ->
    Lifted (fun h => ∃ (x : T), Φ x h)%I d.
  Proof.
    rewrite /Lifted; intros.
    iDestruct 1 as (x) "HΦ".
    iDestruct (H with "HΦ") as "H"; iNamed "H".
    iExists m.
    iFrame "%∗".
    iIntros (??) "Hm".
    iExists x.
    iApply "Hmapsto2"; auto.
  Qed.

  Global Instance singleton_lifted a v :
    Lifted (fun mapsto => mapsto a v) {[a]}.
  Proof.
    apply lifted_strong.
    exists emp%I, {[a := v]}.
    intros.
    rewrite big_sepM_singleton.
    rewrite dom_singleton_L.
    rewrite left_id.
    iSplit; by [iIntros "$" | iIntros "[_ $]"].
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

  Global Instance map_singleton_lifted m Φ :
    (∀ a v, Lifted (Φ a v) {[a]}) →
    Lifted (fun mapsto => [∗ map] a ↦ v ∈ m, (Φ a v mapsto))%I (dom _ m).
  Proof.
    intros LiftedΦ.
    iIntros (??) "Hm".
    iInduction m as [|l v m] "IH" using map_ind.
    - iExists ∅.
      setoid_rewrite big_sepM_empty.
      eauto with iFrame.
    - setoid_rewrite big_sepM_insert; auto.
      iDestruct "Hm" as "[HΦ Hm]".
      iDestruct (LiftedΦ with "HΦ") as (ml) "(%Hdom & Hml & HΦ)".
      apply dom_singleton_inv in Hdom as [v' ->].
      setoid_rewrite big_sepM_singleton.
      iDestruct ("IH" with "Hm") as (m') "(%Hdom'&Hm'&Hmapsto2)".
      iExists (<[l:=v']> m').
      iSplitR; [ iPureIntro | ].
      { rewrite !dom_insert_L; congruence. }
      assert (m' !! l = None).
      { apply not_elem_of_dom. rewrite Hdom'. apply not_elem_of_dom.
        auto. }
      rewrite big_sepM_insert //.
      iFrame.
      iIntros (??) "Hm".
      rewrite !big_sepM_insert //.
      iDestruct "Hm" as "[Hl Hm']".
      iDestruct ("HΦ" with "[% //] Hl") as "$".
      iApply "Hmapsto2"; auto.
  Qed.

End bi.
