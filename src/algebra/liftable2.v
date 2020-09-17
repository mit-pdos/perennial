From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From Perennial.Helpers Require Import NamedProps ipm gset.
From Perennial.algebra Require Import big_op.

Set Default Proof Using "Type".

Section bi.
  Context {PROP:bi}.
  Context `{BiInternalEq PROP}.

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
      ∃ m, "%Hdom" ∷ ⌜dom _ m = d⌝ ∗
           "Hm" ∷ ([∗ map] a↦v ∈ m, mapsto1 a v) ∗
           "Hmapsto2" ∷
           ∀ mapsto2, ⌜Conflicting mapsto2⌝ -∗
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

  Instance star_lifted `{!Lifted P d1, !Lifted Q d2} `{BiAffine PROP} :
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
    apply H1.
  Qed.

End bi.
