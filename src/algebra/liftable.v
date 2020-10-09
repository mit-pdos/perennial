From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import iprop.
From Perennial.algebra Require Import big_op.

Section liftable.

  Context `{PROP:bi} `{!BiAffine PROP} `{!BiPureForall PROP}.
  Context {L V: Type} `{!EqDecision L} `{!Countable L}.

  Set Default Proof Using "BiAffine0".

  Class Liftable (P : (L -> V -> PROP) -> PROP) := liftable :
    ∀ mapsto1,
      Conflicting mapsto1 ->
      P mapsto1 -∗
      ∃ (m : gmap L V),
        ([∗ map] a ↦ v ∈ m, mapsto1 a v) ∗
           ∀ mapsto2, ([∗ map] a ↦ v ∈ m, mapsto2 a v) -∗ P mapsto2.

  Theorem liftable_sep P Q : Liftable P → Liftable Q → Liftable (fun h => P h ∗ Q h)%I.
  Proof using BiAffine0 BiPureForall0.
    unfold Liftable in *.
    intros LiftableP LiftableQ.
    iIntros (??) "[Hp Hq]".
    iDestruct (LiftableP with "Hp") as (mp) "[Hpm Hpi]"; eauto.
    iDestruct (LiftableQ with "Hq") as (mq) "[Hqm Hqi]"; eauto.
    iExists (mp ∪ mq).
    iDestruct (big_sepM_disjoint_pred with "[$Hpm] [$Hqm]") as %?; eauto.
    iDestruct (big_sepM_union with "[$Hpm $Hqm]") as "Hm"; eauto.
    iFrame.
    iIntros (h2) "Hm".
    rewrite big_sepM_union; eauto.
    iDestruct "Hm" as "[Hpm Hqm]".
    iDestruct ("Hpi" with "Hpm") as "Hp".
    iDestruct ("Hqi" with "Hqm") as "Hq".
    iFrame.
  Unshelve.
    all: eauto.
  Qed.

  Global Instance star_liftable `{Liftable P} `{Liftable Q} : Liftable (fun h => P h ∗ Q h)%I.
  Proof using BiAffine0 BiPureForall0.
    apply liftable_sep; auto.
  Qed.

  Global Instance pure_liftable P : Liftable (fun h => ⌜ P ⌝)%I.
  Proof.
    unfold Liftable in *.
    iIntros (??) "%".
    iExists ∅.
    rewrite big_sepM_empty.
    iSplit; try done.
    iIntros (h2) "Hm".
    iPureIntro. auto.
  Qed.

  Global Instance exists_liftable T P :
    (forall x, Liftable (P x)) ->
    Liftable (fun h => ∃ (x : T), P x h)%I.
  Proof.
    unfold Liftable in *.
    iIntros (H h ?) "H".
    iDestruct "H" as (x) "H".
    iDestruct (H with "H") as (m) "(Hm & Hx)"; eauto.
    iExists _. iFrame.
    iIntros (h2) "Hm".
    iDestruct ("Hx" with "Hm") as "Hp".
    iExists _. iFrame.
  Qed.

  Global Instance map_liftable `{EqDecision LM} `{Countable LM} `(m : gmap LM VM) P :
    (forall a v, Liftable (P a v)) ->
    Liftable (fun h => [∗ map] a ↦ v ∈ m, (P a v h))%I.
  Proof using BiAffine0 BiPureForall0.
    intros.
    unfold Liftable.
    iIntros (??) "Hm".
    iInduction m as [|i x m] "IH" using map_ind.
    - iExists ∅.
      repeat rewrite big_sepM_empty.
      iFrame.
      iIntros.
      repeat rewrite big_sepM_empty.
      done.
    - iDestruct (big_sepM_insert with "Hm") as "[Hx Hm]"; auto.
      iDestruct ("IH" with "Hm") as (m0) "[Hm0 Hr0]".
      specialize (H0 i x).
      unfold Liftable in H0.
      iPoseProof H0 as "Hlift"; eauto.
      iDestruct ("Hlift" with "Hx") as (m1) "[Hm1 Hr1]".
      iExists (m0 ∪ m1).
      iDestruct (big_sepM_disjoint_pred with "[$Hm0] [$Hm1]") as %?; eauto.
      rewrite big_sepM_union; auto. iFrame.
      iIntros (h2) "Hh2".
      rewrite big_sepM_union; auto.
      iDestruct ("Hh2") as "[Hm0 Hm1]".
      iDestruct ("Hr0" with "Hm0") as "Hr0".
      iDestruct ("Hr1" with "Hm1") as "Hr1".
      rewrite big_sepM_insert; auto.
      iFrame.
  Unshelve.
    all: eauto.
  Qed.

  Global Instance conflicting_liftable :
    Liftable (fun mapsto => mapsto a v)%I.
  Proof.
    intros; unfold Liftable.
    iIntros (mapsto1 ?) "Ha".
    iExists (<[a:=v]> ∅).
    rewrite big_sepM_insert; try apply lookup_empty.
    iFrame.
    rewrite big_sepM_empty.
    iSplitL; try done.
    iIntros (h2) "Hh2".
    rewrite big_sepM_insert; try apply lookup_empty.
    iDestruct "Hh2" as "[Ha Hemp]".
    rewrite big_sepM_empty.
    iFrame.
  Qed.

  Global Instance independent_liftable P : Liftable (fun h => P)%I.
  Proof.
    intros; unfold Liftable.
    iIntros (mapsto1 ?) "H".
    iExists ∅.
    rewrite big_sepM_empty; iFrame.
    iIntros (h2) "Hm".
    rewrite big_sepM_empty; iFrame.
    auto.
  Qed.

  Lemma list_liftable' `(l : list V) (off : nat) P :
    (forall a v, Liftable (P a v)) ->
    Liftable (fun h => [∗ list] a ↦ v ∈ l, (P (off + a)%nat v h))%I.
  Proof using BiAffine0 BiPureForall0.
    intros.
    generalize dependent off.
    induction l; intros.
    - apply emp_liftable.
    - unfold Liftable in *.
      simpl.
      iIntros (mapsto1 ?) "[Ha Hl]".
      iDestruct (H with "Ha") as (ma0) "[Ha Hm0]"; eauto.
      iDestruct (IHl with "[Hl]") as (ml) "[Hl Hml]"; eauto.
      {
        iApply big_sepL_mono; iFrame.
        iIntros (? ? ?) "H".
        replace (off + S x)%nat with (S off + x)%nat by lia.
        iFrame.
      }

      iExists (ma0 ∪ ml).
      iDestruct (big_sepM_disjoint_pred with "[$Ha] [$Hl]") as %?; eauto.
      rewrite big_sepM_union; auto; iFrame.
      iIntros (h2) "Hh2".
      rewrite big_sepM_union; auto.
      iDestruct "Hh2" as "[Ha Hl]".
      iDestruct ("Hm0" with "Ha") as "Ha".
      iDestruct ("Hml" with "Hl") as "Hl".
      simpl.
      iFrame.
      iApply big_sepL_mono; iFrame.
      iIntros (? ? ?) "H".
      replace (off + S x)%nat with (S off + x)%nat by lia.
      iFrame.
  Unshelve.
    all: eauto.
  Qed.

  Global Instance list_liftable `(l : list V) P :
    (forall a v, Liftable (P a v)) ->
    Liftable (fun h => [∗ list] a ↦ v ∈ l, (P a v h))%I.
  Proof using BiAffine0 BiPureForall0.
    intros.
    apply (list_liftable' l 0 P) in H.
    simpl in H.
    auto.
  Qed.

End liftable.

Hint Mode Liftable ! ! ! ! ! ! : typeclass_instances.
