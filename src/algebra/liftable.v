From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import iprop.
From Perennial.algebra Require Import big_op.

Section liftable.

  Context `{PROP:bi} `{!BiAffine PROP} `{!BiPureForall PROP}.
  Context {L V: Type} `{!EqDecision L} `{!Countable L}.
  Implicit Types (P Q : (L → V → PROP) → PROP).

  Set Default Proof Using "BiAffine0".

  (** The resources needed to restore predicate P over map m; has no ownership
  of maps-to facts itself *)
  Definition PredRestore P (m: gmap L V) : PROP :=
    (∀ mapsto2, ([∗ map] a↦v ∈ m, mapsto2 a v) -∗ P mapsto2)%I.

  Global Instance PredRestore_proper : Proper (pointwise_relation _ (⊣⊢) ==> eq ==> (⊣⊢)) PredRestore.
  Proof.
    intros P1 P2 Hequiv m m' ->.
    rewrite /PredRestore.
    setoid_rewrite Hequiv.
    auto.
  Qed.

  Class Liftable (P : (L -> V -> PROP) -> PROP) := liftable :
    ∀ mapsto1,
      Conflicting mapsto1 ->
      P mapsto1 -∗
      ∃ (m : gmap L V),
        ([∗ map] a ↦ v ∈ m, mapsto1 a v) ∗
           □ PredRestore P m.

  Global Instance liftable_proper : Proper (pointwise_relation _ (⊣⊢) ==> iff) Liftable.
  Proof.
    intros P1 P2 Hequiv.
    rewrite /Liftable.
    setoid_rewrite Hequiv.
    auto.
  Qed.

  Theorem liftable_sep P Q : Liftable P → Liftable Q → Liftable (fun h => P h ∗ Q h)%I.
  Proof using BiAffine0 BiPureForall0.
    unfold Liftable in *.
    intros LiftableP LiftableQ.
    iIntros (??) "[Hp Hq]".
    iDestruct (LiftableP with "Hp") as (mp) "[Hpm #Hpi]"; eauto.
    iDestruct (LiftableQ with "Hq") as (mq) "[Hqm #Hqi]"; eauto.
    iExists (mp ∪ mq).
    iDestruct (big_sepM_disjoint_pred with "[$Hpm] [$Hqm]") as %?; eauto.
    iDestruct (big_sepM_union with "[$Hpm $Hqm]") as "Hm"; eauto.
    iFrame.
    iIntros "!>" (h2) "Hm".
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

  Global Instance exists_liftable T Φ :
    (∀ x, Liftable (Φ x)) ->
    Liftable (λ h, ∃ (x : T), Φ x h)%I.
  Proof.
    unfold Liftable in *.
    iIntros (H h ?) "H".
    iDestruct "H" as (x) "H".
    iDestruct (H with "H") as (m) "(Hm & #Hx)"; eauto.
    iExists _. iFrame.
    iIntros "!>" (h2) "Hm".
    iDestruct ("Hx" with "Hm") as "Hp".
    iExists _. iFrame.
  Qed.

  Global Instance independent_liftable R `{!Persistent R} : Liftable (fun h => R)%I.
  Proof.
    intros; unfold Liftable.
    iIntros (mapsto1 ?) "#H".
    iFrame "H".
    iExists ∅.
    rewrite big_sepM_empty.
    setoid_rewrite big_sepM_empty.
    eauto with iFrame.
  Qed.

  Global Instance singleton_liftable {a v} :
    Liftable (fun mapsto => mapsto a v)%I.
  Proof.
    intros; unfold Liftable.
    iIntros (mapsto1 ?) "Ha".
    iExists (<[a:=v]> ∅).
    rewrite big_sepM_insert; try apply lookup_empty.
    iFrame.
    rewrite big_sepM_empty.
    iSplitL; try done.
    iIntros "!>" (h2) "Hh2".
    rewrite big_sepM_insert; try apply lookup_empty.
    iDestruct "Hh2" as "[$ _]".
  Qed.

  Global Instance map_liftable `{EqDecision LM} `{Countable LM} `(m : gmap LM VM) Φ :
    (forall a v, Liftable (Φ a v)) →
    Liftable (fun h => [∗ map] a ↦ v ∈ m, (Φ a v h))%I.
  Proof using BiAffine0 BiPureForall0.
    intros.
    induction m as [|i x m] using map_ind.
    - setoid_rewrite big_sepM_empty.
      apply _.
    - setoid_rewrite (big_sepM_insert _ _ _ _ H1).
      apply _.
  Qed.

  Lemma list_liftable' `(l : list V) (off : nat) Φ :
    (forall a v, Liftable (Φ a v)) ->
    Liftable (fun h => [∗ list] a ↦ v ∈ l, (Φ (off + a)%nat v h))%I.
  Proof using BiAffine0 BiPureForall0.
    intros.
    revert off.
    induction l as [|x l]; simpl; intros.
    - apply _.
    - apply liftable_sep; auto.
      setoid_rewrite <- Nat.add_succ_comm.
      auto.
  Qed.

  Global Instance list_liftable `(l : list V) Φ :
    (forall a v, Liftable (Φ a v)) ->
    Liftable (fun h => [∗ list] a ↦ v ∈ l, (Φ a v h))%I.
  Proof using BiAffine0 BiPureForall0.
    intros.
    apply (list_liftable' l 0 Φ) in H.
    simpl in H.
    auto.
  Qed.

End liftable.

Hint Mode Liftable ! ! ! ! ! ! : typeclass_instances.
