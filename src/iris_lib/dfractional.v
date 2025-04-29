From iris.bi Require Import bi.
From iris.proofmode Require Import classes classes_make proofmode.
From iris.bi.lib Require Import fractional.
From iris.algebra Require Import dfrac.
From iris.prelude Require Import options.

(** This library is a (partial) copy of the Iris fractional library, adapted to
dfrac. We do extend the interface to include dfrac-specific laws. *)

Class DFractional {PROP : bi} `{BUpd PROP} (Φ : dfrac → PROP) :=
  { dfractional dp dq : Φ (dp ⋅ dq) ⊣⊢ Φ dp ∗ Φ dq;
    dfractional_persistent : Persistent (Φ DfracDiscarded);
    dfractional_persist dq : Φ dq ⊢ |==> Φ DfracDiscarded; }.
Global Arguments dfractional {_ _ _ _} _ _.
Global Arguments dfractional_persistent {_ _} _ {_}.
Global Arguments dfractional_persist {_ _ _ _} _.

(** The [AsDFractional] typeclass is analogous to [AsFractional]: it is only
there to assist higher-order unification for APIs that want to take a [P] that
has to be turned into [Φ dq]. See the documentation for [AsFractional] for more
details. *)
Class AsDFractional {PROP : bi} (H: BUpd PROP) (P : PROP) (Φ : dfrac → PROP) (dq : dfrac) := {
  as_dfractional : P ⊣⊢ Φ dq;
  as_dfractional_dfractional : DFractional Φ
}.
Global Arguments AsDFractional {_ _} _%_I _%_I _%_Qp.
Global Hint Mode AsDFractional - - ! - - : typeclass_instances.

Section dfractional.
  Context {PROP : bi} {H: BiBUpd PROP}.
  Implicit Types P Q : PROP.
  Implicit Types Φ : dfrac → PROP.
  Implicit Types q : Qp.
  Implicit Types dq : dfrac.

  Lemma fractional_of_dfractional Φ : DFractional Φ → Fractional (λ q, Φ (DfracOwn q)).
  Proof.
    intros ?.
    rewrite /Fractional.
    intros.
    rewrite -dfrac_op_own dfractional //.
  Qed.

  (* TODO: not sure if this is a good instance to have. It doesn't allow proving
  Fractional directly, and it's hard to do that with typeclass search due to
  higher-order unification struggling to go from a predicate over Qp to one
  over dfrac. *)
  Global Instance as_fractional_of_as_dfractional P Φ q :
    AsDFractional P Φ (DfracOwn q) → AsFractional P (λ q, Φ (DfracOwn q)) q.
  Proof.
    intros [Heq ?].
    constructor; [ done | ].
    apply fractional_of_dfractional; auto.
  Qed.

  (* this instance isn't generally useful since DFractional doesn't unify with Φ
  dq *)
  Local Existing Instance dfractional_persistent.

  Global Instance DFractional_proper :
    Proper (pointwise_relation _ (≡) ==> iff) (@DFractional PROP _).
  Proof.
    intros Φ1 Φ2 Hequiv.
    split; intros [? ? ?].
    - constructor; setoid_rewrite <- Hequiv; auto.
    - constructor; setoid_rewrite -> Hequiv; auto.
  Qed.

  Global Instance persistent_dfractional (P : PROP) :
    Persistent P → TCOr (Affine P) (Absorbing P) → DFractional (λ _, P).
  Proof.
    intros ??. constructor; [ | by auto | by auto ].
    intros dq1 dq2. apply: bi.persistent_sep_dup.
  Qed.

  Global Instance dfractional_sep Φ Ψ :
    DFractional Φ → DFractional Ψ → DFractional (λ dq, Φ dq ∗ Ψ dq)%I.
  Proof.
    intros ??.
    constructor.
    - intros dq1 dq2. rewrite !dfractional -!assoc. f_equiv.
      rewrite !assoc. f_equiv. by rewrite comm.
    - apply _.
    - intros dq.
      rewrite (dfractional_persist dq).
      rewrite (dfractional_persist dq).
      iIntros "[>H1 >H2]".
      iFrame. done.
  Qed.

  Global Instance dfractional_big_sepL {A} (l : list A) Ψ :
    (∀ k x, DFractional (Ψ k x)) →
    DFractional (PROP:=PROP) (λ dq, [∗ list] k↦x ∈ l, Ψ k x dq)%I.
  Proof.
    intros ?.
    constructor.
    - intros dq1 dq2. rewrite -big_sepL_sep. by setoid_rewrite dfractional.
    - apply _.
    - intros q. rewrite -big_sepL_bupd.
      iIntros "H".
      iApply (big_sepL_impl with "H").
      iIntros "!>" (???).
      iApply dfractional_persist.
  Qed.

  Global Instance dfractional_big_sepL2 {A B} (l1 : list A) (l2 : list B) Ψ :
    (∀ k x1 x2, DFractional (Ψ k x1 x2)) →
    DFractional (PROP:=PROP) (λ dq, [∗ list] k↦x1; x2 ∈ l1; l2, Ψ k x1 x2 dq)%I.
  Proof.
    intros ?.
    constructor.
    - intros dq1 dq2. rewrite -big_sepL2_sep. by setoid_rewrite dfractional.
    - apply _.
    - intros q.
      rewrite !big_sepL2_alt.
      iIntros "[$ H]".
      rewrite -big_sepL_bupd.
      iApply (big_sepL_impl with "H").
      iIntros "!>" (???).
      iApply dfractional_persist.
  Qed.

  Lemma dfractional_update_to_dfrac `{BiBUpd PROP} Φ dq `{BiAffine PROP} :
    DFractional Φ →
    ✓dq →
    Φ (DfracOwn 1) ⊢ |==> Φ dq.
  Proof.
    intros ? Hvalid.
    destruct dq.
    - apply -> dfrac_valid_own in Hvalid.
      apply Qp.le_lteq in Hvalid as [? | ?].
      + destruct (Qp.lt_sum q 1) as [[q' ->] _]; auto.
        change (DfracOwn (q + q')) with (DfracOwn q ⋅ DfracOwn q').
        rewrite dfractional.
        iIntros "[$ _]"; auto.
      + subst; auto.
    - rewrite dfractional_persist //.
    - rewrite /valid /cmra_valid /= in Hvalid.
      destruct (Qp.lt_sum q 1) as [[q' ->] _]; auto.
      change (DfracBoth q) with (DfracOwn q ⋅ DfracDiscarded).
      change (DfracOwn (q + q')) with (DfracOwn q ⋅ DfracOwn q').
      rewrite !dfractional.
      iIntros "[$ H2]".
      iMod (dfractional_persist with "H2") as "$".
      done.
  Qed.

End dfractional.

Global Arguments fractional_of_dfractional {_ _} Φ {_} p q.

Ltac solve_as_frac :=
  solve [ constructor; [ done | apply _ ] ].
Hint Extern 1 (AsDFractional _ _ _) => solve_as_frac : core.
Hint Extern 1 (AsFractional _ _ _) => solve_as_frac : core.
