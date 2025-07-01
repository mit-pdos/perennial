(* Needs [Local Set Universe Polymorphic] in [cmra.v].
   Don't know which definitions *actually* need to be polymorphic. *)
From iris.algebra Require Export cmra.

Section all.
(* A cmra that contains all cmras (that are a universe level below). I think
   this needs [cmra] to be universe polymorphic. *)
Context {SI : sidx}.
Definition all_ucmra := ∀ A : ucmra, A.

Global Instance equiv_instance : Equiv all_ucmra :=
  λ x y, ∀ A, (x A) ≡ (y A).

Global Instance dist_instance : Dist all_ucmra :=
  λ i x y, ∀ A, dist i (x A) (y A).

Global Instance unit_instance : Unit all_ucmra :=
  λ A, ε.

Global Instance valid_instance : Valid all_ucmra :=
  λ x, ∀ A, ✓ (x A).

Global Instance validN_instance : ValidN all_ucmra :=
  λ n x, ∀ A, ✓{n} (x A).

Global Instance pcore_instance : PCore all_ucmra :=
  λ x, Some (λ A : ucmra, default ε (pcore (x A))).

Global Instance op_instance : Op all_ucmra :=
  λ x y, λ A, (x A) ⋅ (y A).

Global Instance dist_equivalence n : Equivalence (dist n (A:=all_ucmra)).
Proof.
  split.
  - intros ??. done.
  - intros ????. done.
  - intros ??????. specialize (H A). specialize (H0 A). rewrite H H0 //.
Qed.

Lemma all_ucmra_ofe_mixin : OfeMixin all_ucmra.
  split.
  - intros ??. split.
    + intros H n. intros A. apply equiv_dist. apply H.
    + intros H. intros A. apply equiv_dist. intros n.
      specialize (H n). apply H.
  - apply _.
  - intros. intros A. eapply dist_le; last done. apply H.
Qed.


Lemma all_ucmra_ucmra_mixin : UcmraMixin all_ucmra.
Proof.
  split.
  - intros ?. apply ucmra_unit_valid.
  - intros ??. apply ucmra_unit_left_id.
  - constructor. simpl. unfold equiv. unfold equiv_instance.
    intros ?. rewrite ucmra_pcore_unit //.
Qed.

Lemma all_ucmra_cmra_mixin : CmraMixin all_ucmra.
  split; repeat intros ?.
  - specialize (H A). by apply cmra_op_ne.
  - eexists _; split; [done|].
    intros A. specialize (H A).
    setoid_rewrite <- H.
    rewrite /pcore /pcore_instance in H0.
    simplify_eq. done.
  - specialize (H A). specialize (H0 A). by eapply cmra_validN_ne.
  - split; repeat intros ?.
    + specialize (H A). by apply cmra_valid_validN.
    + apply cmra_valid_validN. intros n. specialize (H n A). done.
  - specialize (H A). by eapply cmra_validN_le.
  - apply cmra_assoc.
  - apply cmra_comm.
  - rewrite /op /op_instance.
    rewrite /pcore /pcore_instance in H. simplify_eq.
    destruct (pcore (x A)) eqn:H.
    + simpl. by apply cmra_pcore_l.
    + simpl. rewrite left_id //.
  - constructor. repeat intros ?.
    inversion H. subst.
    destruct (pcore (x A)) eqn:H'.
    + simpl. rewrite cmra_pcore_idemp //.
    + simpl. rewrite ucmra_pcore_unit //.
  - eexists _; split; [done|].
    destruct H as [z H]. inversion H0. subst.
    eexists _. intros ?.
    specialize (H A). rewrite /pcore /pcore_instance.
(*
    mixin_cmra_pcore_mono : ∀ x y cx : A, x ≼ y → pcore x = Some cx → ∃ cy : A, pcore y = Some cy ∧ cx ≼ cy;
    mixin_cmra_validN_op_l : ∀ (n : SI0) (x y : A), ✓{n} (x ⋅ y) → ✓{n} x;
    mixin_cmra_extend : ∀ (n : SI0) (x y1 y2 : A),
                          ✓{n} x
                          → x ≡{n}≡ y1 ⋅ y2 → {z1 : A & {z2 : A | x ≡ z1 ⋅ z2 ∧ z1 ≡{n}≡ y1 ∧ z2 ≡{n}≡ y2}} }.
 *)
Admitted.

(* Need universe polymorphism:
Definition all_ucmraUR: ucmra :=
  (Ucmra' all_ucmra all_ucmra_ofe_mixin all_ucmra_cmra_mixin all_ucmra_ucmra_mixin).
  *)

End all.

From Coq Require Import Logic.ClassicalEpsilon.
Section own.
Context {SI : sidx}.

Definition convert_to_all {A : ucmra} (a : A) : all_ucmra :=
  λ B, match (excluded_middle_informative (A = B)) with
       | right _ => ε
       | left eq_proof => eq_rect A id a B eq_proof
       end.

End own.
