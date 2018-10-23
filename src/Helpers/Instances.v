Require Export RelationClasses.
Require Import ProofIrrelevance.

Class EqualDec A :=
  equal_dec : forall x y : A, { x = y } + { x <> y }.

(**
    We define the notation [x == y] to mean our decidable equality
    between [x] and [y].
  *)

Notation " x == y " := (equal_dec (x :>) (y :>)) (no associativity, at level 70).

Ltac RelInstance_t :=
  intros;
  let refl := try solve [ hnf; intros; reflexivity ] in
  let symm := try solve [ hnf; intros; try symmetry; eauto ] in
  let trans := try solve [ hnf; intros; etransitivity; eauto ] in
  try match goal with
      | |- EqualDec _ =>
        hnf; decide equality
      | |- Reflexive _ =>
        hnf; intros; refl
      | |- Symmetric _ =>
        hnf; intros; symm
      | |- Transitive _ =>
        hnf; intros; trans
      | |- PreOrder _ =>
        constructor; hnf; intros; [ refl | trans ]
      | |- Equivalence _ =>
        constructor; hnf; intros; [ refl | symm | trans ]
      end.

Notation RelInstance := (ltac:(RelInstance_t)) (only parsing).

(* For units, an explicit definition has better computational behavior.
Specifically it is syntactically a [left], so any matches on [u == u']
automatically reduce to the true case; [decide equality] would first destruct
the arguments before producing [left]. *)
Instance unit_equal_dec : EqualDec unit :=
  fun x y => left (match x, y with
                | tt, tt => eq_refl
                end).

Instance nat_equal_dec : EqualDec nat := RelInstance.
Instance bool_equal_dec : EqualDec bool := RelInstance.

Instance sigT_eq_dec A (P: A -> Prop) (dec:EqualDec A) : EqualDec (sig P).
Proof.
  hnf; intros.
  destruct x as [x ?], y as [y ?].
  destruct (x == y); subst; [ left | right ].
  - f_equal.
    apply proof_irrelevance.
  - intro.
    inversion H; congruence.
Qed.

Inductive kleene_star {A} (R: A -> A -> Prop) : A -> A -> Prop :=
| star_refl : forall x, kleene_star R x x
| star_one_more : forall x y z,
    R x y ->
    kleene_star R y z ->
    kleene_star R x z.

Local Hint Constructors kleene_star.

Theorem star_one : forall A (R: A -> A -> Prop) x y,
    R x y ->
    kleene_star R x y.
Proof.
  eauto.
Qed.

Instance kleene_star_preorder A (R: A -> A -> Prop) : PreOrder (kleene_star R).
Proof.
  RelInstance_t.
  - eauto.
  - induction H; eauto.
Qed.
