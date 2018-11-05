Require Export RelationClasses.
Require Import ProofIrrelevance.

Class EqualDec A :=
  equal_dec : forall x y : A, { x = y } + { x <> y }.

(**
    We define the notation [x == y] to mean our decidable equality
    between [x] and [y].
  *)

Module EqualDecNotation.
  Infix "==" := (equal_dec) (no associativity, at level 70).
End EqualDecNotation.

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
  destruct (equal_dec x y); subst; [ left | right ].
  - f_equal.
    apply proof_irrelevance.
  - intro.
    inversion H; congruence.
Qed.

Class Default T := default : T.
(* should address most instances *)
Hint Extern 0 (Default _) => unfold Default; constructor : typeclass_instances.

Instance unit_inhabited : Default unit.
Proof.
  typeclasses eauto.
Qed.
