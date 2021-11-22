From Coq Require Import ssreflect.
From stdpp Require Import prelude tactics.
From stdpp Require Import list.

Set Default Proof Using "Type".

Ltac list_simpl :=
  repeat first [
      progress rewrite -> ?app_length, ?drop_length in * |
      rewrite -> @take_length_le in * by lia |
      rewrite -> @take_length_ge in * by lia |
      rewrite -> @take_length in *
    ];
  repeat first [
      rewrite -> lookup_app_l by lia |
      rewrite -> lookup_app_r by lia |
      progress rewrite ?lookup_drop |
      rewrite -> lookup_take by lia |
      rewrite -> lookup_take_ge by lia
    ].

Section list.
  Context {A: Type}.
  Implicit Types (l: list A) (x: A).

  Lemma list_eq_length l1 l2 :
    l1 = l2 → length l1 = length l2.
  Proof. move=> -> //. Qed.

  Lemma list_eq_forall l1 l2 :
    l1 = l2 →
    ∀ i, l1 !! i = l2 !! i.
  Proof. move=> -> //. Qed.

  Lemma list_prefix_forall l1 l2 :
    l1 `prefix_of` l2 →
    ∀ i, i < length l1 → l1 !! i = l2 !! i.
  Proof.
    intros.
    apply lookup_lt_is_Some_2 in H0 as [x ?].
    rewrite H0.
    eapply prefix_lookup in H0; eauto.
  Qed.

  Lemma list_eq_bounded l1 l2 :
    length l1 = length l2 →
    (∀ i, i < length l1 →
          l1 !! i = l2 !! i) →
    l1 = l2.
  Proof.
    intros ? Heq.
    eapply list_eq_same_length; eauto.
    intros ??? ? Hl1 Hl2.
    rewrite Heq in Hl1; [ lia | ].
    congruence.
  Qed.

  Lemma list_prefix_bounded l1 l2 :
    length l1 ≤ length l2 →
    (∀ i, i < length l1 →
          l1 !! i = l2 !! i) →
    l1 `prefix_of` l2.
  Proof.
    intros Hlen Heq.
    exists (drop (length l1) l2).
    apply list_eq_bounded.
    - list_simpl; lia.
    - intros i Hlt.
      destruct (decide (i < length l1)).
      + list_simpl.
        rewrite Heq //.
      + list_simpl.
        f_equal; lia.
  Qed.

  Lemma list_prefix_refl l :
    l `prefix_of` l.
  Proof. reflexivity. Qed.
End list.

Ltac saturate_length :=
  repeat match goal with
         | H: @eq (list _) ?l1 ?l2 |- _ =>
             learn_hyp (list_eq_length l1 l2);
             pose proof (list_eq_forall l1 l2 H);
             clear H
         | H: ?l1 `prefix_of` ?l2 |- _ =>
             let Hnew := fresh H "len" in
             learn_hyp (prefix_length l1 l2 H) as Hnew;
             pose proof (list_prefix_forall l1 l2 H);
             clear H
         end.

Ltac find_nil :=
  repeat match goal with
         | H: length ?l = 0 |- _ =>
             apply nil_length_inv in H; subst
         | H: 0 = length ?l |- _ =>
             apply eq_sym, nil_length_inv in H; subst
         | H: ?l `prefix_of` [] |- _ =>
             apply prefix_nil_inv in H; subst
         end.

Create HintDb list.
Hint Resolve list_prefix_refl : list.
Hint Resolve prefix_nil : list.

Ltac solve_list_eq :=
  saturate_length;
  let i := fresh "i" in
  first [
      apply list_eq_bounded;
      [ lia | intros i ? ] |
      apply list_eq; intros i
    ];
  list_simpl;
  auto with lia.

(* TODO: actually try list_prefix_bounded *)
Ltac solve_list_prefix :=
  saturate_length;
  auto with list.

Ltac solve_list_general :=
  saturate_length;
  list_simpl;
  auto with lia.

Ltac list_solver :=
  autounfold with list in *;
  intros;
  lazymatch goal with
  | |- @eq (list _) _ _ => solve [ solve_list_eq ]
  | |- _ `prefix_of` _ => solve [ solve_list_prefix ]
  | _ => solve [ solve_list_general ]
  end.

Section test.
  Context {A: Type}.
  Implicit Types (l: list A).

  Theorem test_1 l1 l2 :
    length l2 ≤ length l1 →
    l1 `prefix_of` l2 →
    l1 = l2.
  Proof.
    list_solver.
  Qed.

End test.
