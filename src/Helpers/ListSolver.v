From Coq Require Import ssreflect.
From stdpp Require Import prelude tactics.
From stdpp Require Import list.

Set Default Proof Using "Type".

Lemma list_prefix_refl {A} (l: list A) :
  l `prefix_of` l.
Proof. reflexivity. Qed.

Lemma list_lookup_eq {A} (l: list A) (i1 i2: nat) :
  i1 = i2 →
  l !! i1 = l !! i2.
Proof. by intros ->. Qed.

Create HintDb list.
#[global]
Hint Resolve list_prefix_refl : list.
#[global]
Hint Resolve prefix_nil : list.
#[global]
Hint Resolve list_lookup_eq : list.

Ltac find_nil :=
  repeat match goal with
         | H: length ?l = 0 |- _ =>
             apply nil_length_inv in H; subst l
         | H: 0 = length ?l |- _ =>
             apply eq_sym, nil_length_inv in H; subst l
         | H: ?l `prefix_of` [] |- _ =>
             apply prefix_nil_inv in H; subst l
         end.

Ltac list_simpl :=
  (* TODO: this is fragile with split_app_lookup: we rely on re-proving [i <
  length l] with [lia], to detect that a split has been made, but this can break
  if the hypothesis gets simplified away by the rewriting here.

  This solver needs a more robust way to remember that something has happened,
  more like the Learn library in coq-tactical, combined with support here for
  not altering Learned hypotheses. *)
  repeat match goal with
         | H: context[(_ ++ _) !! _] |- _ =>
             first [ rewrite -> lookup_app_l in H by lia |
                     rewrite -> lookup_app_r in H by lia ]
         | |- context[(_ ++ _) !! _] =>
             first [ rewrite -> lookup_app_l by lia |
                     rewrite -> lookup_app_r by lia ]
         end;
  repeat first [
      progress rewrite -> ?length_app, ?length_drop, ?length_insert in * |
      rewrite -> @length_take_le in * by lia |
      rewrite -> @length_take_ge in * by lia |
      rewrite -> @length_take in *
    ];
  repeat first [
      progress rewrite -> @lookup_drop in * |
      progress rewrite -> @lookup_take_lt in * by lia |
      progress rewrite -> lookup_take_ge in * by lia |
      progress rewrite -> lookup_nil in *
    ];
  find_nil;
  cbn [length] in *.

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
    eapply prefix_lookup_Some in H0; eauto.
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
        auto with list lia.
  Qed.

End list.

Ltac find_list_hyps :=
  repeat match goal with
         | H: @eq (list _) ?l1 ?l2 |- _ =>
             learn_hyp (list_eq_length l1 l2 H);
             pose proof (list_eq_forall l1 l2 H);
             clear H
         | H: ?l1 `prefix_of` ?l2 |- _ =>
             let Hnew := fresh H "len" in
             learn_hyp (prefix_length l1 l2 H) as Hnew;
             pose proof (list_prefix_forall l1 l2 H);
             clear H
         end.

(*
Ltac learn_feed_as H i :=
  feed_core H using (fun p => let P := type of p in
                  lazymatch goal with
                  | H: P |- _ => fail 1
                  | _ => pose proof p as i
                  end).

Ltac use_list_hyps :=
  repeat match goal with
         | H: (forall (i:nat), _), i: nat |- _ =>
             let Hi := fresh H i in
             learn_feed_as (H i) Hi; [ lia .. | ]
         end.
*)

Ltac start_list_eq :=
  let i := fresh "i" in
  first [
      apply list_eq_bounded; [ lia | intros i ? ] |
      apply list_eq; intros i
    ].

Definition lt_le_dec n1 n2 : {n1 < n2} + {n2 ≤ n1}.
Proof.
  destruct (decide (n1 < n2)); [ left | right ]; lia.
Qed.

(* Split on whether i is < length l or not. Checks if the split is
unnecessary. *)
Ltac split_i l i :=
  first [
      assert_succeeds
        ((assert (i < length l) by lia) || (assert (length l ≤ i) by lia));
      fail 1 "i < length l or not already" |
      destruct (lt_le_dec i (length l))
    ].

Ltac split_app_lookups :=
  repeat match goal with
         | |- context[(?l1 ++ _) !! ?i] =>
             split_i l1 i
         | H: context[(?l1 ++ _) !! ?i] |- _ =>
             split_i l1 i
         end.

(*
Ltac solve_list_eq :=
  find_list_hyps;
  start_list_eq;
  repeat first [
      progress list_simpl |
      progress use_list_hyps |
      progress split_app_lookups
    ];
  auto with lia list.

Ltac start_list_prefix :=
  apply list_prefix_bounded;
  [ list_simpl; solve [ auto with list lia ] |
    let i := fresh "i" in
    let Hle := fresh "Hle" in
    intros i Hle ].

Ltac solve_list_prefix :=
  find_list_hyps;
  start_list_prefix;
  list_simpl;
  use_list_hyps;
  list_simpl;
  auto with lia list.
*)

Ltac solve_list_general :=
  find_list_hyps;
  list_simpl;
  auto with lia list.

(*
Ltac list_solver :=
  autounfold with list in *;
  intros;
  lazymatch goal with
  | |- @eq (list _) _ _ => solve [ solve_list_eq ]
  | |- _ `prefix_of` _ => solve [ solve_list_prefix ]
  | _ => solve [ solve_list_general ]
  end.
*)

(*
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

  (* B[:n] ⪯ A -∗ A[:n] ⪯ B[:n] *)
  Theorem test_2 l1 l2 n :
    n ≤ length l2 →
    take n l2 `prefix_of` l1 →
    take n l1 `prefix_of` take n l2.
  Proof.
    list_solver.
  Qed.

  Theorem test_3 l :
    [] `prefix_of` l.
  Proof.
    list_solver.
  Qed.

  Theorem test_4 l1 l2 :
    l1 ++ l2 `prefix_of` l2  →
    l1 `prefix_of` l2.
  Proof.
    list_solver.
  Qed.

  Theorem test_5 l n :
    n ≤ length l →
    take n l ++ drop n l = l.
  Proof.
    list_solver.
  Qed.

End test.
*)
