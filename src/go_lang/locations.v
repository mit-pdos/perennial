From stdpp Require Import countable numbers gmap.
From iris.algebra Require Import base.

Record loc := { loc_car : Z }.
Definition null := {| loc_car := 0 |}.

Instance loc_eq_decision : EqDecision loc.
Proof. solve_decision. Qed.

Instance loc_inhabited : Inhabited loc := populate {|loc_car := 0 |}.

Instance loc_countable : Countable loc.
Proof. by apply (inj_countable' loc_car (λ i, {| loc_car := i |})); intros []. Qed.

Program Instance loc_infinite : Infinite loc :=
  inj_infinite (λ p, {| loc_car := p |}) (λ l, Some (loc_car l)) _.
Next Obligation. done. Qed.

Definition loc_add (l : loc) (off : Z) : loc :=
  {| loc_car := loc_car l + off|}.

Notation "l +ₗ off" :=
  (loc_add l off) (at level 50, left associativity) : stdpp_scope.

Lemma loc_add_assoc l i j : l +ₗ i +ₗ j = l +ₗ (i + j).
Proof. destruct l; rewrite /loc_add /=; f_equal; lia. Qed.

Lemma loc_add_0 l : l +ₗ 0 = l.
Proof. destruct l; rewrite /loc_add /=; f_equal; lia. Qed.

Lemma loc_add_eq_inv l i : l +ₗ i = l -> i = 0.
Proof. destruct l; rewrite /=; inversion 1; lia. Qed.

Lemma loc_add_ne l i : (0 < i)%Z -> l +ₗ i <> l.
Proof. intros H Heq%loc_add_eq_inv; lia. Qed.

Instance loc_add_inj l : Inj eq eq (loc_add l).
Proof. destruct l; rewrite /Inj /loc_add /=; intros; simplify_eq; lia. Qed.

Definition fresh_locs (ls : gset loc) : loc :=
  {| loc_car := set_fold (λ k r, (1 + loc_car k) `max` r)%Z 1%Z ls |}.

Lemma fresh_locs_fresh ls i :
  (0 ≤ i)%Z → fresh_locs ls +ₗ i ∉ ls.
Proof.
  intros Hi. cut (∀ l, l ∈ ls → loc_car l < loc_car (fresh_locs ls) + i)%Z.
  { intros help Hf%help. simpl in *. lia. }
  apply (set_fold_ind_L (λ r ls, ∀ l, l ∈ ls → (loc_car l < r + i)%Z));
    set_solver by eauto with lia.
Qed.

Lemma fresh_locs_non_negative ls :
  (0 < loc_car (fresh_locs ls))%Z.
Proof.
  simpl.
  apply (set_fold_ind_L (λ r (ls: gset loc), (0 < r)%Z));
    intros; lia.
Qed.

Lemma fresh_locs_non_null ls i :
  (0 <= i)%Z -> fresh_locs ls +ₗ i <> null.
Proof.
  intros.
  pose proof (fresh_locs_non_negative ls); simpl in *.
  let H := fresh in
  intros H; inversion H; clear H.
  lia.
Qed.

Global Opaque fresh_locs.
