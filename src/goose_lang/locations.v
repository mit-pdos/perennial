From stdpp Require Import countable numbers gmap.
From iris.prelude Require Export prelude.
From iris.prelude Require Import options.
From Perennial.algebra Require Export blocks.

Record loc := Loc { loc_car : Z; loc_off : Z }.
Add Printing Constructor loc. (* avoid printing with record syntax *)
Definition null := {| loc_car := 0; loc_off := 0 |}.

Instance loc_eq_decision : EqDecision loc.
Proof. solve_decision. Defined.

Instance loc_inhabited : Inhabited loc := populate null.

(* loc_countable was originally given with a non-constructive proof,
so we define loc_car_inj and give a constructive definition for
loc_countable in order to be able to actually interpret heap
operations. *)
Lemma loc_car_inj : forall x : loc, {| loc_car := loc_car x; loc_off := loc_off x |} = x.
  by intros [].
Qed.
Instance loc_countable : Countable loc :=
  inj_countable' (λ x, (loc_car x, loc_off x)) (fun i => {| loc_car := i.1; loc_off := i.2 |}) loc_car_inj.

Program Instance loc_infinite : Infinite loc :=
  inj_infinite (λ p, {| loc_car := p; loc_off := 0 |}) (λ l, Some (loc_car l)) _.
Next Obligation. done. Qed.

Program Instance locs_BlockAddr: BlockAddr loc :=
  {| addr_decode := λ l, (loc_car l, loc_off l);
     addr_encode := λ l, {| loc_car := fst l; loc_off := snd l |} |}.
Next Obligation. intros (?&?) => //=. Qed.
Next Obligation. intros (?&?) => //=. Qed.

Definition loc_add (l : loc) (off : Z) : loc := addr_plus_off l off.

Notation "l +ₗ off" :=
  (loc_add l off) (at level 50, left associativity) : stdpp_scope.

Lemma loc_add_assoc l i j : l +ₗ i +ₗ j = l +ₗ (i + j).
Proof. apply addr_plus_plus. Qed.

Lemma loc_add_comm l i j : l +ₗ i +ₗ j = l +ₗ j +ₗ i.
Proof. rewrite ?loc_add_assoc. f_equal. lia. Qed.

Lemma loc_add_0 l : l +ₗ 0 = l.
Proof. apply addr_plus_off_0. Qed.

Lemma loc_add_Sn l n : l +ₗ S n = (l +ₗ 1) +ₗ n.
Proof. apply addr_plus_Sn. Qed.

Lemma loc_add_eq_inv l i : l +ₗ i = l -> i = 0.
Proof. apply addr_plus_eq_inv. Qed.

Lemma loc_add_ne l i : (0 < i)%Z -> l +ₗ i <> l.
Proof. apply addr_plus_ne. Qed.

Instance loc_add_inj l : Inj eq eq (loc_add l).
Proof. apply addr_plus_off_inj. Qed.

Definition fresh_locs (ls : gset loc) : loc :=
  {| loc_car := set_fold (λ k r, (1 + loc_car k) `max` r)%Z 1%Z ls; loc_off := 0 |}.

Lemma fresh_locs_fresh ls i :
  fresh_locs ls +ₗ i ∉ ls.
Proof.
  cut (∀ l, l ∈ ls → loc_car l < loc_car (fresh_locs ls))%Z.
  { intros help Hf%help. simpl in *. rewrite /addr_id/addr_decode//= in Hf. lia. }
  apply (set_fold_ind_L (λ r ls, ∀ l, l ∈ ls → (loc_car l < r)%Z));
    set_solver by eauto with lia.
Qed.

Lemma fresh_locs_non_negative ls :
  (0 < loc_car (fresh_locs ls))%Z.
Proof.
  simpl.
  apply (set_fold_ind_L (λ r (ls: gset loc), (0 < r)%Z));
    intros; lia.
Qed.

Lemma fresh_locs_off_0 ls :
  (loc_off (fresh_locs ls) = 0)%Z.
Proof. trivial. Qed.

Lemma fresh_locs_non_null ls i :
  fresh_locs ls +ₗ i <> null.
Proof.
  intros.
  pose proof (fresh_locs_non_negative ls); simpl in *.
  rewrite /fresh_locs/loc_add/addr_plus_off/addr_id/addr_offset/addr_plus_off//=.
  inversion 1. lia.
Qed.

Global Opaque fresh_locs.
