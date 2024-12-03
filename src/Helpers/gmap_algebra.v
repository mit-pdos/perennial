From stdpp Require Export list gmap.
From iris.algebra Require Export list cmra.
From iris.algebra Require Import gset.
From iris.algebra Require Import updates local_updates proofmode_classes big_op gmap.

Section unital_properties.
Context `{Countable K} {A : ucmra}.
Implicit Types m : gmap K A.
Implicit Types i : K.
Implicit Types x y : A.

#[local]
Instance singleton_proper i : Proper ((≡) ==> (≡)) (singletonM i : A → gmap K A).
Proof. apply (ne_proper _). Qed.

Lemma singleton_big_opS {X : Type} `{Countable1 : Countable X} (i : K) (M : gset X) (f : X → A):
  M ≠ ∅ →
  (([^op set] x ∈ M, {[i := f x]}) : gmapUR K A) ≡ {[i := [^op set] x ∈ M, f x]}.
Proof.
  induction M as [ | x M IH1] using set_ind_L.
  { set_solver. }
  intros _.
  induction M as [ | y M IH2] using set_ind_L.
  { rewrite union_empty_r_L ?big_opS_singleton //. }
  rewrite big_opS_union; last by set_solver.
  symmetry.
  rewrite big_opS_union; last by set_solver.
  rewrite -singleton_op.
  f_equiv.
  { rewrite ?big_opS_singleton //. }
  rewrite IHM //; set_solver.
Qed.

Lemma singleton_big_opS_le {X : Type} `{Countable1 : Countable X} (i : K) (M : gset X) (f : X → A):
  (([^op set] x ∈ M, {[i := f x]}) : gmapUR K A) ≼  {[i := [^op set] x ∈ M, f x]}.
Proof.
  induction M as [ | x M IH1] using set_ind_L.
  { rewrite big_opS_empty. eexists. rewrite left_id //. }
  rewrite singleton_big_opS; last by set_solver.
  reflexivity.
Qed.

End unital_properties.
