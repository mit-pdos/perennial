From iris.algebra Require Export big_op.
From iris.proofmode Require Import tactics.
From Perennial.base_logic Require Import ncfupd.
From Perennial.algebra Require Import big_op.big_sepL.

(* FIXME: upstream (see Iris MR 673) *)
Lemma big_sepS_elements {PROP:bi} `{Countable A} (Φ : A → PROP) (X : gset A) :
  ([∗ set] x ∈ X, Φ x) ⊣⊢ [∗ list] _↦x ∈ elements X, Φ x.
Proof. by rewrite big_opS_eq. Qed.

(* FIXME: upstream (see Iris MR 673) *)
Lemma big_sepS_sepS {PROP:bi} `{Countable A, Countable B}
    (X : gset A) (Y : gset B) (Φ : A → B → PROP) :
  ([∗ set] x ∈ X, [∗ set] y ∈ Y, Φ x y) -∗ ([∗ set] y ∈ Y, [∗ set] x ∈ X, Φ x y).
Proof.
  repeat setoid_rewrite big_sepS_elements.
  rewrite big_sepL_sepL. done.
Qed.
