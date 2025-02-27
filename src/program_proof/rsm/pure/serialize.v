From iris.proofmode Require Import proofmode.
From Perennial.Helpers Require Import Integers.

Set Default Proof Using "Type".

Definition serialize {A} (f : A -> list u8) (l : list A) :=
  foldl (λ p c, p ++ f c) [] l.

Section lemmas.
  Context {A : Type}.
  Implicit Type f : A -> list u8.
  Implicit Type l : list A.
  Implicit Type x : A.
  Implicit Type n : nat.

  Lemma serialize_snoc f l x :
    serialize f (l ++ [x]) = serialize f l ++ f x.
  Proof. by rewrite /serialize foldl_snoc. Qed.

  Lemma app_serialize f (bs : list u8) l :
    bs ++ serialize f l = foldl (λ p c, p ++ f c) bs l.
  Proof.
    generalize dependent bs.
    induction l as [| x xs IH]; intros bs.
    { by rewrite /= app_nil_r. }
    by rewrite /serialize /= -(IH (f x)) -(IH (bs ++ f x)) app_assoc.
  Qed.

  Lemma serialize_cons f l x :
    serialize f (x :: l) = f x ++ serialize f l.
  Proof. by rewrite /serialize /= -app_serialize. Qed.

  Lemma serialize_app f l1 l2 :
    serialize f (l1 ++ l2) = serialize f l1 ++ serialize f l2.
  Proof. by rewrite /serialize foldl_app -app_serialize. Qed.

  Lemma serialize_length_inv f l n :
    (∀ x, length (f x) ≠ O) ->
    (length (serialize f l) ≤ n)%nat ->
    (length l ≤ n)%nat.
  Proof.
    intros Hnz.
    generalize dependent n.
    induction l as [| x xs IH]; intros n; first done.
    rewrite serialize_cons length_app /=.
    intros Hlen.
    specialize (Hnz x).
    assert (Hlenxs : (length xs ≤ pred n)%nat).
    { apply IH. lia. }
    lia.
  Qed.

  Lemma serialize_nil f :
    serialize f [] = [].
  Proof. done. Qed.

End lemmas.
