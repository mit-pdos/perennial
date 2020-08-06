From stdpp Require Import list list_numbers.
From Coq Require Import ssreflect.

Section list.
  Context (A:Type).
  Notation list := (list A).
  Implicit Types (l:list).

  Lemma map_neq_nil {B: Type} (f: A → B) (l: list): l ≠ [] → map f l ≠ [].
  Proof. induction l => //=. Qed.

  Lemma length_nonzero_neq_nil (l: list): (0 < length l)%nat → l ≠ [].
  Proof. induction l => //=. inversion 1. Qed.

  Lemma drop_lt (l : list) (n : nat): (n < length l)%nat → drop n l ≠ [].
  Proof.  intros. eapply length_nonzero_neq_nil. rewrite drop_length. lia. Qed.

  Lemma list_lookup_lt (l: list) (i: nat) :
    (i < length l)%nat ->
    exists x, l !! i = Some x.
  Proof.
    intros.
    destruct_with_eqn (l !! i); eauto.
    exfalso.
    apply lookup_ge_None in Heqo.
    lia.
  Qed.

  Lemma list_fmap_map {B} (f: A → B) (l: list):
    f <$> l = map f l.
  Proof. induction l => //=. Qed.

  Definition Forall_idx (P: nat -> A -> Prop) (start:nat) (l: list): Prop :=
    Forall2 P (seq start (length l)) l.

  Lemma drop_seq n len m :
    drop m (seq n len) = seq (n + m) (len - m).
  Proof.
    revert n m.
    induction len; simpl; intros.
    - rewrite drop_nil //.
    - destruct m; simpl.
      + replace (n + 0)%nat with n by lia; auto.
      + rewrite IHlen.
        f_equal; lia.
  Qed.


  Theorem Forall_idx_drop (P: nat -> A -> Prop) l (start n: nat) :
    Forall_idx P start l ->
    Forall_idx P (start + n) (drop n l).
  Proof.
    rewrite /Forall_idx.
    intros.
    rewrite drop_length -drop_seq.
    apply Forall2_drop; auto.
  Qed.

  Theorem Forall_idx_impl (P1 P2: nat -> A -> Prop) l (start n: nat) :
    Forall_idx P1 start l ->
    (forall i x, l !! i = Some x ->
            P1 (start + i)%nat x ->
            P2 (start + i)%nat x) ->
    Forall_idx P2 start l.
  Proof.
    rewrite /Forall_idx.
    intros.
    apply Forall2_same_length_lookup.
    eapply Forall2_same_length_lookup in H.
    intuition idtac.
    pose proof H as Hlookup.
    apply lookup_seq in Hlookup; intuition subst.
    apply H0; eauto.
  Qed.

  (* copied from Coq 8.12+alpha for compatibility with Coq 8.11 *)
  Lemma incl_Forall P l1 l2 : incl l2 l1 -> Forall P l1 -> Forall P l2.
  Proof.
    intros Hincl HF.
    apply List.Forall_forall; intros a Ha.
    apply List.Forall_forall with (x:=a) in HF; intuition.
  Qed.
End list.

(* section for more specific list lemmas that aren't for arbitrary [list A] *)
Section list.
  (* for compatibility with Coq v8.11, which doesn't have this lemma *)
  Lemma in_concat {A} : forall (l: list (list A)) y,
    In y (concat l) <-> exists x, In x l /\ In y x.
  Proof.
    induction l; simpl; split; intros.
    contradiction.
    destruct H as (x,(H,_)); contradiction.
    destruct (in_app_or _ _ _ H).
    exists a; auto.
    destruct (IHl y) as (H1,_); destruct (H1 H0) as (x,(H2,H3)).
    exists x; auto.
    apply in_or_app.
    destruct H as (x,(H0,H1)); destruct H0.
    subst; auto.
    right; destruct (IHl y) as (_,H2); apply H2.
    exists x; auto.
  Qed.

  Lemma concat_insert_app {A} : forall (index: nat) (l: list (list A)) (x: list A),
    index < length l ->
    concat (<[index := x]> l) = (concat (take index l)) ++ x ++ (concat (drop (index+1) l)).
  Proof.
    intros.
    rewrite -(take_drop_middle (<[index := x]> l) index x); auto.
    rewrite list_lookup_insert; auto.
    rewrite concat_app concat_cons take_insert; auto.
    rewrite drop_insert_gt; auto.
    by replace (index + 1) with (S index) by lia.
  Qed.

End list.

(* copied from Coq 8.12+alpha for 8.11 compatibility *)
Lemma Permutation_app_swap_app {A} : forall (l1 l2 l3: list A),
  Permutation (l1 ++ l2 ++ l3) (l2 ++ l1 ++ l3).
Proof.
  intros.
  rewrite -> 2 app_assoc.
  apply Permutation_app_tail, Permutation_app_comm.
Qed.

Global Instance concat_permutation_proper T :
  Proper (Permutation ==> Permutation) (@concat T).
Proof.
  intros a b H.
  induction H; eauto.
  - simpl. rewrite IHPermutation. eauto.
  - simpl. apply Permutation_app_swap_app.
  - etransitivity; eauto.
Qed.

Global Instance concat_permutation_proper_forall T :
  Proper (Forall2 Permutation ==> Permutation) (@concat T).
Proof.
  intros a b H.
  induction H; eauto.
  simpl. rewrite H. rewrite IHForall2. eauto.
Qed.

(** subslice takes elements with indices [n, m) in list [l] *)
Definition subslice {A} (n m: nat) (l: list A): list A :=
  drop n (take m l).

Theorem subslice_length {A} n m (l: list A) :
  (m <= length l)%nat ->
  length (subslice n m l) = (m - n)%nat.
Proof.
  rewrite /subslice; intros.
  rewrite drop_length take_length.
  lia.
Qed.

Theorem subslice_take_drop {A} n m (l: list A) :
  subslice n m l =
  drop n (take m l).
Proof. reflexivity. Qed.

Theorem subslice_drop_take {A} n m (l: list A) :
  n ≤ m →
  subslice n m l =
  take (m-n) (drop n l).
Proof.
  intros ?.
  rewrite /subslice.
  rewrite take_drop_commute.
  f_equal. f_equal.
  lia.
Qed.

Theorem subslice_app_1 {A} n m (l1 l2: list A) :
  (m ≤ length l1)%nat →
  subslice n m (l1 ++ l2) = subslice n m l1.
Proof.
  intros.
  rewrite /subslice.
  rewrite take_app_le; auto.
Qed.

Lemma subslice_to_end {A} n m (l: list A) :
  (length l ≤ m)%nat →
  subslice n m l = drop n l.
Proof.
  intros Hbound.
  rewrite /subslice.
  rewrite take_ge; auto.
Qed.

Theorem subslice_zero_length {A} n (l: list A) :
  subslice n n l = [].
Proof.
  rewrite /subslice.
  rewrite drop_ge //.
  rewrite take_length; lia.
Qed.

Lemma subslice_none {A} n m (l: list A) :
  (m ≤ n)%nat →
  subslice n m l = [].
Proof.
  intros.
  rewrite /subslice.
  rewrite -length_zero_iff_nil.
  rewrite drop_length take_length.
  lia.
Qed.

Theorem subslice_nil {A} n m :
  subslice n m (@nil A) = [].
Proof.
  rewrite /subslice.
  rewrite take_nil drop_nil //.
Qed.

Theorem subslice_S {A} n m x (l: list A) :
  n < m →
  l !! n = Some x →
  subslice n m l = x :: subslice (S n) m l.
Proof.
  intros ? Hlookup.
  rewrite -> !subslice_drop_take by lia.
  erewrite drop_S; eauto.
  replace (m - n) with (S (m - S n)) by lia.
  rewrite //=.
Qed.

Theorem subslice_before_app_eq {A} n m (l l': list A):
  m <= length l -> subslice n m l = subslice n m (l ++ l').
Proof.
  intros.
  by rewrite /subslice take_app_le.
Qed.
