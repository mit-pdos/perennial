From stdpp Require Import list list_numbers.
From Coq Require Import ssreflect.

Set Default Proof Using "Type".
Set Default Goal Selector "!".

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
  Proof. reflexivity. Qed.

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

  Lemma prefix_lookup_lt l1 l2 i :
    i < length l1 →
    l1 `prefix_of` l2 →
    l1 !! i = l2 !! i.
  Proof.
    intros Hlt Hprefix.
    apply lookup_lt_is_Some_2 in Hlt as [? Hlookup].
    rewrite Hlookup.
    eapply prefix_lookup_Some in Hlookup; eauto.
  Qed.

  Lemma list_prefix_eq l1 l2 :
    l1 `prefix_of` l2 → length l2 ≤ length l1 → l1 = l2.
  Proof.
    intros Hprefix Hlen.
    assert (length l1 = length l2).
    { apply prefix_length in Hprefix; lia. }
    eapply list_eq_same_length; [ done | done | ].
    intros i x y ? Hlookup1 Hlookup2.
    eapply prefix_lookup_Some in Hlookup1; eauto.
    congruence.
  Qed.
End list.

(* section for more specific list lemmas that aren't for arbitrary [list A] *)
Section list.
  (* for compatibility with Coq v8.11, which doesn't have this lemma *)
  Lemma in_concat {A} : forall (l: list (list A)) y,
    In y (concat l) <-> exists x, In x l /\ In y x.
  Proof.
    induction l; simpl; split; intros.
    - contradiction.
    - destruct H as (x,(H,_)); contradiction.
    - destruct (in_app_or _ _ _ H).
      + exists a; auto.
      + destruct (IHl y) as (H1,_); destruct (H1 H0) as (x,(H2,H3)).
        exists x; auto.
    - apply in_or_app.
      destruct H as (x,(H0,H1)); destruct H0.
      + subst; auto.
      + right; destruct (IHl y) as (_,H2); apply H2.
        exists x; auto.
  Qed.

  Lemma concat_insert_app {A} : forall (index: nat) (l: list (list A)) (x: list A),
    index < length l ->
    concat (<[index := x]> l) = (concat (take index l)) ++ x ++ (concat (drop (index+1) l)).
  Proof.
    intros.
    rewrite insert_take_drop //.
    rewrite concat_app concat_cons.
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

Lemma subslice_from_take {A} m (l: list A) :
  take m l = subslice 0 m l.
Proof.
  rewrite /subslice //.
Qed.

Lemma subslice_from_drop {A} n (l: list A) :
  drop n l = subslice n (length l) l.
Proof.
  rewrite /subslice.
  rewrite take_ge; auto.
Qed.

Lemma subslice_complete {A} (l: list A) :
  l = subslice 0 (length l) l.
Proof.
  rewrite subslice_take_drop.
  rewrite drop_0 take_ge //.
Qed.

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

Theorem subslice_app_contig {A} n1 n2 n3 (l: list A) :
  n1 ≤ n2 ≤ n3 →
  subslice n1 n2 l ++ subslice n2 n3 l = subslice n1 n3 l.
Proof.
  intros Hbound; intuition.
  rewrite /subslice.
  rewrite -(drop_take_drop (take n3 l) n1 n2) //.
  rewrite take_take Nat.min_l //.
Qed.

Lemma subslice_to_end {A} n m (l: list A) :
  (length l ≤ m)%nat →
  subslice n m l = drop n l.
Proof.
  intros Hbound.
  rewrite /subslice.
  rewrite take_ge; auto.
Qed.

Lemma subslice_from_start {A} n (l: list A) :
  subslice 0 n l = take n l.
Proof.
  eauto.
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

Theorem subslice_suffix_eq {A} (l l': list A) n n' m:
  n ≤ n' ->
  subslice n m l = subslice n m l' ->
  subslice n' m l = subslice n' m l'.
Proof.
  rewrite /subslice. intros.
  replace n' with (n + (n'-n)) by lia.
  rewrite -?drop_drop.
  rewrite H0. reflexivity.
Qed.

Lemma take_more {A} (n m: nat) (l: list A) :
  (n ≤ length l)%nat →
  take (n + m) l = take n l ++ take m (drop n l).
Proof.
  intros Hbound.
  rewrite -{1}(take_drop n l).
  rewrite -> take_app_ge.
  - f_equal.
    f_equal.
    rewrite take_length_le; lia.
  - rewrite take_length_le; lia.
Qed.

Lemma subslice_def {A} (n m: nat) (l: list A) :
  subslice n m l = drop n (take m l).
Proof. reflexivity. Qed.

Lemma subslice_comm {A} (n m: nat) (l: list A) :
  subslice n m l = take (m - n)%nat (drop n l).
Proof. rewrite /subslice skipn_firstn_comm //. Qed.

(** this is a way to re-fold subslice after commuting it, a useful inverse to
[subslice_comm] *)
Lemma subslice_take_drop' {A} (n k: nat) (l: list A) :
  take k (drop n l) = subslice n (n + k) l.
Proof. rewrite /subslice firstn_skipn_comm //. Qed.

Lemma subslice_take {A} (l: list A) n m k :
  subslice n m (take k l) = subslice n (m `min` k) l.
Proof.
  rewrite subslice_take_drop.
  rewrite take_take //.
Qed.

Lemma subslice_take_all {A} (l: list A) n m k :
  m ≤ k →
  subslice n m (take k l) = subslice n m l.
Proof.
  intros.
  rewrite subslice_take.
  rewrite Nat.min_l //.
Qed.

Lemma subslice_drop {A} (l: list A) n m k :
  subslice n m (drop k l) = subslice (k + n) (k + m) l.
Proof.
  destruct (decide (n ≤ m)).
  - rewrite subslice_drop_take //.
    rewrite drop_drop.
    rewrite subslice_take_drop'.
    f_equal.
    lia.
  - rewrite -> subslice_none by lia.
    rewrite -> subslice_none by lia.
    auto.
Qed.

Theorem subslice_split_r {A} n m m' (l: list A) :
  (n ≤ m ≤ m')%nat →
  (m ≤ length l)%nat →
  subslice n m' l = subslice n m l ++ subslice m m' l.
Proof.
  intros Hbound1 Hbound2.
  rewrite /subslice.
  replace m' with (m + (m' - m))%nat by lia.
  rewrite -> take_more by lia.
  rewrite -> drop_app_le.
  2: { rewrite take_length_le; lia. }
  f_equal.
  rewrite -> drop_app_le.
  2: { rewrite take_length_le; lia. }
  rewrite -> (drop_ge (take m l)).
  2: { rewrite take_length_le; lia. }
  auto.
Qed.

Lemma subslice_lookup A (n m i : nat) (l : list A) :
  (n + i < m)%nat ->
  subslice n m l !! i = l !! (n + i)%nat.
Proof.
  intros.
  unfold subslice.
  rewrite lookup_drop.
  rewrite lookup_take; auto.
Qed.

Lemma subslice_lookup_bound A (n m i : nat) (l : list A) :
  is_Some (subslice n m l !! i) ->
  (n + i < m)%nat.
Proof.
  unfold subslice.
  intros.
  apply lookup_lt_is_Some_1 in H.
  rewrite drop_length in H.
  pose proof (firstn_le_length m l).
  lia.
Qed.

Lemma subslice_lookup_bound' A (n m i : nat) (l : list A) a :
  subslice n m l !! i = Some a ->
  (n + i < m)%nat.
Proof.
  intros.
  eapply subslice_lookup_bound; eauto.
Qed.

Lemma subslice_lookup_some A (n m i : nat) (l : list A) (a : A) :
  subslice n m l !! i = Some a ->
  l !! (n + i)%nat = Some a.
Proof.
  intros.
  pose proof H as H'.
  rewrite subslice_lookup in H'; eauto.
  eapply subslice_lookup_bound. eauto.
Qed.

Lemma fmap_subslice {A B} (f: A → B) (l: list A) n m :
  f <$> subslice n m l = subslice n m (f <$> l).
Proof.
  rewrite !subslice_take_drop fmap_drop fmap_take //.
Qed.
