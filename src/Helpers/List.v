From stdpp Require Import list ssreflect.

Set Default Proof Using "Type".
Set Default Goal Selector "!".

(* these lemmas require specific forms of A, so they don't include it as a
context variable. *)
Section list_misc.

  Lemma last_replicate {A} (x : A) n :
    last (replicate n x) = match n with 0 => None | S _ => Some x end.
  Proof.
    rewrite last_lookup length_replicate.
    destruct n; [done|].
    rewrite lookup_replicate_2; [done|lia].
  Qed.

  Lemma last_replicate_option_app {A} (l : list (option A)) n :
    mjoin $ last (l ++ replicate n (mjoin $ last l)) = mjoin $ last l.
  Proof.
    rewrite last_app last_replicate.
    repeat case_match; try done.
    naive_solver.
  Qed.

End list_misc.

Section list.
  Context {A : Type}.
  Implicit Types l : (list A).

  Lemma take_0' n l :
    n = 0 →
    take n l = [].
  Proof. intros. subst. apply take_0. Qed.

  Lemma list_join_inj (c : nat) (l0 l1 : list $ list A) :
    c > 0 →
    Forall (λ x, length x = c) l0 →
    Forall (λ x, length x = c) l1 →
    mjoin l0 = mjoin l1 →
    l0 = l1.
  Proof.
    revert l1.
    induction l0; destruct l1; [done|..]; intros ? Hc0 Hc1 Heq.
    - apply (f_equal length) in Heq.
      rewrite !length_join in Heq.
      list_simplifier. lia.
    - apply (f_equal length) in Heq.
      rewrite !length_join in Heq.
      list_simplifier. lia.
    - simpl in *.
      apply Forall_cons in Hc0 as [??].
      apply Forall_cons in Hc1 as [??].
      eapply (app_inj_1 _) in Heq as [-> ?]; [|lia].
      f_equal.
      by eapply IHl0.
  Qed.

  Lemma Forall_snoc (P : A → Prop) (x : A) l :
    Forall P (l ++ [x]) ↔ Forall P l ∧ P x.
  Proof.
    split; intros H.
    - apply Forall_app in H as [H1 H2].
      by eapply (proj1 (Forall_singleton _ _)) in H2.
    - destruct H as [H1 H2].
      apply Forall_app.
      split; [done|].
      by apply Forall_singleton.
  Qed.

  Lemma filter_snoc (P : A → Prop) `{∀ x, Decision (P x)} l x :
    filter P (l ++ [x]) = filter P l ++ (if decide (P x) then [x] else []).
  Proof. by rewrite filter_app. Qed.

  Lemma prefix_to_take (l0 l1 : list A) :
    l0 `prefix_of` l1 →
    l0 = take (length l0) l1.
  Proof.
    intros [? Hpref].
    apply (f_equal (take (length l0))) in Hpref.
    by rewrite take_app_length in Hpref.
  Qed.

  Lemma prefix_fmap {B} (f : A → B) (l0 l1 : list A) :
    l0 `prefix_of` l1 →
    f <$> l0 `prefix_of` f <$> l1.
  Proof.
    unfold prefix. intros [? Heq].
    apply (f_equal (fmap f)) in Heq.
    rewrite fmap_app in Heq.
    naive_solver.
  Qed.

  Lemma drop_eq_0 n l :
    n = 0 →
    drop n l = l.
  Proof.
    intros ->. rewrite drop_0 //.
  Qed.

  Lemma replicate_0 (x: A) :
    replicate 0 x = [].
  Proof. reflexivity. Qed.

  Lemma replicate_eq_0 (n: nat) (x: A) :
    n = 0 →
    replicate n x = [].
  Proof. intros ->. reflexivity. Qed.

  Lemma list_filter_singleton (P : A → Prop)
      `{!∀ x, Decision (P x)} x :
    (filter P [x] = [] ∧ ¬ P x) ∨ (filter P [x] = [x] ∧ P x).
  Proof.
    destruct (decide $ P x).
    - right. split; [|done]. rewrite filter_cons_True; [naive_solver|done].
    - left. split; [|done]. rewrite filter_cons_False; [naive_solver|done].
  Qed.

  Lemma list_filter_iff_strong (P1 P2 : A → Prop)
      `{!∀ x, Decision (P1 x), !∀ x, Decision (P2 x)} l :
    (∀ i x, l !! i = Some x → (P1 x ↔ P2 x)) →
    filter P1 l = filter P2 l.
  Proof.
    intros HPiff. induction l as [|a l IH]; [done|].
    opose proof (HPiff 0 a _) as ?; [done|].
    ospecialize (IH _). { intros i x ?. by ospecialize (HPiff (S i) x _). }
    destruct (decide (P1 a)).
    - rewrite !filter_cons_True; [|by naive_solver..]. by rewrite IH.
    - rewrite !filter_cons_False; [|by naive_solver..]. by rewrite IH.
  Qed.

  Lemma list_filter_all (P : A → Prop)
      `{!∀ x, Decision (P x)} l :
    (∀ i x, l !! i = Some x → P x) →
    filter P l = l.
  Proof.
    intros HP. induction l as [|a l IH]; [done|].
    opose proof (HP 0 a _) as ?; [done|].
    ospecialize (IH _). { intros i x ?. by ospecialize (HP (S i) x _). }
    rewrite filter_cons_True; [|done]. by rewrite IH.
  Qed.

  Lemma lookup_snoc l x :
    (l ++ [x]) !! (length l) = Some x.
  Proof.
    opose proof (proj2 (lookup_snoc_Some _ _ (length l) x) _) as ?;
      [naive_solver|done].
  Qed.

  Lemma list_singleton_exists l :
    length l = 1 →
    ∃ x, l = [x].
  Proof.
    intros Hlen.
    destruct l as [|x0 l0].
    - list_simplifier.
    - destruct l0.
      + eauto.
      + list_simplifier.
  Qed.

  Lemma list_snoc_exists l :
    length l > 0 →
    ∃ l' x, l = l' ++ [x].
  Proof.
    intros Hlen.
    assert (∃ x0, drop (pred (length l)) l = [x0]) as [x0 Hlast].
    {
      pose proof (length_drop l (pred (length l))) as Hlen_drop.
      replace (length _ - pred (length _)) with (1) in Hlen_drop by lia.
      apply list_singleton_exists in Hlen_drop as [x0' ->].
      eauto.
    }
    exists (take (pred (length l)) l), x0.
    rewrite -Hlast.
    rewrite take_drop.
    eauto.
  Qed.

  Lemma map_neq_nil {B: Type} (f: A → B) (l: list A): l ≠ [] → map f l ≠ [].
  Proof. induction l => //=. Qed.

  Lemma length_nonzero_neq_nil (l: list A): (0 < length l)%nat → l ≠ [].
  Proof. induction l => //=. inversion 1. Qed.

  Lemma drop_lt (l : list A) (n : nat): (n < length l)%nat → drop n l ≠ [].
  Proof.  intros. eapply length_nonzero_neq_nil. rewrite length_drop. lia. Qed.

  Lemma list_lookup_lt (l: list A) (i: nat) :
    (i < length l)%nat ->
    exists x, l !! i = Some x.
  Proof.
    intros.
    destruct_with_eqn (l !! i); eauto.
    exfalso.
    apply lookup_ge_None in Heqo.
    lia.
  Qed.

  Lemma list_fmap_map {B} (f: A → B) (l: list A):
    f <$> l = map f l.
  Proof. reflexivity. Qed.

  Definition Forall_idx (P: nat -> A -> Prop) (start:nat) (l: list A): Prop :=
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
    rewrite length_drop -drop_seq.
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

  (* for compatibility with Coq v8.11, which doesn't have this lemma *)
  Lemma in_concat : forall (l: list (list A)) y,
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

  Lemma concat_insert_app : forall (index: nat) (l: list (list A)) (x: list A),
    index < length l ->
    concat (<[index := x]> l) = (concat (take index l)) ++ x ++ (concat (drop (index+1) l)).
  Proof.
    intros.
    rewrite insert_take_drop //.
    rewrite concat_app concat_cons.
    by replace (index + 1) with (S index) by lia.
  Qed.

  (* copied from Coq 8.12+alpha for 8.11 compatibility *)
  Lemma Permutation_app_swap_app : forall (l1 l2 l3: list A),
    Permutation (l1 ++ l2 ++ l3) (l2 ++ l1 ++ l3).
  Proof.
    intros.
    rewrite -> 2 app_assoc.
    apply Permutation_app_tail, Permutation_app_comm.
  Qed.

End list.

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

Lemma take_subslice {A} (n m : nat) (l : list A) :
  n ≤ m →
  take m l = take n l ++ subslice n m l.
Proof.
  intros. rewrite /subslice.
  replace (m) with (n + (m - n)) by lia.
  by rewrite -take_drop_commute -take_take_drop.
Qed.

Theorem subslice_length' {A} n m (l: list A) :
  length (subslice n m l) = (m `min` length l - n)%nat.
Proof.
  rewrite /subslice.
  rewrite length_drop length_take.
  auto.
Qed.

Theorem subslice_length {A} n m (l: list A) :
  (m <= length l)%nat ->
  length (subslice n m l) = (m - n)%nat.
Proof.
  intros.
  rewrite subslice_length'.
  lia.
Qed.

Theorem subslice_take_drop {A} n m (l: list A) :
  subslice n m l =
  drop n (take m l).
Proof. reflexivity. Qed.

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
  rewrite length_take; lia.
Qed.

Lemma subslice_none {A} n m (l: list A) :
  (m ≤ n)%nat →
  subslice n m l = [].
Proof.
  intros.
  rewrite /subslice.
  rewrite -length_zero_iff_nil.
  rewrite length_drop length_take.
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
    rewrite length_take_le; lia.
  - rewrite length_take_le; lia.
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

Local Lemma subslice_subslice_trivial {A} (l: list A) n m n' m' :
  n > m →
  subslice n' m' (subslice n m l) =
    subslice (n + n') (n + m' `min` (m-n)) l.
Proof.
  intros Hgt.
  rewrite (subslice_none n m); [|lia].
  rewrite subslice_nil.
  rewrite subslice_none //.
  lia.
Qed.

Lemma subslice_subslice {A} (l: list A) n m n' m' :
  subslice n' m' (subslice n m l) = subslice (n + n') (n + m' `min` (m-n)) l.
Proof.
  destruct (decide (n ≤ m)).
  - rewrite (subslice_drop_take n m) //.
    rewrite subslice_take.
    rewrite subslice_drop.
    auto.
  - rewrite subslice_subslice_trivial //.
    lia.
Qed.

Lemma subslice_subslice' {A} (l: list A) n m n' m' :
  m' ≤ m - n →
  subslice n' m' (subslice n m l) = subslice (n + n') (n + m') l.
Proof.
  intros Hle.
  rewrite subslice_subslice.
  f_equal; lia.
Qed.

Lemma drop_subslice {A} (l: list A) n m k :
  drop k (subslice n m l) = subslice (n + k) m l.
Proof.
  destruct (decide (n ≤ m)).
  - destruct (decide (m ≤ length l)).
    + rewrite subslice_from_drop.
      rewrite subslice_length' //.
      rewrite subslice_subslice.
      rewrite -> Nat.min_l by lia.
      rewrite -> Nat.min_l by lia.
      f_equal; lia.
    + repeat rewrite -> subslice_to_end by lia.
      rewrite drop_drop //.
  - rewrite -> subslice_none by lia.
    rewrite -> subslice_none by lia.
    rewrite drop_nil //.
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
  2: { rewrite length_take_le; lia. }
  f_equal.
  rewrite -> drop_app_le.
  2: { rewrite length_take_le; lia. }
  rewrite -> (drop_ge (take m l)).
  2: { rewrite length_take_le; lia. }
  auto.
Qed.

Lemma subslice_lookup A (n m i : nat) (l : list A) :
  (n + i < m)%nat ->
  subslice n m l !! i = l !! (n + i)%nat.
Proof.
  intros.
  unfold subslice.
  rewrite lookup_drop.
  rewrite lookup_take_lt; auto.
Qed.

Lemma subslice_lookup_bound A (n m i : nat) (l : list A) :
  is_Some (subslice n m l !! i) ->
  (n + i < m)%nat.
Proof.
  unfold subslice.
  intros.
  apply lookup_lt_is_Some_1 in H.
  rewrite length_drop in H.
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

#[local]
Lemma list_split2 {A} (l: list A) (i1 i2: nat) (x1 x2: A) :
  (i1 < i2)%nat →
  l !! i1 = Some x1 →
  l !! i2 = Some x2 →
  l = take i1 l ++ [x1] ++ subslice (S i1) i2 l ++ [x2] ++ drop (S i2) l.
Proof.
  intros Hlt Hget1 Hget2.
  assert (i1 < i2 < length l)%nat.
  { apply lookup_lt_Some in Hget1.
    apply lookup_lt_Some in Hget2.
    lia. }
  trans (take i1 l ++ [x1] ++ drop (S i1) l).
  {
    rewrite -{1}(list_insert_id l i1 x1) //.
    rewrite -> insert_take_drop by lia.
    auto.
  }
  f_equal.
  f_equal.
  rewrite -{1}(list_insert_id l i2 x2) //.
  rewrite -> drop_insert_ge by lia.
  rewrite -> insert_take_drop.
  2: {
    rewrite length_drop; lia.
  }
  rewrite -> subslice_drop_take by lia.
  simpl.
  do 2 f_equal.
  rewrite drop_drop.
  f_equal; lia.
Qed.

Lemma list_insert_middle {A} (l1 l2: list A) i x1 x2 :
  i = length l1 →
  <[i := x2]> (l1 ++ [x1] ++ l2) = l1 ++ [x2] ++ l2.
Proof.
  intros; subst.
  rewrite -> insert_app_r_alt by lia.
  f_equal.
  replace (length l1 - length l1)%nat with 0%nat by lia; auto.
Qed.

Lemma Permutation_insert_swap {A} (l: list A) (i1 i2: nat) (x1 x2: A) :
  l !! i1 = Some x1 →
  l !! i2 = Some x2 →
  <[i2 := x1]> (<[i1 := x2]> l) ≡ₚ l.
Proof.
  wlog: i1 i2 x1 x2 / i1 < i2.
  {
    intros Hordered Hget1 Hget2.
    (* this case is exactly Hordered *)
    destruct (decide (i1 < i2)).
    { apply Hordered; auto. }
    (* special case *)
    destruct (decide (i1 = i2)); subst.
    { rewrite list_insert_insert_eq list_insert_id //. }
    (* this is the symmetric case, by appeal to Hordered *)
    assert (i2 < i1) by lia.
    rewrite -> list_insert_insert_ne by lia.
    apply Hordered; auto.
  }
  intros Hlt Hget1 Hget2.
  assert (i1 < i2 < length l)%nat.
  { apply lookup_lt_Some in Hget1.
    apply lookup_lt_Some in Hget2.
    lia. }
  rewrite -> (list_split2 l i1 i2 x1 x2) by auto.
  rewrite list_insert_middle.
  2: { rewrite length_take; lia. }
  do 2 rewrite app_assoc.
  rewrite list_insert_middle.
  2: { rewrite !length_app ?length_take ?subslice_length' /=; lia. }
  rewrite -!app_assoc.
  f_equiv.
  simpl.
  rewrite !Permutation_middle.
  f_equiv.
  rewrite Permutation_swap //.
Qed.

Lemma subslice_app_length {A} n m (l0 l1 : list A) :
  subslice ((length l0) + n) ((length l0) + m) (l0 ++ l1) =
  subslice n m l1.
Proof. by rewrite /subslice take_app_add drop_app_add. Qed.

Lemma join_lookup_Some_same_length'' {A} i c (x : list A) ls :
  Forall (λ x, length x = c) ls →
  ls !! i = Some x →
  x = subslice (i * c) (S i * c) (mjoin ls).
Proof.
  revert i. induction ls.
  { intros ?? Hlook. by rewrite lookup_nil in Hlook. }
  intros ? Hc ?.
  apply Forall_cons in Hc as [<- ?].
  destruct i.
  - rewrite subslice_from_start.
    rewrite take_app_length'; [|lia].
    naive_solver.
  - rewrite subslice_app_length.
    by apply IHls.
Qed.

Lemma subslice_singleton {A} l n (x : A) :
  l !! n = Some x →
  subslice n (S n) l = [x].
Proof.
  intros Hlook. rewrite /subslice.
  eapply lookup_lt_Some in Hlook as ?.
  eapply take_drop_middle in Hlook as <-.
  rewrite cons_middle.
  rewrite (assoc app).
  rewrite take_app_length'.
  2: { rewrite app_length length_take. simpl. lia. }
  rewrite drop_app_length'; [done|].
  rewrite length_take. lia.
Qed.

Local Lemma join_subslice_aux {A} i k c (ls : list $ list A) :
  i ≤ i + k ≤ length ls →
  Forall (λ x, length x = c) ls →
  mjoin (subslice i (k + i) ls) = subslice (i * c) ((k + i) * c) (mjoin ls).
Proof.
  intros. induction k.
  { by rewrite !subslice_zero_length. }
  rewrite (subslice_split_r _ (k + i)); [|lia..].
  rewrite join_app.
  rewrite (subslice_split_r (i * c) ((k + i) * c)); [|lia|].
  2: {
    rewrite length_join.
    rewrite (sum_list_fmap_same c); [|done].
    eapply Nat.mul_le_mono_r. lia. }
  f_equal. { apply IHk. lia. }
  clear IHk.
  destruct (list_lookup_lt ls (k + i)) as [x Hlook]; [lia|].
  pose proof Hlook as Hlook0.
  replace (S k + i) with (S (k + i)) by lia.
  eapply subslice_singleton in Hlook0 as ->.
  list_simplifier.
  by rewrite -(join_lookup_Some_same_length'' _ _ x).
Qed.

Lemma join_subslice {A} i j c (ls : list $ list A) :
  i ≤ j ≤ length ls →
  Forall (λ x, length x = c) ls →
  mjoin (subslice i j ls) = subslice (i * c) (j * c) (mjoin ls).
Proof.
  intros.
  replace (j) with ((j - i) + i) by lia.
  eapply join_subslice_aux; [lia|done].
Qed.
