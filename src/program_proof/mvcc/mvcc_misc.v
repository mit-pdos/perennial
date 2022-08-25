From Perennial.program_proof Require Import mvcc_prelude.

(**
 * This file contains what I wish to have in stdpp.
 *)

(* Q: Existing tactic does this? *)
Lemma ite_apply (A B : Type) (b : bool) (f : A -> B) x y :
  (if b then f x else f y) = f (if b then x else y).
Proof. destruct b; done. Qed.

Lemma list_delete_insert_delete {A} (l : list A) i v :
  (i < length l)%nat ->
  delete i (<[i := v]> l) = delete i l.
Proof.
  intros.
  rewrite insert_take_drop; last done.
  rewrite delete_take_drop.
  replace i with (length (take i l)) at 1; last first.
  { apply take_length_le. lia. }
  rewrite take_app.
  rewrite cons_middle.
  replace (S i) with (length (take i l ++ [v])); last first.
  { rewrite app_length.
    simpl.
    rewrite take_length_le; last lia.
    lia.
  }
  rewrite app_assoc.
  rewrite drop_app.
  rewrite app_length.
  simpl.
  rewrite take_length_le; last lia.
  replace (i + 1)%nat with (S i)%nat by lia.
  by rewrite -delete_take_drop.
Qed.
  
Lemma list_to_map_insert {A} `{FinMap K M} (l : list (K * A)) k v v' i :
  NoDup l.*1 ->
  l !! i = Some (k, v) ->
  <[k := v']> (list_to_map l) =@{M A} list_to_map (<[i := (k, v')]> l).
Proof.
  intros.
  apply lookup_lt_Some in H8 as Hlength.
  apply delete_Permutation in H8 as Hperm.
  apply Permutation_sym in Hperm.
  rewrite -(list_to_map_proper ((k, v) :: (delete i l)) l); last done; last first.
  { apply NoDup_Permutation_proper with l.*1; [by apply fmap_Permutation | done]. }
  set l' := <[_:=_]> l.
  assert (Hlookup : l' !! i = Some (k, v')).
  { rewrite list_lookup_insert; auto. }
  apply delete_Permutation in Hlookup as Hperm'.
  apply Permutation_sym in Hperm'.
  rewrite -(list_to_map_proper ((k, v') :: (delete i l')) l'); last done; last first.
  { apply NoDup_Permutation_proper with l'.*1; first by apply fmap_Permutation.
    rewrite list_fmap_insert.
    simpl.
    rewrite list_insert_id; first done.
    rewrite list_lookup_fmap.
    by rewrite H8.
  }
  do 2 rewrite list_to_map_cons.
  rewrite insert_insert.
  by rewrite list_delete_insert_delete.
Qed.

Lemma list_swap_with_end {A} (l : list A) (i : nat) (xlast xi : A) :
  (i < pred (length l))%nat ->
  last l = Some xlast ->
  l !! i = Some xi ->
  <[i := xlast]> (removelast l) ≡ₚ delete i l.
Proof.
  intros Hlt Hlast Hi.
  apply last_Some in Hlast as [l' El].
  rewrite El.
  assert (Hlen : length l' = pred (length l)).
  { rewrite El. rewrite last_length. lia. }
  (* RHS *)
  rewrite delete_take_drop.
  rewrite take_app_le; last lia.
  rewrite drop_app_le; last lia.
  (* LHS *)
  rewrite removelast_last.
  rewrite insert_take_drop; last lia.
  apply Permutation_app_head.
  apply Permutation_cons_append.
Qed.

Lemma list_insert_at_end {A} (l : list A) (x : A) :
  l ≠ [] ->
  <[pred (length l) := x]> l = (removelast l) ++ [x].
Proof.
  intros Hnotnil.
  destruct (@nil_or_length_pos A l); first contradiction.
  rewrite insert_take_drop; last lia.
  rewrite -removelast_firstn_len.
  replace (S _) with (length l); last lia.
  by rewrite drop_all.
Qed.

Lemma set_Forall_subseteq {A C : Type} `{SemiSet A C} (P : A -> Prop) (X Y : C) :
  X ⊆ Y ->
  set_Forall P Y ->
  set_Forall P X.
Proof.
  intros Hsubseteq HY.
  intros x Helem.
  apply (elem_of_weaken _ _ Y) in Helem; last auto.
  by apply HY in Helem.
Qed.

#[local]
Lemma NoDup_app_comm_1 {A : Type} (l m : list A) :
  NoDup (l ++ m) -> NoDup (m ++ l).
Proof.
  intros H.
  apply NoDup_app in H as (Hl & Hlm & Hm).
  apply NoDup_app.
  split; first done.
  split; last done.
  intros x Helem Helem'.
  apply Hlm in Helem'.
  contradiction.
Qed.

Lemma NoDup_app_comm {A : Type} (l m : list A) :
  NoDup (l ++ m) ↔ NoDup (m ++ l).
Proof. split; by apply NoDup_app_comm_1. Qed.

Lemma NoDup_app_assoc_1 (A : Type) (l m n : list A) :
  NoDup (l ++ m ++ n) -> NoDup ((l ++ m) ++ n).
Proof.
  intros H.
  apply NoDup_app in H as (Hl & Hlmn & Hmn).
  apply NoDup_app in Hmn as (Hm & Hmn & Hn).
  apply NoDup_app.
  split.
  { apply NoDup_app.
    split; first done.
    split; [set_solver | done].
  }
  split; [set_solver | done].
Qed.

Lemma NoDup_app_assoc_2 (A : Type) (l m n : list A) :
  NoDup ((l ++ m) ++ n) -> NoDup (l ++ m ++ n).
Proof.
  intros H.
  apply NoDup_app in H as (Hlm & Hlmn & Hn).
  apply NoDup_app in Hlm as (Hl & Hlm & Hm).
  apply NoDup_app.
  split; first done.
  split; first set_solver.
  apply NoDup_app.
  split; first done.
  split; [set_solver | done].
Qed.

Lemma NoDup_app_assoc {A : Type} (l m n : list A) :
  NoDup (l ++ m ++ n) ↔ NoDup ((l ++ m) ++ n).
Proof. split; [apply NoDup_app_assoc_1 | apply NoDup_app_assoc_2]. Qed.

Lemma take_S_insert {A : Type} (l : list A) (i : nat) (x : A) :
  (i < length l)%nat ->
  take (S i) (<[i := x]> l) = take i l ++ [x].
Proof.
  intros Hlen.
  rewrite (take_S_r _ _ x); last by apply list_lookup_insert.
  rewrite take_insert; [done | lia].
Qed.

(* Definition and lemmas about [extend]. *)
Definition extend {X : Type} (n : nat) (l : list X) :=
  match last l with
  | None => []
  | Some v => l ++ replicate (n - length l) v
  end.

Lemma extend_last {X : Type} (n : nat) (l : list X) :
  last (extend n l) = last l.
Proof.
  unfold extend.
  destruct (last l) eqn:Elast; last done.
  rewrite last_app.
  destruct (last (replicate _ _)) eqn:Erep; last auto.
  apply last_Some_elem_of in Erep.
  apply elem_of_replicate_inv in Erep.
  by f_equal.
Qed.

Lemma extend_length {X : Type} (n : nat) (l : list X) :
  (∃ x, last l = Some x) ->
  length (extend n l) = (n - length l + length l)%nat.
Proof.
  intros [x Hlast].
  unfold extend.
  rewrite Hlast app_length replicate_length.
  lia.
Qed.

Lemma extend_length_ge {X : Type} (n : nat) (l : list X) :
  (length l ≤ length (extend n l))%nat.
Proof.
  unfold extend.
  destruct (last l) eqn:E.
  - rewrite app_length. lia.
  - apply last_None in E. by rewrite E.
Qed.

Lemma extend_length_ge_n {X : Type} (n : nat) (l : list X) :
  (∃ x, last l = Some x) ->
  (n ≤ length (extend n l))%nat.
Proof.
  intros [x Hlast].
  unfold extend.
  rewrite Hlast.
  rewrite app_length.
  rewrite replicate_length.
  lia.
Qed.

Lemma extend_length_same {X : Type} (n : nat) (l : list X) :
  (n ≤ length l)%nat ->
  extend n l = l.
Proof.
  intros Hlen.
  unfold extend.
  destruct (last l) eqn:E.
  - replace (n - length l)%nat with 0%nat by lia. simpl. apply app_nil_r.
  - symmetry. by apply last_None.
Qed.

Lemma extend_last_Some {X : Type} (n : nat) (l : list X) (x : X) :
  last l = Some x ->
  extend n l = l ++ replicate (n - length l) x.
Proof. intros Hlast. unfold extend. by rewrite Hlast. Qed.

Lemma extend_prefix {X : Type} (n : nat) (l : list X) :
  prefix l (extend n l).
Proof.
  unfold extend.
  destruct (last l) eqn:E.
  - unfold prefix. eauto.
  - rewrite last_None in E. by rewrite E.
Qed.
