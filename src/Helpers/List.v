From stdpp Require Import list list_numbers.
From Coq Require Import ssreflect.

Section list.
  Context (A:Type).
  Notation list := (list A).
  Implicit Types (l:list).

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
End list.
