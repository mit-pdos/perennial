From stdpp Require Import list.
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
    pose proof (lookup_seq_inv _ _ _ _ H); intuition subst.
    apply H0; eauto.
  Qed.
End list.
