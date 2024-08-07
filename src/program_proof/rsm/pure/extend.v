From iris.proofmode Require Import proofmode.

Set Default Proof Using "Type".

(** Definitions. *)
Definition extend {A} (n : nat) (x : A) (l : list A) :=
  l ++ replicate (n - length l) x.

Definition last_extend {A} (n : nat) (l : list A) :=
  match last l with
  | None => []
  | Some x => extend n x l
  end.

Section lemmas.
  Context {A : Type}.

  (** Lemmas about [extend]. *)
  Lemma extend_id (n : nat) (x : A) (l : list A) :
    (n ≤ length l)%nat ->
    extend n x l = l.
  Proof.
    intros Hlen. rewrite /extend. replace (n - _)%nat with O by lia.
    by rewrite /= app_nil_r.
  Qed.

  Lemma extend_length (n : nat) (x : A) (l : list A) :
    length (extend n x l) = (n - length l + length l)%nat.
  Proof. rewrite app_length replicate_length. lia. Qed.

  Lemma extend_length_ge_n (n : nat) (x : A) (l : list A) :
    (n ≤ length (extend n x l))%nat.
  Proof. rewrite extend_length. lia. Qed.

  (** Lemmas about [last_extend]. *)
  Lemma last_extend_id (n : nat) (l : list A) :
    (n ≤ length l)%nat ->
    last_extend n l = l.
  Proof.
    intros Hlen. rewrite /last_extend.
    destruct (last l) eqn:Hl; first by apply extend_id.
    symmetry.
    by apply last_None.
  Qed.

  Lemma last_extend_length (n : nat) (l : list A) :
    l ≠ [] ->
    length (last_extend n l) = (n - length l + length l)%nat.
  Proof.
    intros Hl. rewrite -last_is_Some in Hl. destruct Hl as [x Hl].
    rewrite /last_extend Hl extend_length.
    lia.
  Qed.

  Lemma last_extend_length_ge_n (n : nat) (l : list A) :
    l ≠ [] ->
    (n ≤ length (last_extend n l))%nat.
  Proof. intros Hl. rewrite last_extend_length; [lia | done]. Qed.

  Lemma last_extend_length_eq_n_or_same (n : nat) (l : list A) :
    length (last_extend n l) = n ∨ length (last_extend n l) = length l.
  Proof.
    destruct (decide (l = [])) as [-> | Hne]; first by right.
    rewrite last_extend_length; last done.
    lia.
  Qed.

  Lemma last_last_extend (n : nat) (l : list A) :
    last (last_extend n l) = last l.
  Proof.
    destruct (last l) as [x |] eqn:Hlast; last by rewrite /last_extend Hlast.
    rewrite /last_extend Hlast /extend last_app.
    destruct (last (replicate _ _)) eqn:Hl; last done.
    apply last_Some_elem_of, elem_of_replicate_inv in Hl.
    by rewrite Hl.
  Qed.

  Lemma last_extend_twice (n1 n2 : nat) (l : list A) :
    last_extend n1 (last_extend n2 l) = last_extend (n1 `max` n2) l.
  Proof.
    destruct (decide (l = [])) as [-> | Hne]; first done.
    destruct (last l) as [x |] eqn:Hlast; last by rewrite last_None in Hlast.
    pose proof (last_last_extend n2 l) as Hn2.
    rewrite {1}/last_extend Hn2 Hlast /last_extend Hlast /extend -app_assoc.
    rewrite -replicate_add app_length replicate_length.
    (* wow how does lia solve this *)
    by replace (n2 - _ + _)%nat with (n1 `max` n2 - length l)%nat by lia.
  Qed.

End lemmas.
