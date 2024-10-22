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
  Implicit Types x : A.
  Implicit Types l : list A.

  (** Lemmas about [extend]. *)

  Lemma extend_id n x l :
    (n ≤ length l)%nat ->
    extend n x l = l.
  Proof.
    intros Hlen. rewrite /extend. replace (n - _)%nat with O by lia.
    by rewrite /= app_nil_r.
  Qed.

  Lemma extend_length n x l :
    length (extend n x l) = (n - length l + length l)%nat.
  Proof. rewrite length_app length_replicate. lia. Qed.

  Lemma extend_length_ge_n n x l :
    (n ≤ length (extend n x l))%nat.
  Proof. rewrite extend_length. lia. Qed.

  Lemma extend_length_ge n x l :
    (length l ≤ length (extend n x l))%nat.
  Proof. rewrite length_app. lia. Qed.

  Lemma extend_prefix n x l :
    prefix l (extend n x l).
  Proof. by apply prefix_app_r. Qed.

  Lemma lookup_extend_l n i x l :
    (i < length l)%nat ->
    extend n x l !! i = l !! i.
  Proof. intros Hlt. by rewrite lookup_app_l. Qed.

  Lemma lookup_extend_r n i x l :
    (length l ≤ i < n)%nat ->
    extend n x l !! i = Some x.
  Proof. intros Hle. rewrite lookup_app_r; last lia. apply lookup_replicate_2. lia. Qed.

  (** Lemmas about [last_extend]. *)

  Lemma last_extend_id n l :
    (n ≤ length l)%nat ->
    last_extend n l = l.
  Proof.
    intros Hlen. rewrite /last_extend.
    destruct (last l) eqn:Hl; first by apply extend_id.
    symmetry.
    by apply last_None.
  Qed.

  Lemma last_extend_length n l :
    l ≠ [] ->
    length (last_extend n l) = (n - length l + length l)%nat.
  Proof.
    intros Hl. rewrite -last_is_Some in Hl. destruct Hl as [x Hl].
    rewrite /last_extend Hl extend_length.
    lia.
  Qed.

  Lemma last_extend_length_ge n l :
    (length l ≤ length (last_extend n l))%nat.
  Proof.
    destruct (decide (l = [])) as [Hnil | Hnnil].
    { by rewrite /last_extend Hnil /=. }
    rewrite last_extend_length; [lia | done].
  Qed.

  Lemma last_extend_length_eq_n n l :
    l ≠ [] ->
    (length l ≤ n)%nat ->
    length (last_extend n l) = n.
  Proof. intros Hl Hlen. rewrite last_extend_length; [lia | done]. Qed.

  Lemma last_extend_length_ge_n n l :
    l ≠ [] ->
    (n ≤ length (last_extend n l))%nat.
  Proof. intros Hl. rewrite last_extend_length; [lia | done]. Qed.

  Lemma last_extend_length_eq_n_or_same n l :
    length (last_extend n l) = n ∨ length (last_extend n l) = length l.
  Proof.
    destruct (decide (l = [])) as [-> | Hne]; first by right.
    rewrite last_extend_length; last done.
    lia.
  Qed.

  Lemma last_last_extend n l :
    last (last_extend n l) = last l.
  Proof.
    destruct (last l) as [x |] eqn:Hlast; last by rewrite /last_extend Hlast.
    rewrite /last_extend Hlast /extend last_app.
    destruct (last (replicate _ _)) eqn:Hl; last done.
    apply last_Some_elem_of, elem_of_replicate_inv in Hl.
    by rewrite Hl.
  Qed.

  Lemma lookup_last_extend_r n i l :
    (length l ≤ S i)%nat ->
    (i < n)%nat ->
    last_extend n l !! i = last l.
  Proof.
    intros Hlen Hni.
    rewrite /last_extend.
    destruct (last l) as [x |] eqn:Hl; last done.
    destruct (decide (length l = S i)) as [Heq | Hne].
    { rewrite /extend lookup_app_l; last lia.
      by rewrite last_lookup Heq /= in Hl.
    }
    assert (length l ≤ i) by lia.
    rewrite /extend lookup_app_r; last done.
    rewrite lookup_replicate.
    split; [done | lia].
  Qed.

  Lemma lookup_last_extend_l n i l :
    (i < length l) ->
    last_extend n l !! i = l !! i.
  Proof.
    intros Hi.
    rewrite /last_extend.
    destruct (last l) as [x |] eqn:Hl; last first.
    { rewrite last_None in Hl. by rewrite Hl. }
    by rewrite lookup_app_l.
  Qed.

  Lemma last_extend_twice n1 n2 l :
    last_extend n1 (last_extend n2 l) = last_extend (n1 `max` n2) l.
  Proof.
    destruct (decide (l = [])) as [-> | Hne]; first done.
    destruct (last l) as [x |] eqn:Hlast; last by rewrite last_None in Hlast.
    pose proof (last_last_extend n2 l) as Hn2.
    rewrite {1}/last_extend Hn2 Hlast /last_extend Hlast /extend -app_assoc.
    rewrite -replicate_add length_app length_replicate.
    (* wow how does lia solve this *)
    by replace (n2 - _ + _)%nat with (n1 `max` n2 - length l)%nat by lia.
  Qed.

  (* TODO: rename this to [prefix_last_extend]. *)
  Lemma last_extend_prefix n l :
    prefix l (last_extend n l).
  Proof.
    rewrite /last_extend.
    destruct (last l) as [x |] eqn:Hlast.
    { apply extend_prefix. }
    rewrite last_None in Hlast.
    by rewrite Hlast.
  Qed.

  Lemma last_extend_not_nil_inv n l :
    last_extend n l ≠ [] ->
    l ≠ [].
  Proof. intros Hext Hl. by rewrite /last_extend Hl /= in Hext. Qed.

End lemmas.
