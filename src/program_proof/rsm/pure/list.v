(** This file contain general properties about list that are not in stdpp. *)
From iris.proofmode Require Import proofmode.

Set Default Proof Using "Type".

Section lemma.
  Context {A : Type}.
  Implicit Type l : list A.

  Lemma prefix_snoc l1 l2 x :
    prefix l1 (l2 ++ [x]) ->
    prefix l1 l2 ∨ l1 = l2 ++ [x].
  Proof.
    intros Hprefix.
    destruct Hprefix as [l Hprefix].
    destruct l as [| y l].
    { right. by rewrite app_nil_r in Hprefix. }
    left.
    rewrite /prefix.
    apply app_eq_inv in Hprefix.
    destruct Hprefix as [(k & Hprefix & _) | (k & Hprefix & Hx)]; first by eauto.
    destruct k.
    { rewrite app_nil_r in Hprefix. exists nil. by rewrite app_nil_r. }
    inversion Hx as [[Ha Hcontra]].
    by apply app_cons_not_nil in Hcontra.
  Qed.

  Lemma prefix_common_ub l1 l2 l :
    prefix l1 l ->
    prefix l2 l ->
    prefix l1 l2 ∨ prefix l2 l1.
  Proof.
    generalize dependent l2.
    generalize dependent l1.
    induction l as [| x l IHl].
    { intros l1 l2 Hl1 Hl2.
      apply prefix_nil_inv in Hl1 as ->.
      left.
      apply prefix_nil.
    }
    intros l1 l2 Hl1 Hl2.
    destruct l1 as [| x' l1'].
    { left. apply prefix_nil. }
    apply prefix_cons_inv_2 in Hl1 as Hprefix1.
    apply prefix_cons_inv_1 in Hl1 as ->.
    destruct l2 as [| x' l2'].
    { right. apply prefix_nil. }
    apply prefix_cons_inv_2 in Hl2 as Hprefix2.
    apply prefix_cons_inv_1 in Hl2 as ->.
    specialize (IHl _ _ Hprefix1 Hprefix2).
    destruct IHl as [Hprefix | Hprefix].
    - left. by apply prefix_cons.
    - right. by apply prefix_cons.
  Qed.

  Lemma take_length_prefix l1 l2 :
    prefix l1 l2 ->
    take (length l1) l2 = l1.
  Proof. intros [l Happ]. by rewrite Happ take_app_length. Qed.

  Lemma NoDup_prefix l1 l2 :
    prefix l1 l2 ->
    NoDup l2 ->
    NoDup l1.
  Proof.
    intros [l Happ] Hl2. rewrite Happ in Hl2.
    by apply NoDup_app in Hl2 as [? _].
  Qed.

  Lemma not_elem_of_take l n x :
    NoDup l ->
    l !! n = Some x ->
    x ∉ take n l.
  Proof.
    intros Hnd Hx Htake.
    apply take_drop_middle in Hx.
    rewrite -Hx cons_middle NoDup_app in Hnd.
    destruct Hnd as (_ & Hnd & _).
    specialize (Hnd _ Htake).
    set_solver.
  Qed.

  Lemma not_elem_of_tail l x :
    x ∉ l ->
    x ∉ tail l.
  Proof. intros Hl. by destruct l as [| h t]; last set_solver. Qed.

  Lemma length_not_nil l :
    l ≠ [] ->
    length l ≠ O.
  Proof. intros Hnnil Hlen. by apply nil_length_inv in Hlen. Qed.

  Lemma prefix_not_nil l1 l2 :
    prefix l1 l2 ->
    l1 ≠ [] ->
    l2 ≠ [].
  Proof. intros Hprefix Hl1 Hl2. subst l2. by apply prefix_nil_inv in Hprefix. Qed.

  Lemma tail_app_l l1 l2 :
    l1 ≠ [] ->
    tail (l1 ++ l2) = tail l1 ++ l2.
  Proof. intros Hl1. by destruct l1 as [| x t]. Qed.

  Lemma head_prefix l1 l2 :
    l1 ≠ [] ->
    prefix l1 l2 ->
    head l1 = head l2.
  Proof. intros Hl1 [lp ->]. by destruct l1 as [| x t]. Qed.

  Lemma NoDup_snoc l x :
    x ∉ l ->
    NoDup l ->
    NoDup (l ++ [x]).
  Proof.
    intros Hnotin Hnd.
    apply NoDup_app.
    split; first done.
    split; last apply NoDup_singleton.
    intros y Hy Heq.
    rewrite elem_of_list_singleton in Heq.
    by subst y.
  Qed.

End lemma.
