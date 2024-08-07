(** This file contain general properties about list that are not in stdpp. *)
From iris.proofmode Require Import proofmode.

Set Default Proof Using "Type".

Section lemma.
  Context {A : Type}.

  Lemma prefix_snoc (l1 l2 : list A) x :
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

  Lemma take_length_prefix (l1 l2 : list A) :
    prefix l1 l2 ->
    take (length l1) l2 = l1.
  Proof. intros [l Happ]. by rewrite Happ take_app_length. Qed.

  Lemma NoDup_prefix (l1 l2 : list A) :
    prefix l1 l2 ->
    NoDup l2 ->
    NoDup l1.
  Proof.
    intros [l Happ] Hl2. rewrite Happ in Hl2.
    by apply NoDup_app in Hl2 as [? _].
  Qed.

  Lemma not_elem_of_take (l : list A) n x :
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

End lemma.
