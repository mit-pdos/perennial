From iris.proofmode Require Import proofmode.
From Perennial.program_proof.rsm.pure Require Export dual_lookup.

Set Default Proof Using "Type".

Definition vslice_step `{Countable K1} `{Countable K2} {V}
  (k2 : K2) (k1 : K1) (m2 : gmap K2 V) (m1 : gmap K1 V) :=
  match m2 !! k2 with
  | Some v => <[k1 := v]> m1
  | None => m1
  end.

Definition vslice `{Countable K1} `{Countable K2} {V}
  (m : gmap K1 (gmap K2 V)) (k : K2) :=
  map_fold (vslice_step k) ∅ m.

(* TODO: move [dual_lookup] to here. *)

Section lemma.
  Context `{Countable K1} `{Countable K2} {V  : Type}.

  Lemma lookup_vslice (m : gmap K1 (gmap K2 V)) k1 k2 :
    vslice m k2 !! k1 = dual_lookup m k1 k2.
  Proof.
    apply (map_fold_weak_ind (λ r m, r !! k1 = dual_lookup m k1 k2)).
    { by rewrite /dual_lookup lookup_empty. }
    intros x m2 m' m1 Hnone IH.
    rewrite /vslice_step /dual_lookup.
    destruct (m2 !! k2) as [v |] eqn:Hv.
    - destruct (decide (x = k1)) as [-> | Hne].
      + by rewrite 2!lookup_insert_eq.
      + by do 2 (rewrite lookup_insert_ne; last done).
    - destruct (decide (x = k1)) as [-> | Hne].
      + by rewrite lookup_insert_eq IH /dual_lookup Hnone.
      + by rewrite lookup_insert_ne.
  Qed.

  Lemma vslice_insert_Some (m : gmap K1 (gmap K2 V)) (im : gmap K2 V) k1 k2 v :
    im !! k2 = Some v ->
    vslice (<[k1 := im]> m) k2 = <[k1 := v]> (vslice m k2).
  Proof.
    intros Him.
    apply map_eq. intros x.
    rewrite lookup_vslice /dual_lookup.
    destruct (decide (x = k1)) as [-> | Hne].
    - by rewrite 2!lookup_insert_eq.
    - do 2 (rewrite lookup_insert_ne; last done).
      by rewrite lookup_vslice /dual_lookup.
  Qed.

  Lemma vslice_insert_None (m : gmap K1 (gmap K2 V)) (im : gmap K2 V) k1 k2 :
    m !! k1 = None ->
    im !! k2 = None ->
    vslice (<[k1 := im]> m) k2 = vslice m k2.
  Proof.
    intros Hm Him.
    apply map_eq. intros x.
    do 2 (rewrite lookup_vslice /dual_lookup).
    destruct (decide (x = k1)) as [-> | Hne].
    - by rewrite lookup_insert_eq Hm.
    - by rewrite lookup_insert_ne.
  Qed.

  Lemma vslice_delete (m : gmap K1 (gmap K2 V)) k1 k2 :
    vslice (delete k1 m) k2 = delete k1 (vslice m k2).
  Proof.
    apply map_eq. intros x.
    rewrite lookup_vslice /dual_lookup.
    destruct (decide (x = k1)) as [-> | Hne].
    - by rewrite 2!lookup_delete_eq.
    - do 2 (rewrite lookup_delete_ne; last done).
      by rewrite lookup_vslice /dual_lookup.
  Qed.

  Lemma vslice_delete_None (m : gmap K1 (gmap K2 V)) (im : gmap K2 V) k1 k2 :
    m !! k1 = Some im ->
    im !! k2 = None ->
    vslice (delete k1 m) k2 = vslice m k2.
  Proof.
    intros Hm Him.
    rewrite vslice_delete.
    apply delete_id.
    by rewrite lookup_vslice /dual_lookup Hm.
  Qed.

  Lemma dom_vslice_subseteq (m : gmap K1 (gmap K2 V)) k :
    dom (vslice m k) ⊆ dom m.
  Proof.
    apply (map_fold_weak_ind (λ r m, dom r ⊆ dom m)); first done.
    intros x m2 m' m1 Hnone IH.
    rewrite /vslice_step.
    destruct (m2 !! k) as [v |]; set_solver.
  Qed.

  Lemma elem_of_dom_vslice (m : gmap K1 (gmap K2 V)) k1 k2 :
    k1 ∈ dom (vslice m k2) ->
    ∃ im, m !! k1 = Some im ∧ k2 ∈ dom im.
  Proof.
    intros Hin.
    apply elem_of_dom in Hin as [v Hlookup].
    rewrite lookup_vslice /dual_lookup in Hlookup.
    destruct (m !! k1) as [im |]; last done.
    exists im.
    by split; last apply elem_of_dom.
  Qed.

  Lemma vslice_empty k :
    vslice (∅ : gmap K1 (gmap K2 V)) k = ∅.
  Proof. by rewrite /vslice map_fold_empty. Qed.

End lemma.
