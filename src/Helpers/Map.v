From stdpp Require Import gmap.
From Coq Require Import ssreflect.

Section map.

  Context (K V:Type).
  Context `{Countable K}.
  Notation gmap := (gmap K V).
  Implicit Types (m:gmap).

  Theorem delete_insert_union m1 m2 k v :
    m1 !! k = Some v ->
    delete k m1 ∪ <[k := v]> m2 = m1 ∪ m2.
  Proof.
    intros.
    rewrite -insert_delete.
    rewrite -insert_union_r; first by apply lookup_delete.
    erewrite <- (insert_id (m1 ∪ m2)) by ( apply lookup_union_Some_l; eauto ).
    rewrite <- (insert_delete (m1 ∪ m2)).
    rewrite delete_union.
    eauto.
  Qed.

End map.
