From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import iprop.
From Perennial.algebra Require Import blocks.

Theorem heap_array_to_list {Σ} {A} `{BlockAddr L} l0 (vs: list A) (P: L -> A -> iProp Σ) :
  ([∗ map] l↦v ∈ heap_array l0 vs, P l v) ⊣⊢
  ([∗ list] i↦v ∈ vs, P (addr_plus_off l0 i) v).
Proof.
  iInduction (vs) as [| v vs] "IH" forall (l0).
  - simpl.
    rewrite big_sepM_empty.
    auto.
  - simpl.
    rewrite addr_plus_off_0.
    rewrite big_sepM_union.
    { rewrite big_sepM_singleton.
      setoid_rewrite addr_plus_Sn.
      iSpecialize ("IH" $! (addr_plus_off l0 1)).
      iSplit.
      + iIntros "($&Hm)".
        iApply ("IH" with "Hm").
      + iIntros "($&Hl)".
        iApply ("IH" with "Hl").
    }
    symmetry.
    apply heap_array_map_disjoint; intros.
    apply (not_elem_of_dom (D := gset L)).
    rewrite dom_singleton elem_of_singleton addr_plus_plus.
    intros ?%addr_plus_ne; auto; lia.
Qed.
