(* Just reexport Iris mdoule *)
From iris.base_logic Require Export lib.ghost_map.

(* Add some Perennial-specific stuff *)
From iris.proofmode Require Import tactics.
From Perennial.algebra Require Import own_discrete atleast.
From Perennial.Helpers Require Import Map.

Set Default Proof Using "Type".

Section lemmas.
  Context `{ghost_mapG Σ K V}.
  Implicit Types (k : K) (v : V) (dq : dfrac) (q : Qp) (m : gmap K V).

  Lemma ghost_map_elem_big_exist γ m :
    ([∗ map] l↦_ ∈ m, ∃ v', l ↪[γ] v') -∗
    ∃ m', ⌜dom (gset _) m' = dom (gset _) m⌝ ∗
          [∗ map] l↦v ∈ m', l ↪[γ] v.
  Proof.
    induction m as [|l v m] using map_ind.
    - rewrite big_sepM_empty.
      iIntros "_". iExists ∅.
      iSplit; first done.
      rewrite big_sepM_empty; done.
    - rewrite big_sepM_insert //.
      iIntros "[Hl Hm]".
      iDestruct "Hl" as (v') "Hl".
      iDestruct (IHm with "Hm") as (m0 Hdom) "Hm".
      iExists (<[l:=v']> m0).
      iSplit.
      + iPureIntro.
        rewrite !dom_insert_L. congruence.
      + rewrite big_sepM_insert; [ by iFrame | ].
        apply not_elem_of_dom.
        apply not_elem_of_dom in H1.
        congruence.
  Qed.

  Lemma ghost_map_update_big_exist {γ m} m1 :
    ghost_map_auth γ 1 m -∗
    ( [∗ map] l↦v ∈ m1, ∃ v', l ↪[γ] v' ) ==∗
      ghost_map_auth γ 1 (m1 ∪ m) ∗
      ( [∗ map] l↦v ∈ m1, l ↪[γ] v ).
  Proof.
    iIntros "Hauth Hm0".
    iDestruct (ghost_map_elem_big_exist with "Hm0") as (m0 Hdom) "Hm0".
    iMod (ghost_map_update_big with "Hauth Hm0") as "[$ Hm]"; auto.
  Qed.


  Global Instance ghost_map_auth_discrete γ q m : Discretizable (ghost_map_auth γ q m).
  Proof. rewrite ghost_map_auth_eq. apply _. Qed.

  Global Instance ghost_map_auth_abs_timeless γ q m : AbsolutelyTimeless (ghost_map_auth γ q m).
  Proof. rewrite ghost_map_auth_eq. apply _. Qed.

  Global Instance ghost_map_elem_discrete γ dq k v : Discretizable (k ↪[γ]{dq} v).
  Proof. rewrite ghost_map_elem_eq. apply _. Qed.

  Global Instance ghost_map_elem_abs_timeless γ dq k v : AbsolutelyTimeless (k ↪[γ]{dq} v).
  Proof. rewrite ghost_map_elem_eq. apply _. Qed.

End lemmas.
