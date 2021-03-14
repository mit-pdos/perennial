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

  (* TODO upstream, see Iris MR 649 *)
  Lemma ghost_map_insert_big {γ σ} σ' :
    σ' ##ₘ σ →
    ghost_map_auth γ 1 σ ==∗
    ghost_map_auth γ 1 (σ' ∪ σ) ∗ ([∗ map] l ↦ v ∈ σ', l ↪[γ] v).
  Proof.
    revert σ; induction σ' as [| l v σ' Hl IH] using map_ind; iIntros (σ Hdisj) "Hσ".
    { rewrite left_id_L. auto. }
    iMod (IH with "Hσ") as "[Hσ'σ Hσ']"; first by eapply map_disjoint_insert_l.
    decompose_map_disjoint.
    rewrite !big_opM_insert // -insert_union_l //.
    by iMod (ghost_map_insert with "Hσ'σ") as "($ & $)";
      first by apply lookup_union_None.
  Qed.

  (* TODO upstream, see Iris MR 649 *)
  Theorem ghost_map_update_big {γ m m0} m1 :
    dom (gset _) m0 = dom _ m1 →
    ghost_map_auth γ 1 m -∗
    ([∗ map] a↦v ∈ m0, a ↪[γ] v) -∗
    |==> ghost_map_auth γ 1 (m1 ∪ m) ∗
        [∗ map] a↦v ∈ m1, a ↪[γ] v.
  Proof.
    iIntros (Hdom) "Hauth Hm0". apply (comm (R:=(↔)) (=)) in Hdom.
    iInduction m0 as [|l v m0] "IH" using map_ind forall (m m1 Hdom).
    - rewrite dom_empty_L in Hdom.
      apply dom_empty_inv_L in Hdom as ->.
      rewrite left_id_L big_sepM_empty.
      by iFrame.
    - rewrite big_sepM_insert //.
      iDestruct "Hm0" as "[Hl Hm0]".
      rewrite dom_insert_L in Hdom.
      assert (l ∈ dom (gset K) m1) as Hindom by set_solver.
      apply elem_of_dom in Hindom as [v' Hlookup].
      iMod (ghost_map_update v' with "Hauth Hl") as "[Hauth Hl]".
      iSpecialize ("IH" $! (<[l:=v']> m)).
      apply dom_union_inv in Hdom as (m1l&m1' & ? & -> & Hm1ldom & ?); last first.
      { apply disjoint_singleton_l, not_elem_of_dom; auto. }
      iMod ("IH" $! m1' with "[%] Hauth Hm0") as "[Hauth Hm0]"; auto.
      iModIntro.
      assert (m1l = {[l := v']}).
      { apply dom_singleton_inv in Hm1ldom as [v'' ->].
        f_equal.
        erewrite lookup_union_Some_l in Hlookup; last first.
        { rewrite lookup_singleton_Some //. }
        congruence. }
      subst.
      rewrite big_sepM_union // big_sepM_singleton.
      iFrame. iClear "#".
      rewrite insert_union_singleton_l.
      rewrite !assoc [m1' ∪ _]map_union_comm //.
  Qed.

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
