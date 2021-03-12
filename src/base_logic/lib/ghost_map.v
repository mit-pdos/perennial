(* Just reexport Iris mdoule *)
From iris.base_logic Require Export lib.ghost_map.

(* Add some Perennial-specific stuff *)
From iris.proofmode Require Import tactics.
From Perennial.algebra Require Import own_discrete atleast.

Section lemmas.
  Context `{ghost_mapG Σ K V}.
  Implicit Types (k : K) (v : V) (dq : dfrac) (q : Qp) (m : gmap K V).

  (* FIXME upstream *)
  Lemma ghost_map_insert_big {γ σ} σ' :
    σ' ##ₘ σ →
    ghost_map_auth γ 1 σ ==∗
    ghost_map_auth γ 1 (σ' ∪ σ) ∗ ([∗ map] l ↦ v ∈ σ', l ↪[γ] v).
  Proof using Type.
    revert σ; induction σ' as [| l v σ' Hl IH] using map_ind; iIntros (σ Hdisj) "Hσ".
    { rewrite left_id_L. auto. }
    iMod (IH with "Hσ") as "[Hσ'σ Hσ']"; first by eapply map_disjoint_insert_l.
    decompose_map_disjoint.
    rewrite !big_opM_insert // -insert_union_l //.
    by iMod (ghost_map_insert with "Hσ'σ") as "($ & $)";
      first by apply lookup_union_None.
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
