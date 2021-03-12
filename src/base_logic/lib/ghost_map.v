(* Just reexport Iris mdoule *)
From iris.base_logic Require Export lib.ghost_map.

(* Add some Perennial-specific stuff *)
From Perennial.algebra Require Import own_discrete atleast.

Section lemmas.
  Context `{ghost_mapG Σ K V}.
  Implicit Types (k : K) (v : V) (dq : dfrac) (q : Qp) (m : gmap K V).

  Global Instance ghost_map_auth_discrete γ q m : Discretizable (ghost_map_auth γ q m).
  Proof. rewrite ghost_map_auth_eq. apply _. Qed.

  Global Instance ghost_map_auth_abs_timeless γ q m : AbsolutelyTimeless (ghost_map_auth γ q m).
  Proof. rewrite ghost_map_auth_eq. apply _. Qed.

  Global Instance ghost_map_elem_discrete γ dq k v : Discretizable (k ↪[γ]{dq} v).
  Proof. rewrite ghost_map_elem_eq. apply _. Qed.

  Global Instance ghost_map_elem_abs_timeless γ dq k v : AbsolutelyTimeless (k ↪[γ]{dq} v).
  Proof. rewrite ghost_map_elem_eq. apply _. Qed.

End lemmas.
