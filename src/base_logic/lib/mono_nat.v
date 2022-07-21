From iris.base_logic Require Export lib.mono_nat.

(* Add some Perennial-specific stuff *)
From iris.proofmode Require Import tactics.
From Perennial.algebra Require Import own_discrete atleast.

Section iris.
Context `{mono_natG Σ}.

Global Instance mono_nat_auth_own_discretizable (γ: gname) q n :
  Discretizable (mono_nat_auth_own γ q n).
Proof. rewrite mono_nat.mono_nat_auth_own_unseal. apply _. Qed.

Global Instance mono_nat_lb_own_discretizable (γ: gname) n :
  Discretizable (mono_nat_lb_own γ n).
Proof. rewrite mono_nat.mono_nat_lb_own_unseal. apply _. Qed.

End iris.
