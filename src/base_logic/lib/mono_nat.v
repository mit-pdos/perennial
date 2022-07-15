(* Just reexport Iris mdoule *)
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

(* TODO UPSTREAM https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/817 *)
Lemma mono_nat_lb_own_0 γ :
  ⊢ |==> mono_nat_lb_own γ 0.
Proof.
  rewrite mono_nat.mono_nat_lb_own_unseal /mono_nat.mono_nat_lb_own_def.
  iApply (own_unit mono_nat.mono_natUR).
Qed.

End iris.
