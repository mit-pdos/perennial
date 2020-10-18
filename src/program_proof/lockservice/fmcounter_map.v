From iris.algebra Require Import auth numbers gmap.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Import lib.own.
From iris.bi.lib Require Import fractional.
From Perennial.algebra Require Import fmcounter.
From Perennial.goose_lang Require Import prelude.

Class fmcounter_mapG Σ :=
   { fmcounter_map_inG :> inG Σ (gmapUR u64 fmcounterUR) }.

Section fmcounter_map_props.
  Context `{!fmcounter_mapG Σ}.

Definition fmcounter_map_own γ (k:u64) q n := own γ {[ k := (●{q}MaxNat n)]}.
Definition fmcounter_map_lb γ (k:u64) n := own γ {[ k := (◯MaxNat n)]}.

Notation "k fm[[ γ ]]↦{ q } n " := (fmcounter_map_own γ k q%Qp n)
(at level 20, format "k fm[[ γ ]]↦{ q }  n") : bi_scope.
Notation "k fm[[ γ ]]↦ n " := (k fm[[ γ ]]↦{ 1 } n)%I
(at level 20, format "k fm[[ γ ]]↦ n") : bi_scope.
Notation "k fm[[ γ ]]≥ n " := (fmcounter_map_lb γ k n)
(at level 20, format "k fm[[ γ ]]≥ n") : bi_scope.
Notation "k fm[[ γ ]]> n " := (fmcounter_map_lb γ k (n + 1))
(at level 20, format "k fm[[ γ ]]> n") : bi_scope.

Lemma fmcounter_map_get_lb γ k q n :
      k fm[[γ]]↦{q} n ==∗ k fm[[γ]]↦{q} n ∗ k fm[[γ]]≥ n.
Admitted.

Lemma fmcounter_map_update γ k (n n':nat):
  n ≤ n' ->
      k fm[[γ]]↦ n ==∗ k fm[[γ]]↦ n'.
Admitted.

Lemma fmcounter_map_agree_lb γ k q n1 n2 :
  k fm[[γ]]↦{q} n1 -∗ k fm[[γ]]≥ n2 -∗ ⌜n1 ≥ n2⌝.
Admitted.

Lemma fmcounter_map_agree_strict_lb γ k q n1 n2 :
  k fm[[γ]]↦{q} n1 -∗ k fm[[γ]]> n2 -∗ ⌜n1 > n2⌝.
Admitted.

Lemma fmcounter_map_mono_lb (n1 n2:nat) γ k :
  n1 ≤ n2 ->
  k fm[[γ]]≥ n2 -∗ k fm[[γ]]≥ n1.
Admitted.

(* TODO: in the real fmcounter_map, this will need some preconditions *)
Lemma fmcounter_map_alloc n γ k :
  True
  ==∗ k fm[[γ]]↦ n.
Admitted.

End fmcounter_map_props.

Notation "k fm[[ γ ]]↦{ q } n " := (fmcounter_map_own γ k q%Qp n)
(at level 20, format "k fm[[ γ ]]↦{ q }  n") : bi_scope.
Notation "k fm[[ γ ]]↦ n " := (k fm[[ γ ]]↦{ 1 } n)%I
(at level 20, format "k fm[[ γ ]]↦ n") : bi_scope.
Notation "k fm[[ γ ]]≥ n " := (fmcounter_map_lb γ k n)
(at level 20, format "k fm[[ γ ]]≥ n") : bi_scope.
Notation "k fm[[ γ ]]> n " := (fmcounter_map_lb γ k (n + 1))
(at level 20, format "k fm[[ γ ]]> n") : bi_scope.
