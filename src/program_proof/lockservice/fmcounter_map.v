From iris.algebra Require Import gmap lib.mono_nat.
From iris.proofmode Require Import base tactics classes.
From Perennial.base_logic Require Import lib.own.
From iris.bi.lib Require Import fractional.
From Perennial.program_proof Require Import proof_prelude.

Class fmcounter_mapG Σ :=
   { fmcounter_map_inG :> inG Σ (gmapUR u64 mono_natR) }.

Definition fmcounter_map_own `{!fmcounter_mapG Σ} γ (k:u64) q n :=
  own γ {[ k := mono_nat_auth q n]}.
Definition fmcounter_map_lb `{!fmcounter_mapG Σ} γ (k:u64) n :=
  own γ {[ k := mono_nat_lb n]}.

Notation "k fm[[ γ ]]↦{ q } n " := (fmcounter_map_own γ k q%Qp n)
(at level 20, format "k  fm[[ γ ]]↦{ q }  n") : bi_scope.
Notation "k fm[[ γ ]]↦ n " := (k fm[[ γ ]]↦{ 1 } n)%I
(at level 20, format "k  fm[[ γ ]]↦  n") : bi_scope.
Notation "k fm[[ γ ]]≥ n " := (fmcounter_map_lb γ k n)
(at level 20, format "k  fm[[ γ ]]≥  n") : bi_scope.
Notation "k fm[[ γ ]]> n " := (fmcounter_map_lb γ k (n + 1))
(at level 20, format "k  fm[[ γ ]]>  n") : bi_scope.

Section fmcounter_map_props.
  Context `{!fmcounter_mapG Σ}.

  Lemma fmcounter_map_alloc (n : nat) :
    ⊢ |==> ∃ γ, [∗ set] k ∈ (fin_to_set u64), k fm[[γ]]↦ n.
  Proof.
    pose (m := gset_to_gmap (mono_nat_auth 1 n) (fin_to_set u64)).
    iMod (own_alloc m) as (γ) "Hown".
    { intros k. rewrite lookup_gset_to_gmap option_guard_True; last by apply elem_of_fin_to_set.
      rewrite Some_valid. apply mono_nat_auth_valid. }
    iExists γ.
    rewrite -(big_opM_singletons m).
    rewrite big_opM_own_1.
    replace (fin_to_set u64) with (dom (gset _) m); last first.
    { rewrite dom_gset_to_gmap. done. }
    iApply big_sepM_dom.
    iApply (big_sepM_impl with "Hown").
    iIntros "!#" (k x [_ <-]%lookup_gset_to_gmap_Some).
    eauto.
  Qed.

  Lemma fmcounter_map_get_lb γ k q n :
    k fm[[γ]]↦{q} n -∗ k fm[[γ]]≥ n.
  Proof.
    rewrite /fmcounter_map_own /fmcounter_map_lb.
    apply own_mono. apply singleton_included. right.
    apply mono_nat_included.
  Qed.

  Lemma fmcounter_map_update (n' n:nat) γ k:
    (n ≤ n')%nat →
    k fm[[γ]]↦ n ==∗ k fm[[γ]]↦ n' ∗ k fm[[γ]]≥ n'.
  Proof.
    iIntros (Hn) "Hauth". iAssert (|==> k fm[[γ]]↦ n')%I with "[Hauth]" as ">Hauth".
    { rewrite /fmcounter_map_own. iApply (own_update with "Hauth").
      apply singleton_update. apply mono_nat_update. done. }
    iDestruct (fmcounter_map_get_lb with "Hauth") as "#$". done.
  Qed.

  Lemma fmcounter_map_agree_lb γ k q n1 n2 :
    k fm[[γ]]↦{q} n1 -∗ k fm[[γ]]≥ n2 -∗ ⌜n1 ≥ n2⌝%nat.
  Proof.
    rewrite /fmcounter_map_own /fmcounter_map_lb. iIntros "H1 H2".
    iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %[_ Hval]%singleton_valid%mono_nat_both_frac_valid.
    eauto.
  Qed.

  Lemma fmcounter_map_agree_strict_lb γ k q n1 n2 :
    k fm[[γ]]↦{q} n1 -∗ k fm[[γ]]> n2 -∗ ⌜n1 > n2⌝%nat.
  Proof.
    rewrite /fmcounter_map_own /fmcounter_map_lb. iIntros "H1 H2".
    iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %[_ Hval]%singleton_valid%mono_nat_both_frac_valid.
    eauto with lia.
  Qed.

  Lemma fmcounter_map_mono_lb (n1 n2:nat) γ k :
    n1 ≤ n2 ->
    k fm[[γ]]≥ n2 -∗ k fm[[γ]]≥ n1.
  Proof.
    rewrite /fmcounter_map_own /fmcounter_map_lb. iIntros (Hn).
    iApply own_mono. apply singleton_included. right.
    apply mono_nat_lb_mono; auto with lia.
  Qed.

  Lemma fmcounter_map_sep γ q1 q2 k n:
    k fm[[γ]]↦{q1 + q2} n ⊣⊢ k fm[[γ]]↦{q1} n ∗ k fm[[γ]]↦{q2} n.
  Proof.
  iSplit.
  - iIntros "H".
    rewrite -own_op.
    rewrite singleton_op.
    by rewrite mono_nat_auth_frac_op.
  - iIntros "(Hm1&Hm2)". iCombine "Hm1 Hm2" as "Hm".
    by rewrite mono_nat_auth_frac_op.
  Qed.

  Global Instance fmcounter_map_fractional γ k n :
    Fractional (λ q, fmcounter_map_own γ k q n).
  Proof. intros p q. by apply fmcounter_map_sep. Qed.

  Global Instance fmcounter_map_as_fractional γ k q n :
    AsFractional (k fm[[γ]]↦{q} n) (λ q, fmcounter_map_own γ k q n) q.
  Proof. split; first by done. apply _. Qed.

  Global Instance fmcounter_map_into_sep γ k n :
    IntoSep (k fm[[γ]]↦{1} n) (k fm[[γ]]↦{1/2} n) (k fm[[γ]]↦{1/2} n).
  Proof. apply _. Qed.

End fmcounter_map_props.
