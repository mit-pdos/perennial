From iris.algebra Require Import gmap lib.mnat_auth.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Import lib.own.
From iris.bi.lib Require Import fractional.
From Perennial.program_proof Require Import proof_prelude.

Class fmcounter_mapG Σ :=
   { fmcounter_map_inG :> inG Σ (gmapUR u64 mnat_authR) }.

(* TODO: move upstream *)
Section gmap.
Context `{Countable K} {A : cmraT}.
Implicit Types m : gmap K A.
Implicit Types i : K.
Implicit Types x y : A.

Lemma big_opM_singletons (m : gmap K A) :
  ([^op map] k ↦ x ∈ m, {[ k := x ]}) ≡ m.
Proof.
  induction m as [|k x m Hk IH] using map_ind.
  - rewrite big_opM_empty. done.
  - rewrite big_opM_insert // IH insert_singleton_op //.
Qed.
End gmap.

Definition fmcounter_map_own `{!fmcounter_mapG Σ} γ (k:u64) q n :=
  own γ {[ k := mnat_auth_auth q n]}.
Definition fmcounter_map_lb `{!fmcounter_mapG Σ} γ (k:u64) n :=
  own γ {[ k := mnat_auth_frag n]}.

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
    pose (m := gset_to_gmap (mnat_auth_auth 1 n) (fin_to_set u64)).
    iMod (own_alloc m) as (γ) "Hown".
    { intros k. rewrite lookup_gset_to_gmap option_guard_True; last by apply elem_of_fin_to_set.
      rewrite Some_valid. apply mnat_auth_auth_valid. }
    iExists γ.
    rewrite -(big_opM_singletons m).
    rewrite (big_opM_own_1 (H0:=mnat_auth_auth 1 0)).
    replace (fin_to_set u64) with (dom (gset _) m); last first.
    { rewrite dom_gset_to_gmap. done. }
    iApply big_sepM_dom.
    iApply (big_sepM_impl with "Hown").
    iIntros "!#" (k x [_ <-]%lookup_gset_to_gmap_Some).
    eauto.
  Qed.

  Lemma fmcounter_map_get_lb γ k q n :
    k fm[[γ]]↦{q} n -∗ k fm[[γ]]↦{q} n ∗ k fm[[γ]]≥ n.
  Proof.
    rewrite /fmcounter_map_own /fmcounter_map_lb.
    rewrite -own_op singleton_op.
    (* FIXME: needs Iris update *)
  Admitted.

  Lemma fmcounter_map_update (n' n:nat) γ k:
    (n ≤ n')%nat →
    k fm[[γ]]↦ n ==∗ k fm[[γ]]↦ n' ∗ k fm[[γ]]≥ n'.
  Proof.
    rewrite /fmcounter_map_own /fmcounter_map_lb=>Hn.
    rewrite -own_op singleton_op. iApply own_update. apply singleton_update.
    apply mnat_auth_update. done.
  Qed.

  Lemma fmcounter_map_agree_lb γ k q n1 n2 :
    k fm[[γ]]↦{q} n1 -∗ k fm[[γ]]≥ n2 -∗ ⌜n1 ≥ n2⌝%nat.
  Proof.
    rewrite /fmcounter_map_own /fmcounter_map_lb. iIntros "H1 H2".
    iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %[_ Hval]%singleton_valid%mnat_auth_both_frac_valid.
    eauto.
  Qed.

  Lemma fmcounter_map_agree_strict_lb γ k q n1 n2 :
    k fm[[γ]]↦{q} n1 -∗ k fm[[γ]]> n2 -∗ ⌜n1 > n2⌝%nat.
  Proof.
    rewrite /fmcounter_map_own /fmcounter_map_lb. iIntros "H1 H2".
    iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %[_ Hval]%singleton_valid%mnat_auth_both_frac_valid.
    eauto with lia.
  Qed.

  Lemma fmcounter_map_mono_lb (n1 n2:nat) γ k :
    n1 ≤ n2 ->
    k fm[[γ]]≥ n2 -∗ k fm[[γ]]≥ n1.
  Proof.
    rewrite /fmcounter_map_own /fmcounter_map_lb. iIntros (Hn).
    iApply own_mono. apply singleton_included. right.
    (* FIXME: needs Iris update to get [mnat_auth_frag_mono] *)
  Admitted.

End fmcounter_map_props.
