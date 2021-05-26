(** A lot like [ghost_map] but without the [auth]. *)
From stdpp Require Import finite.
From iris.algebra Require Import gmap agree dfrac.
From iris.proofmode Require Import base tactics classes.
From Perennial.base_logic Require Import lib.own.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "Type".

Local Definition gmapR (K V : Type) `{Countable K} :=
  gmapUR K (prodR dfracR (agreeR (leibnizO V))).
Class gmapG Σ (K V : Type) `{Countable K} :=
   { gmap_inG :> inG Σ (gmapR K V) }.
Definition gmapΣ (K V : Type) `{Countable K} := #[GFunctor (gmapR K V)].

Global Instance subG_gmapΣ {Σ} (K V : Type) `{Countable K} :
  subG (gmapΣ K V) Σ → gmapG Σ K V.
Proof. solve_inG. Qed.

Definition gmap_own {K V : Type} `{Countable K, !gmapG Σ K V}
    γ (k:K) (dq:dfrac) (v:V) :=
  own (A:=gmapR K V) γ {[ k := (dq, to_agree v) ]}.

Notation "k gm[[ γ ]]↦{ dq } v " := (gmap_own γ k dq v)
  (at level 20, format "k  gm[[ γ ]]↦{ dq }  v") : bi_scope.
Notation "k gm[[ γ ]]↦{# q } v " := (k gm[[γ]]↦{DfracOwn q} v)%I
  (at level 20, format "k  gm[[ γ ]]↦{# q }  v") : bi_scope.
Notation "k gm[[ γ ]]↦ v " := (k gm[[γ]]↦{#1} v)%I
  (at level 20, format "k  gm[[ γ ]]↦  v") : bi_scope.
Notation "k gm[[ γ ]]↦□ v " := (gmap_own γ k DfracDiscarded v)
  (at level 20, format "k  gm[[ γ ]]↦□  v") : bi_scope.

Section gmap_own_props.
  Context {K V : Type} `{Countable K, !gmapG Σ K V}.
  Implicit Types (k : K) (v : V).

  Lemma gmap_own_alloc_all `{!Finite K} (v : V) :
    ⊢ |==> ∃ γ, [∗ set] k ∈ (fin_to_set K), k gm[[γ]]↦ v.
  Proof.
    pose (m := gset_to_gmap (DfracOwn 1, to_agree v) (fin_to_set K) : gmapR K V).
    iMod (own_alloc m) as (γ) "Hown".
    { intros k. rewrite lookup_gset_to_gmap option_guard_True; last by apply elem_of_fin_to_set.
      done. }
    iExists γ.
    rewrite -(big_opM_singletons m).
    rewrite big_opM_own_1.
    replace (fin_to_set K) with (dom (gset _) m); last first.
    { rewrite dom_gset_to_gmap. done. }
    iApply big_sepM_dom.
    iApply (big_sepM_impl with "Hown").
    iIntros "!#" (k x [_ <-]%lookup_gset_to_gmap_Some).
    eauto.
  Qed.

  Lemma gmap_own_valid v γ dq k :
    k gm[[γ]]↦{dq} v -∗ ⌜✓ dq⌝.
  Proof.
    iIntros "Helem".
    iDestruct (own_valid with "Helem") as %[??]%singleton_valid.
    eauto.
  Qed.
  Lemma gmap_own_valid_2 v1 v2 γ dq1 dq2 k :
    k gm[[γ]]↦{dq1} v1 -∗ k gm[[γ]]↦{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    iIntros "Helem1 Helem2".
    iDestruct (own_valid_2 with "Helem1 Helem2") as %Hval.
    iPureIntro. move: Hval.
    rewrite singleton_op singleton_valid -pair_op=>-[/= ? /to_agree_op_valid_L ?].
    eauto.
  Qed.
  Lemma gmap_own_agree v1 v2 γ dq1 dq2 k :
    k gm[[γ]]↦{dq1} v1 -∗ k gm[[γ]]↦{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Helem1 Helem2".
    iDestruct (gmap_own_valid_2 with "Helem1 Helem2") as %[??].
    eauto.
  Qed.

  Lemma gmap_own_update v' v γ k :
    k gm[[γ]]↦ v ==∗ k gm[[γ]]↦ v'.
  Proof.
    iApply own_update.
    apply: singleton_update.
    apply: cmra_update_exclusive.
    done.
  Qed.

  Lemma gmap_own_persist v γ dq k :
    k gm[[γ]]↦{dq} v ==∗ k gm[[γ]]↦□ v.
  Proof.
    iApply own_update.
    apply: singleton_update.
    apply: prod_update; last reflexivity. simpl.
    apply: dfrac_discard_update.
  Qed.

  (* TODO: Add more lemmas from [ghost_map]. *)

End gmap_own_props.
