From iris.bi.lib Require Import fractional.
From iris.algebra Require Import gmap cmra dfrac_agree.
From iris.base_logic Require Import mono_nat.
From iris.proofmode Require Import proofmode.

Section definitions.
Class mapG Σ K V `{Countable K} :=
  { map_inG:> inG Σ (gmapR K (dfrac_agreeR (leibnizO V)))} .

Context `{mapG Σ K V}.

Definition ghost_map_points_to_def (γ : gname) (k : K) (dq : dfrac) (v : V) : iProp Σ :=
    own γ {[ k := (to_dfrac_agree dq (v : leibnizO V)) ]}.
Definition ghost_map_points_to_aux : seal (@ghost_map_points_to_def). Proof. by eexists. Qed.
Definition ghost_map_points_to := ghost_map_points_to_aux.(unseal).
Definition ghost_map_points_to_eq : @ghost_map_points_to = @ghost_map_points_to_def := ghost_map_points_to_aux.(seal_eq).

End definitions.

Notation "k ⤳[ γ ]{ dq } v" := (ghost_map_points_to γ k dq v)
  (at level 20, γ at level 50, dq at level 50, format "k ⤳[ γ ]{ dq }  v") : bi_scope.
Notation "k ⤳[ γ ]{# q } v" := (k ⤳[γ]{DfracOwn q} v)%I
  (at level 20, γ at level 50, q at level 50, format "k ⤳[ γ ]{# q }  v") : bi_scope.
Notation "k ⤳[ γ ] v" := (k ⤳[γ]{#1} v)%I
  (at level 20, γ at level 50, format "k  ⤳[ γ ]  v") : bi_scope.
Notation "k ⤳[ γ ]□ v" := (k ⤳[γ]{DfracDiscarded} v)%I
  (at level 20, γ at level 50) : bi_scope.

Local Ltac unseal := rewrite
  ?ghost_map_points_to_eq /ghost_map_points_to_def.

Section lemmas.
  Context `{mapG Σ K V}.
  Implicit Types (k : K) (v : V) (dq : dfrac) (q : Qp) (m : gmap K V).

  (** * Lemmas about the map points_toents *)
  Global Instance ghost_map_points_to_timeless k γ dq v : Timeless (k ⤳[γ]{dq} v).
  Proof. unseal. apply _. Qed.
  Global Instance ghost_map_points_to_persistent k γ v : Persistent (k ⤳[γ]□ v).
  Proof. unseal. apply _. Qed.
  Global Instance ghost_map_points_to_fractional k γ v : Fractional (λ q, k ⤳[γ]{#q} v)%I.
  Proof. unseal. intros p q. rewrite -own_op singleton_op -dfrac_agree_op. done. Qed.

  Global Instance ghost_map_points_to_as_fractional k γ q v :
    AsFractional (k ⤳[γ]{#q} v) (λ q, k ⤳[γ]{#q} v)%I q.
  Proof. split; first done. apply _. Qed.

  Lemma ghost_map_points_to_valid k γ dq v : k ⤳[γ]{dq} v -∗ ⌜✓ dq⌝.
  Proof.
    unseal. iIntros "Hpoints_to".
    iDestruct (own_valid with "Hpoints_to") as %Hvalid%singleton_valid.
    rewrite /to_dfrac_agree in Hvalid. by destruct Hvalid.
  Qed.
  Lemma ghost_map_points_to_valid_2 k γ dq1 dq2 v1 v2 :
    k ⤳[γ]{dq1} v1 -∗ k ⤳[γ]{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    rewrite singleton_op singleton_valid dfrac_agree_op_valid in Hvalid.
    done.
  Qed.
  Lemma ghost_map_points_to_agree k γ dq1 dq2 v1 v2 :
    k ⤳[γ]{dq1} v1 -∗ k ⤳[γ]{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hpoints_to1 Hpoints_to2".
    iDestruct (ghost_map_points_to_valid_2 with "Hpoints_to1 Hpoints_to2") as %[_ ?].
    done.
  Qed.

  Lemma ghost_map_points_to_combine k γ dq1 dq2 v1 v2 :
    k ⤳[γ]{dq1} v1 -∗ k ⤳[γ]{dq2} v2 -∗ k ⤳[γ]{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (ghost_map_points_to_agree with "Hl1 Hl2") as %->.
    unseal. iCombine "Hl1 Hl2" as "Hl".
    rewrite -dfrac_agree_op.
    iFrame.
    done.
  Qed.

  Lemma ghost_map_points_to_frac_ne γ k1 k2 dq1 dq2 v1 v2 :
    ¬ ✓ (dq1 ⋅ dq2) → k1 ⤳[γ]{dq1} v1 -∗ k2 ⤳[γ]{dq2} v2 -∗ ⌜k1 ≠ k2⌝.
  Proof.
    iIntros (?) "H1 H2"; iIntros (->).
    by iDestruct (ghost_map_points_to_valid_2 with "H1 H2") as %[??].
  Qed.
  Lemma ghost_map_points_to_ne γ k1 k2 dq2 v1 v2 :
    k1 ⤳[γ] v1 -∗ k2 ⤳[γ]{dq2} v2 -∗ ⌜k1 ≠ k2⌝.
  Proof. apply ghost_map_points_to_frac_ne. apply: exclusive_l. Qed.

  (** Make an points_toent read-only. *)
  Lemma ghost_map_points_to_persist k γ dq v :
    k ⤳[γ]{dq} v ==∗ k ⤳[γ]□ v.
  Proof. unseal. iApply own_update. apply singleton_update.
         apply dfrac_agree_persist. Qed.

  (** * Lemmas about [ghost_map_auth] *)
  Lemma ghost_map_alloc_strong P (m:gmap K V) :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ [∗ map] k ↦ v ∈ m, k ⤳[γ] v.
  Proof.
    unseal. intros.
    iMod (own_alloc_strong (A:= (gmapR K (dfrac_agreeR (leibnizO V))))
                              (fmap (λ v, to_dfrac_agree (DfracOwn 1) (v:leibnizO V)) m) P)
      as (γ) "Hauth".
    { done. }
    { intros k.
      rewrite lookup_fmap.
      by destruct (m !! k).
    }
    iExists γ.
    iDestruct "Hauth" as "[$ Hauth]".
    rewrite -(big_opM_singletons (_ <$> m)).
    rewrite big_opM_own_1.
    rewrite big_sepM_fmap.
    iApply (big_sepM_impl with "Hauth").
    do 2 iModIntro.
    iIntros.
    iFrame.
  Qed.

  Lemma ghost_map_alloc_fin (v:V) `{!finite.Finite K} :
    ⊢ |==> ∃ γ, [∗ set] k ∈ (fin_to_set K), k ⤳[γ] v.
  Proof.
    set (m:=gset_to_gmap (K:=K) (A:=V) v (fin_to_set K)).
    iStartProof.
    iMod (ghost_map_alloc_strong (λ _, True) m) as (?) "[_ H]".
    { apply pred_infinite_True. }
    iModIntro.
    iExists γ.
    replace (fin_to_set K) with (dom (gset K) m); last first.
    { apply dom_gset_to_gmap. }
    iDestruct (big_sepM_dom) as "Hm".
    iDestruct "Hm" as "[Hm1 _]".
    iApply ("Hm1" with "[H]").
    iApply (big_sepM_impl with "H").
    iModIntro.
    iIntros.
    apply lookup_gset_to_gmap_Some in H2.
    naive_solver.
  Qed.

  Lemma ghost_map_points_to_update {γ k v} w :
    k ⤳[γ] v ==∗ k ⤳[γ] w.
  Proof.
    unseal. apply own_update.
    apply singleton_update.
    apply cmra_update_exclusive.
    by constructor.
  Qed.

End lemmas.
