(* Slightly modified version of https://gitlab.mpi-sws.org/iris/iris/-/blob/849f50f421114ad1b8caf0cd1b66aff338e4abfa/iris/base_logic/lib/ghost_map.v *)

From New.experiments Require Export own.

(** A "ghost map" (or "ghost heap") with a proposition controlling authoritative
ownership of the entire heap, and a "points-to-like" proposition for (mutable,
fractional, or persistent read-only) ownership of individual elements. *)
From iris.bi.lib Require Import fractional.
(* From iris.proofmode Require Import proofmode. *)
(* From iris.algebra Require Import gmap_view. *)
(* From iris.algebra Require Export dfrac. *)
(* From iris.base_logic.lib Require Export own. *)
(* From iris.prelude Require Import options. *)

(** The CMRA we need.
FIXME: This is intentionally discrete-only, but
should we support setoids via [Equiv]? *)
Class ghost_mapG (Σ : gFunctors) `{!allG Σ} (K V : Type) `{Countable K}.

Section definitions.
  Context `{ghost_mapG Σ K V}.

  Local Definition ghost_map_auth_def
      (γ : gname) (q : Qp) (m : gmap K V) : iProp Σ :=
    own γ (gmap_view_auth (V:=agreeR $ leibnizO V) (DfracOwn q) (to_agree <$> m)).
  Local Definition ghost_map_auth_aux : seal (@ghost_map_auth_def).
  Proof. by eexists. Qed.
  Definition ghost_map_auth := ghost_map_auth_aux.(unseal).
  Local Definition ghost_map_auth_unseal :
    @ghost_map_auth = @ghost_map_auth_def := ghost_map_auth_aux.(seal_eq).

  Local Definition ghost_map_elem_def
      (γ : gname) (k : K) (dq : dfrac) (v : V) : iProp Σ :=
    own γ (gmap_view_frag (V:=agreeR $ leibnizO V) k dq (to_agree v)).
  Local Definition ghost_map_elem_aux : seal (@ghost_map_elem_def).
  Proof. by eexists. Qed.
  Definition ghost_map_elem := ghost_map_elem_aux.(unseal).
  Local Definition ghost_map_elem_unseal :
    @ghost_map_elem = @ghost_map_elem_def := ghost_map_elem_aux.(seal_eq).
End definitions.

Notation "k ↪[ γ ] dq v" := (ghost_map_elem γ k dq v)
  (at level 20, γ at level 50, dq custom dfrac at level 1,
   format "k  ↪[ γ ] dq  v") : bi_scope.

Local Ltac unseal := rewrite
  ?ghost_map_auth_unseal /ghost_map_auth_def
  ?ghost_map_elem_unseal /ghost_map_elem_def.

Section lemmas.
  Context `{ghost_mapG Σ K V}.
  Implicit Types (k : K) (v : V) (dq : dfrac) (q : Qp) (m : gmap K V).

  (** * Lemmas about the map elements *)
  Global Instance ghost_map_elem_timeless k γ dq v : Timeless (k ↪[γ]{dq} v).
  Proof. unseal. apply _. Qed.
  Global Instance ghost_map_elem_persistent k γ v : Persistent (k ↪[γ]□ v).
  Proof. unseal. apply _. Qed.
  Global Instance ghost_map_elem_fractional k γ v :
    Fractional (λ q, k ↪[γ]{#q} v)%I.
  Proof. unseal=> p q. rewrite -own_op -gmap_view_frag_add agree_idemp //. Qed.
  Global Instance ghost_map_elem_as_fractional k γ q v :
    AsFractional (k ↪[γ]{#q} v) (λ q, k ↪[γ]{#q} v)%I q.
  Proof. split; first done. apply _. Qed.

  Local Lemma ghost_map_elems_unseal γ m dq :
    ([∗ map] k ↦ v ∈ m, k ↪[γ]{dq} v) ==∗
    own γ ([^op map] k↦v ∈ m,
      gmap_view_frag (V:=agreeR (leibnizO V)) k dq (to_agree v)).
  Proof.
    unseal. destruct (decide (m = ∅)) as [->|Hne].
    - rewrite !big_opM_empty. iIntros "_". iApply own_unit.
    - rewrite big_opM_own //. iIntros "?". done.
  Qed.

  Lemma ghost_map_elem_valid k γ dq v : k ↪[γ]{dq} v -∗ ⌜✓ dq⌝.
  Proof.
    unseal. iIntros "Helem".
    iDestruct (own_valid with "Helem") as %?%gmap_view_frag_valid.
    naive_solver.
  Qed.
  Lemma ghost_map_elem_valid_2 k γ dq1 dq2 v1 v2 :
    k ↪[γ]{dq1} v1 -∗ k ↪[γ]{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iCombine "H1 H2" gives %[? Hag]%gmap_view_frag_op_valid.
    rewrite to_agree_op_valid_L in Hag. done.
  Qed.
  Lemma ghost_map_elem_agree k γ dq1 dq2 v1 v2 :
    k ↪[γ]{dq1} v1 -∗ k ↪[γ]{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Helem1 Helem2".
    iDestruct (ghost_map_elem_valid_2 with "Helem1 Helem2") as %[_ ?].
    done.
  Qed.

  Global Instance ghost_map_elem_combine_gives γ k v1 dq1 v2 dq2 :
    CombineSepGives (k ↪[γ]{dq1} v1) (k ↪[γ]{dq2} v2) ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[H1 H2].
    eauto.
  Qed.

  Lemma ghost_map_elem_combine k γ dq1 dq2 v1 v2 :
    k ↪[γ]{dq1} v1 -∗ k ↪[γ]{dq2} v2 -∗ k ↪[γ]{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (ghost_map_elem_agree with "Hl1 Hl2") as %->.
    unseal. iCombine "Hl1 Hl2" as "Hl". rewrite agree_idemp. eauto with iFrame.
  Qed.

  Global Instance ghost_map_elem_combine_as k γ dq1 dq2 v1 v2 :
    CombineSepAs (k ↪[γ]{dq1} v1) (k ↪[γ]{dq2} v2) (k ↪[γ]{dq1 ⋅ dq2} v1) | 60.
    (* higher cost than the Fractional instance [combine_sep_fractional_bwd],
       which kicks in for #qs *)
  Proof.
    rewrite /CombineSepAs. iIntros "[H1 H2]".
    iDestruct (ghost_map_elem_combine with "H1 H2") as "[$ _]".
  Qed.

  Lemma ghost_map_elem_frac_ne γ k1 k2 dq1 dq2 v1 v2 :
    ¬ ✓ (dq1 ⋅ dq2) → k1 ↪[γ]{dq1} v1 -∗ k2 ↪[γ]{dq2} v2 -∗ ⌜k1 ≠ k2⌝.
  Proof.
    iIntros (?) "H1 H2"; iIntros (->).
    by iCombine "H1 H2" gives %[??].
  Qed.
  Lemma ghost_map_elem_ne γ k1 k2 dq2 v1 v2 :
    k1 ↪[γ] v1 -∗ k2 ↪[γ]{dq2} v2 -∗ ⌜k1 ≠ k2⌝.
  Proof. apply ghost_map_elem_frac_ne. apply: exclusive_l. Qed.

  (** Make an element read-only. *)
  Lemma ghost_map_elem_persist k γ dq v :
    k ↪[γ]{dq} v ==∗ k ↪[γ]□ v.
  Proof. unseal. iApply own_update. apply gmap_view_frag_persist. Qed.

  (** Recover fractional ownership for read-only element. *)
  Lemma ghost_map_elem_unpersist k γ v :
    k ↪[γ]□ v ==∗ ∃ q, k ↪[γ]{# q} v.
  Proof.
    unseal. iIntros "H".
    iMod (own_updateP with "H") as "H";
      first by apply gmap_view_frag_unpersist.
    iDestruct "H" as (? (q&->)) "H".
    iIntros "!>". iExists q. done.
  Qed.

  (** * Lemmas about [ghost_map_auth] *)
  Lemma ghost_map_alloc_strong P m :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ ghost_map_auth γ 1 m ∗ [∗ map] k ↦ v ∈ m, k ↪[γ] v.
  Proof.
    unseal. intros.
    iMod (own_alloc_strong
      (gmap_view_auth (K:=K) (V:=agreeR (leibnizO V)) (DfracOwn 1) ∅) P)
      as (γ) "[% Hauth]"; first done.
    { apply gmap_view_auth_valid. }
    iExists γ. iSplitR; first done.
    rewrite -big_opM_own_1 -own_op. iApply (own_update with "Hauth").
    etrans; first apply (gmap_view_alloc_big _ (to_agree <$> m) (DfracOwn 1)).
    - apply map_disjoint_empty_r.
    - done.
    - by apply map_Forall_fmap.
    - rewrite right_id big_opM_fmap. done.
  Qed.
  Lemma ghost_map_alloc_strong_empty P :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ ghost_map_auth γ 1 (∅ : gmap K V).
  Proof.
    intros. iMod (ghost_map_alloc_strong P ∅) as (γ) "(% & Hauth & _)"; eauto.
  Qed.
  Lemma ghost_map_alloc m :
    ⊢ |==> ∃ γ, ghost_map_auth γ 1 m ∗ [∗ map] k ↦ v ∈ m, k ↪[γ] v.
  Proof.
    iMod (ghost_map_alloc_strong (λ _, True) m) as (γ) "[_ Hmap]".
    - by apply pred_infinite_True.
    - eauto.
  Qed.
  Lemma ghost_map_alloc_empty :
    ⊢ |==> ∃ γ, ghost_map_auth γ 1 (∅ : gmap K V).
  Proof.
    intros. iMod (ghost_map_alloc ∅) as (γ) "(Hauth & _)"; eauto.
  Qed.

  Global Instance ghost_map_auth_timeless γ q m : Timeless (ghost_map_auth γ q m).
  Proof. unseal. apply _. Qed.
  Global Instance ghost_map_auth_fractional γ m : Fractional (λ q, ghost_map_auth γ q m)%I.
  Proof. intros p q. unseal. rewrite -own_op -gmap_view_auth_dfrac_op //. Qed.
  Global Instance ghost_map_auth_as_fractional γ q m :
    AsFractional (ghost_map_auth γ q m) (λ q, ghost_map_auth γ q m)%I q.
  Proof. split; first done. apply _. Qed.

  Lemma ghost_map_auth_valid γ q m : ghost_map_auth γ q m -∗ ⌜q ≤ 1⌝%Qp.
  Proof.
    unseal. iIntros "Hauth".
    iDestruct (own_valid with "Hauth") as %?%gmap_view_auth_dfrac_valid.
    done.
  Qed.
  Lemma ghost_map_auth_valid_2 γ q1 q2 m1 m2 :
    ghost_map_auth γ q1 m1 -∗ ghost_map_auth γ q2 m2 -∗ ⌜(q1 + q2 ≤ 1)%Qp ∧ m1 = m2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    (* We need to explicitly specify the Inj instances instead of
    using inj _ since we need to specify [leibnizO] for [to_agree_inj]. *)
    iCombine "H1 H2" gives %[? ?%(map_fmap_equiv_inj _
      (to_agree_inj (A:=(leibnizO _))))]%gmap_view_auth_dfrac_op_valid.
    iPureIntro. split; first done. by fold_leibniz.
  Qed.
  Lemma ghost_map_auth_agree γ q1 q2 m1 m2 :
    ghost_map_auth γ q1 m1 -∗ ghost_map_auth γ q2 m2 -∗ ⌜m1 = m2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_map_auth_valid_2 with "H1 H2") as %[_ ?].
    done.
  Qed.

  (** * Lemmas about the interaction of [ghost_map_auth] with the elements *)
  Lemma ghost_map_lookup {γ q m k dq v} :
    ghost_map_auth γ q m -∗ k ↪[γ]{dq} v -∗ ⌜m !! k = Some v⌝.
  Proof.
    unseal. iIntros "Hauth Hel".
    iCombine "Hauth Hel" gives
      %(av' & _ & _ & Hav' & _ & Hincl)%gmap_view_both_dfrac_valid_discrete_total.
    iPureIntro.
    apply lookup_fmap_Some in Hav' as [v' [<- Hv']].
    (* FIXME: Why do we need [(SI:=natSI) (A:=leibnizO V)]
    https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/555 seems to resolve
    the problem? *)
    apply (to_agree_included_L (SI:=natSI) (A:=leibnizO V)) in Hincl.
    by rewrite Hincl.
  Qed.

  Global Instance ghost_map_lookup_combine_gives_1 {γ q m k dq v} :
    CombineSepGives (ghost_map_auth γ q m) (k ↪[γ]{dq} v) ⌜m !! k = Some v⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]".
    iDestruct (ghost_map_lookup with "H1 H2") as %->. eauto.
  Qed.

  Global Instance ghost_map_lookup_combine_gives_2 {γ q m k dq v} :
    CombineSepGives (k ↪[γ]{dq} v) (ghost_map_auth γ q m) ⌜m !! k = Some v⌝.
  Proof.
    rewrite /CombineSepGives comm. apply ghost_map_lookup_combine_gives_1.
  Qed.

  Lemma ghost_map_insert {γ m} k v :
    m !! k = None →
    ghost_map_auth γ 1 m ==∗ ghost_map_auth γ 1 (<[k := v]> m) ∗ k ↪[γ] v.
  Proof.
    unseal. intros Hm. rewrite -own_op.
    iApply own_update. rewrite fmap_insert. apply: gmap_view_alloc; [|done..].
    rewrite lookup_fmap Hm //.
  Qed.
  Lemma ghost_map_insert_persist {γ m} k v :
    m !! k = None →
    ghost_map_auth γ 1 m ==∗ ghost_map_auth γ 1 (<[k := v]> m) ∗ k ↪[γ]□ v.
  Proof.
    iIntros (?) "Hauth".
    iMod (ghost_map_insert k with "Hauth") as "[$ Helem]"; first done.
    iApply ghost_map_elem_persist. done.
  Qed.

  Lemma ghost_map_delete {γ m k v} :
    ghost_map_auth γ 1 m -∗ k ↪[γ] v ==∗ ghost_map_auth γ 1 (delete k m).
  Proof.
    unseal. iApply bi.wand_intro_r. rewrite -own_op.
    iApply own_update. rewrite fmap_delete. apply: gmap_view_delete.
  Qed.

  Lemma ghost_map_update {γ m k v} w :
    ghost_map_auth γ 1 m -∗ k ↪[γ] v ==∗ ghost_map_auth γ 1 (<[k := w]> m) ∗ k ↪[γ] w.
  Proof.
    unseal. iApply bi.wand_intro_r. rewrite -!own_op.
    iApply own_update. rewrite fmap_insert. apply: gmap_view_replace; done.
  Qed.

  (** Big-op versions of above lemmas *)
  Lemma ghost_map_lookup_big {γ q m dq} m0 :
    ghost_map_auth γ q m -∗
    ([∗ map] k↦v ∈ m0, k ↪[γ]{dq} v) -∗
    ⌜m0 ⊆ m⌝.
  Proof.
    iIntros "Hauth Hfrag". rewrite map_subseteq_spec. iIntros (k v Hm0).
    iDestruct (ghost_map_lookup with "Hauth [Hfrag]") as %->.
    { rewrite big_sepM_lookup; done. }
    done.
  Qed.

  Lemma ghost_map_insert_big {γ m} m' :
    m' ##ₘ m →
    ghost_map_auth γ 1 m ==∗
    ghost_map_auth γ 1 (m' ∪ m) ∗ ([∗ map] k ↦ v ∈ m', k ↪[γ] v).
  Proof.
    unseal. intros ?. rewrite -big_opM_own_1 -own_op. iApply own_update.
    etrans; first apply: (gmap_view_alloc_big _ (to_agree <$> m') (DfracOwn 1)).
    - apply map_disjoint_fmap. done.
    - done.
    - by apply map_Forall_fmap.
    - rewrite map_fmap_union big_opM_fmap. done.
  Qed.
  Lemma ghost_map_insert_persist_big {γ m} m' :
    m' ##ₘ m →
    ghost_map_auth γ 1 m ==∗
    ghost_map_auth γ 1 (m' ∪ m) ∗ ([∗ map] k ↦ v ∈ m', k ↪[γ]□ v).
  Proof.
    iIntros (Hdisj) "Hauth".
    iMod (ghost_map_insert_big m' with "Hauth") as "[$ Helem]"; first done.
    iApply big_sepM_bupd. iApply (big_sepM_impl with "Helem").
    iIntros "!#" (k v) "_". iApply ghost_map_elem_persist.
  Qed.

  Lemma ghost_map_delete_big {γ m} m0 :
    ghost_map_auth γ 1 m -∗
    ([∗ map] k↦v ∈ m0, k ↪[γ] v) ==∗
    ghost_map_auth γ 1 (m ∖ m0).
  Proof.
    iIntros "Hauth Hfrag". iMod (ghost_map_elems_unseal with "Hfrag") as "Hfrag".
    unseal. iApply (own_update_2 with "Hauth Hfrag").
    rewrite map_fmap_difference.
    etrans; last apply: gmap_view_delete_big.
    rewrite big_opM_fmap. done.
  Qed.

  Theorem ghost_map_update_big {γ m} m0 m1 :
    dom m0 = dom m1 →
    ghost_map_auth γ 1 m -∗
    ([∗ map] k↦v ∈ m0, k ↪[γ] v) ==∗
    ghost_map_auth γ 1 (m1 ∪ m) ∗
        [∗ map] k↦v ∈ m1, k ↪[γ] v.
  Proof.
    iIntros (?) "Hauth Hfrag".
    iMod (ghost_map_elems_unseal with "Hfrag") as "Hfrag".
    unseal. rewrite -big_opM_own_1 -own_op.
    iApply (own_update_2 with "Hauth Hfrag").
    rewrite map_fmap_union.
    rewrite -!(big_opM_fmap to_agree (λ k, gmap_view_frag k (DfracOwn 1))).
    apply: gmap_view_replace_big.
    - rewrite !dom_fmap_L. done.
    - by apply map_Forall_fmap.
  Qed.

End lemmas.
