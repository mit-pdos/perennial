(** Like Iris's "ghost map" except for an asynchronous map, in which each
    key has a "current" value and an associated set of values that could be
    obtained on crash.

    This is meant to model a scenario in which there is no "correlation" or
    "ordering" between the post-crash values of keys, each value is selected
    independently from that keys set. If you want a version where there is some kind
    of correlation between the values after crash that corresponds to the order of writes,
    you probably want async.v
*)

From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From Perennial.algebra Require Import gmap_rel_view log_heap.
From iris.algebra Require Export dfrac.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.

(* The relation that holds between the auth map and the fragment values *)
Section async_rel.
Context {V : Type} `{Countable V}.

Definition async_rel_raw (n : nat) (va : async V) (v : V) (a : gset V) :=
  v = latest va ∧ (∀ v, v ∈ pending va → v ∈ a).

Lemma async_rel_mono :
  ∀ n1 n2 (va1 va2 : leibnizO (async V)) (v1 v2 : leibnizO V) (a : (gset V)),
    async_rel_raw n1 va1 v1 a →
    va1 ≡{n2}≡ va2 →
    v1 ≡{n2}≡ v2 →
    n2 ≤ n1 →
    async_rel_raw n2 va2 v2 a.
Proof. intros ??????? Hrel -> -> => //=. Qed.


Definition async_rel := GValRel (leibnizO (async V)) (leibnizO V) _ async_rel_raw async_rel_mono.

Global Instance : GvalRelDiscrete _ _ async_rel.
Proof. intros n va v a (?&?) => //=. Qed.

End async_rel.

(** The CMRA we need. *)

Class ghost_async_mapG Σ (K V : Type) `{Countable K, Countable V} := GhostMapG {
  ghost_async_map_inG :> inG Σ (gmap_rel_viewR K (leibnizO (async V)) (leibnizO V) (gset V) async_rel);
}.
Definition ghost_async_mapΣ (K V : Type) `{Countable K, Countable V} : gFunctors :=
  #[ GFunctor (gmap_rel_viewR K (leibnizO (async V)) _ _ async_rel) ].

Global Instance subG_ghost_async_mapΣ Σ (K V : Type) `{Countable K, Countable V} :
  subG (ghost_async_mapΣ K V) Σ → ghost_async_mapG Σ K V.
Proof. solve_inG. Qed.

Section definitions.
  Context `{ghost_async_mapG Σ K V}.

  Definition ghost_async_map_auth_def (γ : gname) (q : Qp) (m : gmap K (async V)) : iProp Σ :=
    own γ (gmap_rel_view_auth (VA:=leibnizO (async V)) (V := leibnizO V) (A := gset V) async_rel q m).
  Definition ghost_async_map_auth_aux : seal (@ghost_async_map_auth_def). Proof. by eexists. Qed.
  Definition ghost_async_map_auth := ghost_async_map_auth_aux.(unseal).
  Definition ghost_async_map_auth_eq :
    @ghost_async_map_auth = @ghost_async_map_auth_def := ghost_async_map_auth_aux.(seal_eq).

  Definition ghost_async_map_elem_def (γ : gname) (k : K) (dq : dfrac) (a : gset V) (v : V) : iProp Σ :=
    own γ (gmap_rel_view_frag (VA:=leibnizO (async V)) (V := leibnizO V) (A := gset V) async_rel
                              k dq a v).
  Definition ghost_async_map_elem_aux : seal (@ghost_async_map_elem_def). Proof. by eexists. Qed.
  Definition ghost_async_map_elem := ghost_async_map_elem_aux.(unseal).
  Definition ghost_async_map_elem_eq : @ghost_async_map_elem = @ghost_async_map_elem_def := ghost_async_map_elem_aux.(seal_eq).
End definitions.

(** FIXME: Refactor these notations using custom entries once Coq bug #13654
has been fixed. *)
Notation "k ↪[ γ ]{ dq }[ a ] v" := (ghost_async_map_elem γ k dq a v)
  (at level 20, γ at level 50, dq at level 50, format "k  ↪[ γ ]{ dq }[ a ]  v") : bi_scope.
Notation "k ↪[ γ ]{# q }[ a ] v" := (k ↪[γ]{DfracOwn q}[a] v)%I
  (at level 20, γ at level 50, q at level 50, format "k  ↪[ γ ]{# q }[ a ]  v") : bi_scope.
Notation "k ↪[ γ ][ a ] v" := (k ↪[γ]{#1}[a] v)%I
  (at level 20, γ at level 50, format "k  ↪[ γ ][ a ]  v") : bi_scope.
Notation "k ↪[ γ ]□[ a ] v" := (k ↪[γ]{DfracDiscarded}[ a ] v)%I
  (at level 20, γ at level 50) : bi_scope.

Local Ltac unseal := rewrite
  ?ghost_async_map_auth_eq /ghost_async_map_auth_def
  ?ghost_async_map_elem_eq /ghost_async_map_elem_def.

Section lemmas.
  Context `{ghost_async_mapG Σ K V}.
  Implicit Types (k : K) (a : gset V) (v : V) (dq : dfrac) (q : Qp) (m : gmap K V) (ma : gmap K (async V)).

  (** * Lemmas about the map elements *)
  Global Instance ghost_async_map_elem_timeless k γ dq a v : Timeless (k ↪[γ]{dq}[a] v).
  Proof. unseal. apply _. Qed.
  Global Instance ghost_async_map_elem_persistent k γ v a : Persistent (k ↪[γ]□[a] v).
  Proof. unseal. apply _. Qed.
  Global Instance ghost_async_map_elem_fractional k γ v a : Fractional (λ q, k ↪[γ]{#q}[a] v)%I.
  Proof. unseal. intros p q. rewrite -own_op gmap_rel_view_frag_add //. Qed.
  Global Instance ghost_async_map_elem_as_fractional k γ q a v :
    AsFractional (k ↪[γ]{#q}[a] v) (λ q, k ↪[γ]{#q}[a] v)%I q.
  Proof. split; first done. apply _. Qed.

  Local Lemma ghost_async_map_elems_unseal γ m dq a :
    ([∗ map] k ↦ v ∈ m, k ↪[γ]{dq}[a] v) ==∗
    own γ ([^op map] k↦v ∈ m,
           gmap_rel_view_frag (VA:=leibnizO (async V)) (V := leibnizO V) (A := gset V) _ k dq a v).
  Proof.
    unseal. destruct (decide (m = ∅)) as [->|Hne].
    - rewrite !big_opM_empty. iIntros "_". iApply own_unit.
    - rewrite big_opM_own //. iIntros "?". done.
  Qed.

  Lemma ghost_async_map_elem_valid k γ dq a v : k ↪[γ]{dq}[a] v -∗ ⌜✓ dq⌝.
  Proof.
    unseal. iIntros "Helem".
    iDestruct (own_valid with "Helem") as %?%gmap_rel_view_frag_valid_frac; eauto.
  Qed.
  Lemma ghost_async_map_elem_valid_2 k γ dq1 dq2 a1 a2 v1 v2 :
    k ↪[γ]{dq1}[a1] v1 -∗ k ↪[γ]{dq2}[a2] v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %?%gmap_rel_view_frag_op_valid_L.
    naive_solver.
  Qed.
  Lemma ghost_async_map_elem_agree k γ dq1 dq2 a1 a2 v1 v2 :
    k ↪[γ]{dq1}[a1] v1 -∗ k ↪[γ]{dq2}[a2] v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Helem1 Helem2".
    iDestruct (ghost_async_map_elem_valid_2 with "Helem1 Helem2") as %[_ ?].
    done.
  Qed.

  (* TODO: there is a bupd form in which the a's can be different and we get the intersection. *)
  Lemma ghost_async_map_elem_combine k γ dq1 dq2 a v1 v2 :
    k ↪[γ]{dq1}[a] v1 -∗ k ↪[γ]{dq2}[a] v2 -∗ k ↪[γ]{dq1 ⋅ dq2}[a] v1 ∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (ghost_async_map_elem_agree with "Hl1 Hl2") as %->.
    unseal. iCombine "Hl1 Hl2" as "Hl". eauto with iFrame.
  Qed.

  Lemma ghost_async_map_elem_frac_ne γ k1 k2 dq1 dq2 a1 a2 v1 v2 :
    ¬ ✓ (dq1 ⋅ dq2) → k1 ↪[γ]{dq1}[a1] v1 -∗ k2 ↪[γ]{dq2}[a2] v2 -∗ ⌜k1 ≠ k2⌝.
  Proof.
    iIntros (?) "H1 H2"; iIntros (->).
    by iDestruct (ghost_async_map_elem_valid_2 with "H1 H2") as %[??].
  Qed.
  Lemma ghost_async_map_elem_ne γ k1 k2 dq2 a1 a2 v1 v2 :
    k1 ↪[γ][a1] v1 -∗ k2 ↪[γ]{dq2}[a2] v2 -∗ ⌜k1 ≠ k2⌝.
  Proof. apply ghost_async_map_elem_frac_ne. apply: exclusive_l. Qed.

  (** Make an element read-only. *)
  Lemma ghost_async_map_elem_persist k γ dq a v :
    k ↪[γ]{dq}[a] v ==∗ k ↪[γ]□[a] v.
  Proof. unseal. iApply own_update. apply gmap_rel_view_persist. Qed.

  (** * Lemmas about [ghost_async_map_auth] *)
  Lemma ghost_async_map_alloc_strong P ma :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ ghost_async_map_auth γ 1 ma ∗
           [∗ map] k ↦ v ∈ ma, k ↪[γ][list_to_set (pending v)] (latest v).
  Proof.
    unseal. intros.
    iMod (own_alloc_strong (gmap_rel_view_auth (VA:=leibnizO (async V)) (V:=leibnizO V) async_rel 1 ∅) P)
      as (γ) "[% Hauth]"; first done.
    { apply gmap_rel_view_auth_valid. }
    iExists γ. iSplitR; first done.
    rewrite -big_opM_own_1 -own_op. iApply (own_update with "Hauth").
    set (ma' := (λ x : async V, (x, (latest x, (list_to_set (pending x)) : gset V))) <$> ma).
    etrans; first apply: (gmap_rel_view_alloc_big (VA:=leibnizO (async V)) (V:=leibnizO V) _ _ ma' (DfracOwn 1)).
    - intros k vm v aset. rewrite /ma'. rewrite lookup_fmap /= => Hlookup n.
      apply fmap_Some_1 in Hlookup as (?&Hlookup&Heq).
      inversion Heq; subst. rewrite /async_rel_raw. split; first done.
      intros v. apply elem_of_list_to_set.
    - apply map_disjoint_empty_r.
    - done.
    - rewrite right_id.
      assert (Heq1: fst <$> ma' = ma).
      { rewrite /ma' -map_fmap_compose.
        rewrite -[a in _ = a]map_fmap_id. apply map_fmap_ext => //=. }
      rewrite Heq1. rewrite /ma' ?big_opM_fmap //=.
  Qed.
  Lemma ghost_async_map_alloc_strong_empty P :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ ghost_async_map_auth γ 1 (∅ : gmap K _).
  Proof.
    intros. iMod (ghost_async_map_alloc_strong P ∅) as (γ) "(% & Hauth & _)"; eauto.
  Qed.
  Lemma ghost_async_map_alloc ma :
    ⊢ |==> ∃ γ, ghost_async_map_auth γ 1 ma ∗ [∗ map] k ↦ v ∈ ma, k ↪[γ][list_to_set (pending v)]  (latest v).
  Proof.
    iMod (ghost_async_map_alloc_strong (λ _, True) ma) as (γ) "[_ Hmap]".
    - by apply pred_infinite_True.
    - eauto.
  Qed.
  Lemma ghost_async_map_alloc_empty :
    ⊢ |==> ∃ γ, ghost_async_map_auth γ 1 (∅ : gmap K _).
  Proof.
    intros. iMod (ghost_async_map_alloc ∅) as (γ) "(Hauth & _)"; eauto.
  Qed.

  Global Instance ghost_async_map_auth_timeless γ q ma : Timeless (ghost_async_map_auth γ q ma).
  Proof. unseal. apply _. Qed.
  Global Instance ghost_async_map_auth_fractional γ ma : Fractional (λ q, ghost_async_map_auth γ q ma)%I.
  Proof. intros p q. unseal. rewrite -own_op gmap_rel_view_auth_frac_op //. Qed.
  Global Instance ghost_async_map_auth_as_fractional γ q ma :
    AsFractional (ghost_async_map_auth γ q ma) (λ q, ghost_async_map_auth γ q ma)%I q.
  Proof. split; first done. apply _. Qed.

  Lemma ghost_async_map_auth_valid γ q ma : ghost_async_map_auth γ q ma -∗ ⌜q ≤ 1⌝%Qp.
  Proof.
    unseal. iIntros "Hauth".
    iDestruct (own_valid with "Hauth") as %?%gmap_rel_view_auth_frac_valid.
    done.
  Qed.
  Lemma ghost_async_map_auth_valid_2 γ q1 q2 ma1 ma2 :
    ghost_async_map_auth γ q1 ma1 -∗ ghost_async_map_auth γ q2 ma2 -∗ ⌜(q1 + q2 ≤ 1)%Qp ∧ ma1 = ma2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[??]%gmap_rel_view_auth_frac_op_valid_L.
    done.
  Qed.
  Lemma ghost_async_map_auth_agree γ q1 q2 ma1 ma2 :
    ghost_async_map_auth γ q1 ma1 -∗ ghost_async_map_auth γ q2 ma2 -∗ ⌜ma1 = ma2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_async_map_auth_valid_2 with "H1 H2") as %[_ ?].
    done.
  Qed.

  (** * Lemmas about the interaction of [ghost_async_map_auth] with the elements *)
  Lemma ghost_async_map_lookup {γ q ma k dq a v} :
    ghost_async_map_auth γ q ma -∗ k ↪[γ]{dq}[a] v -∗
   ⌜∃ vm, ma !! k = Some vm ∧ latest vm = v ∧ (∀ x, x ∈ pending vm → x ∈ a) ⌝.
  Proof.
    unseal. iIntros "Hauth Hel".
    iDestruct (own_valid_2 with "Hauth Hel") as %[vm[?[?[? Hrel]]]]%gmap_rel_view_both_frac_valid_L.
    iPureIntro. exists vm. specialize (Hrel O). destruct Hrel as (?&?).
    split_and!; auto.
  Qed.

  Lemma ghost_async_map_insert {γ ma} k v al :
    ma !! k = None →
    ghost_async_map_auth γ 1 ma ==∗
    ghost_async_map_auth γ 1 (<[k := Build_async v al]> ma) ∗ k ↪[γ][list_to_set al] v.
  Proof.
    unseal. intros ?. rewrite -own_op.
    iApply own_update. apply: gmap_rel_view_alloc; try done.
    intros n. rewrite //=; split => //=. intros. rewrite elem_of_list_to_set //.
  Qed.
  Lemma ghost_async_map_insert_persist {γ ma} k v al :
    ma !! k = None →
    ghost_async_map_auth γ 1 ma ==∗
    ghost_async_map_auth γ 1 (<[k := Build_async v al]> ma) ∗ k ↪[γ]□[list_to_set al] v.
  Proof.
    iIntros (?) "Hauth".
    iMod (ghost_async_map_insert k with "Hauth") as "[$ Helem]"; first done.
    iApply ghost_async_map_elem_persist. done.
  Qed.

  Lemma ghost_async_map_delete {γ ma k a v} :
    ghost_async_map_auth γ 1 ma -∗ k ↪[γ][a] v ==∗ ghost_async_map_auth γ 1 (delete k ma).
  Proof.
    unseal. apply bi.wand_intro_r. rewrite -own_op.
    iApply own_update. apply: gmap_rel_view_delete.
  Qed.

  Lemma ghost_async_map_update' {γ ma k a a' al v} w :
    (∀ x, x ∈ al → x ∈ a') →
    ghost_async_map_auth γ 1 ma -∗
    k ↪[γ][a] v ==∗
    ghost_async_map_auth γ 1 (<[k := Build_async w al]> ma) ∗ k ↪[γ][a'] w.
  Proof.
    intros Hsub.
    unseal. apply bi.wand_intro_r. rewrite -!own_op.
    apply own_update. apply: gmap_rel_view_update.
    intros n. rewrite //=; split => //=.
  Qed.

  Lemma ghost_async_map_update {γ ma k a al' v} w :
    ghost_async_map_auth γ 1 ma -∗
    k ↪[γ][a] v ==∗
    ghost_async_map_auth γ 1 (<[k := Build_async w al']> ma) ∗ k ↪[γ][list_to_set al'] w.
  Proof.
    apply ghost_async_map_update'. intros; rewrite elem_of_list_to_set //.
  Qed.

  Lemma ghost_async_map_async_put {γ ma k a vm v} w :
    ma !! k = Some vm →
    ghost_async_map_auth γ 1 ma -∗
    k ↪[γ][a] v ==∗
    ghost_async_map_auth γ 1 (<[k := async_put w vm]> ma) ∗ k ↪[γ][{[v]} ∪ a] w.
  Proof.
    intros Hlook. iIntros "H1 H2".
    iDestruct (ghost_async_map_lookup with "[$] [$]") as %Hlook'.
    destruct Hlook' as (vm'&Heq&Hlatest&Hsub).
    rewrite Heq in Hlook. inversion Hlook; subst.
    iApply (ghost_async_map_update' with "[$] [$]").
    rewrite /possible. intros v. rewrite elem_of_app. set_solver.
  Qed.

  Lemma ghost_async_map_flush_auth {γ} ma :
    ghost_async_map_auth γ 1 ma ==∗ ghost_async_map_auth γ 1 (flush <$> ma).
  Proof.
    unseal. apply own_update. apply: gmap_rel_view_update_fmap.
    intros k vm v a n Hlookup Hrel.
    destruct Hrel as (Heq&Hsubset). split; first done.
    intros x Hin. set_solver.
  Qed.

  Lemma ghost_async_map_update_approx {γ ma k dq a v vm} :
    ma !! k = Some vm →
    ghost_async_map_auth γ 1 ma -∗
    k ↪[γ]{dq}[a] v ==∗
    ghost_async_map_auth γ 1 ma ∗ k ↪[γ]{dq}[list_to_set (pending vm)] v.
  Proof.
    intros Hlook.
    unseal. apply bi.wand_intro_r. rewrite -!own_op.
    apply own_update. apply: gmap_rel_view_update_approx.
    intros vm' n Hlookup Hrel1.
    assert (vm = vm') as ->.
    { rewrite Hlook in Hlookup. inversion Hlookup. eauto. }
    destruct Hrel1.
    rewrite //=; split => //=. intros. rewrite elem_of_list_to_set //.
  Qed.

  (* TODO: a stronger version of this is provable in which one merely has fractional ownership of
     k and gets that same fraction back. *)
  Lemma ghost_async_map_update_flush_big {γ ma m} :
    ghost_async_map_auth γ 1 ma -∗
    ([∗ map] k↦v ∈ m, ∃ a, k ↪[γ][a] v) ==∗
    ghost_async_map_auth γ 1 (flush <$> ma) ∗
    ([∗ map] k↦v ∈ m, k ↪[γ][∅] v).
  Proof.
    iIntros "Hauth Hfrag".
    iMod (ghost_async_map_flush_auth with "Hauth") as "Hauth".
    iInduction m as [| k v m Hlookup] "IH" using map_ind.
    { rewrite ?big_sepM_empty. eauto. }
    rewrite ?big_sepM_insert //.
    iDestruct "Hfrag" as "(Hk&Hm)".
    iMod ("IH" with "[$] [$]") as "(Hauth&$)".
    iDestruct "Hk" as (?) "Hk".
    iDestruct (ghost_async_map_lookup with "[$] [$]") as %Hlook.
    destruct Hlook as (vm&Hlook&Heq&Hsub).
    iMod (ghost_async_map_update_approx with "[$] [$]") as "($&Hp)"; first eauto.
    rewrite lookup_fmap in Hlook.
    apply fmap_Some_1 in Hlook as (?&Hlook&Heq').
    rewrite Heq' => //=.
  Qed.

  (** Big-op versions of above lemmas *)
  (* TODO: Update these. *)
  (*
  Lemma ghost_async_map_lookup_big {γ q m} m0 :
    ghost_async_map_auth γ q m -∗
    ([∗ map] k↦v ∈ m0, k ↪[γ] v) -∗
    ⌜m0 ⊆ m⌝.
  Proof.
    iIntros "Hauth Hfrag". rewrite map_subseteq_spec. iIntros (k v Hm0).
    iDestruct (ghost_async_map_lookup with "Hauth [Hfrag]") as %->.
    { rewrite big_sepM_lookup; done. }
    done.
  Qed.

  Lemma ghost_async_map_insert_big {γ m} m' :
    m' ##ₘ m →
    ghost_async_map_auth γ 1 m ==∗
    ghost_async_map_auth γ 1 (m' ∪ m) ∗ ([∗ map] k ↦ v ∈ m', k ↪[γ] v).
  Proof.
    unseal. intros ?. rewrite -big_opM_own_1 -own_op.
    apply own_update. apply: gmap_view_alloc_big; done.
  Qed.
  Lemma ghost_async_map_insert_persist_big {γ m} m' :
    m' ##ₘ m →
    ghost_async_map_auth γ 1 m ==∗
    ghost_async_map_auth γ 1 (m' ∪ m) ∗ ([∗ map] k ↦ v ∈ m', k ↪[γ]□ v).
  Proof.
    iIntros (Hdisj) "Hauth".
    iMod (ghost_async_map_insert_big m' with "Hauth") as "[$ Helem]"; first done.
    iApply big_sepM_bupd. iApply (big_sepM_impl with "Helem").
    iIntros "!#" (k v) "_". iApply ghost_async_map_elem_persist.
  Qed.

  Lemma ghost_async_map_delete_big {γ m} m0 :
    ghost_async_map_auth γ 1 m -∗
    ([∗ map] k↦v ∈ m0, k ↪[γ] v) ==∗
    ghost_async_map_auth γ 1 (m ∖ m0).
  Proof.
    iIntros "Hauth Hfrag". iMod (ghost_async_map_elems_unseal with "Hfrag") as "Hfrag".
    unseal. iApply (own_update_2 with "Hauth Hfrag").
    apply: gmap_view_delete_big.
  Qed.

  Theorem ghost_async_map_update_big {γ m} m0 m1 :
    dom (gset K) m0 = dom (gset K) m1 →
    ghost_async_map_auth γ 1 m -∗
    ([∗ map] k↦v ∈ m0, k ↪[γ] v) ==∗
    ghost_async_map_auth γ 1 (m1 ∪ m) ∗
        [∗ map] k↦v ∈ m1, k ↪[γ] v.
  Proof.
    iIntros (?) "Hauth Hfrag". iMod (ghost_async_map_elems_unseal with "Hfrag") as "Hfrag".
    unseal. rewrite -big_opM_own_1 -own_op.
    iApply (own_update_2 with "Hauth Hfrag").
    apply: gmap_view_update_big. done.
  Qed.
  *)

End lemmas.
