From Coq.QArith Require Import Qcanon.
From iris.algebra Require Export view gmap frac dfrac.
From iris.algebra Require Import local_updates proofmode_classes big_op.
From iris.prelude Require Import options.

(** * CMRA for a "view of a gmap".

The authoritative element [gmap_view_auth] is any [gmap K V].  The fragments
[gmap_view_frag] represent ownership of a single key in that map.  Ownership is
governed by a discardable fraction, which provides the possibiltiy to obtain
persistent read-only ownership of a key.

The key frame-preserving updates are [gmap_view_alloc] to allocate a new key,
[gmap_view_update] to update a key given full ownership of the corresponding
fragment, and [gmap_view_persist] to make a key read-only by discarding any
fraction of the corresponding fragment. Crucially, the latter does not require
owning the authoritative element.

NOTE: The API surface for [gmap_view] is experimental and subject to change.  We
plan to add notations for authoritative elements and fragments, and hope to
support arbitrary maps as fragments. *)

Local Definition gmap_view_fragUR (K : Type) `{Countable K} (V : cmra) : ucmra :=
  gmapUR K (prodR dfracR V).

(** View relation. *)
Section rel.
  Context (K : Type) `{Countable K} (V : cmra).
  Implicit Types (m : gmap K V) (k : K) (v : V) (n : nat).
  Implicit Types (f : gmap K (dfrac * V)).


  (* FIXME: we should really have a name and theory for the reflexive closure of [≼]... *)
  Local Definition gmap_view_rel_raw n m f : Prop :=
    map_Forall (λ k dv, ∃ v, m !! k = Some v ∧ ✓{n} v ∧ (dv ≼{n} ((DfracOwn 1, v):prodR _ _) ∨ dv ≡{n}≡ (DfracOwn 1, v)) ∧ ✓ dv.1) f.

  Local Lemma gmap_view_rel_raw_mono n1 n2 m1 m2 f1 f2 :
    gmap_view_rel_raw n1 m1 f1 →
    m1 ≡{n2}≡ m2 →
    f2 ≼{n2} f1 →
    n2 ≤ n1 →
    gmap_view_rel_raw n2 m2 f2.
  Proof.
    intros Hrel Hm Hf Hn k [q va] Hk.
    (* For some reason applying the lemma in [Hf] does not work... *)
    destruct (lookup_includedN n2 f2 f1) as [Hf' _]. specialize (Hf' Hf). clear Hf.
    specialize (Hf' k). rewrite Hk in Hf'.
    apply option_includedN in Hf'.
    destruct Hf' as [[=]|(? & [q' va'] & [= <-] & Hf1 & Hincl)].
    specialize (Hrel _ _ Hf1) as (v & Hm1 & Hvval & Hvincl & Hdval). simpl in *.
    specialize (Hm k).
    edestruct (dist_Some_inv_l _ _ _ _ Hm Hm1) as (v' & Hm2 & Hv).
    eexists. split; first done. split.
    { rewrite -Hv. eapply cmra_validN_le; done. }
    rewrite -Hv.
    destruct Hincl as [[Heqq Heqva]|[Hinclq Hinclva]%pair_includedN].
    - simpl in *. split.
      + rewrite Heqva Heqq. destruct Hvincl.
        * left. eapply cmra_includedN_le; last eassumption. done.
        * right. eapply dist_le; last eassumption. done.
      + rewrite <-discrete_iff in Heqq; last by apply _.
        fold_leibniz. subst q'. done.
    - split.
      + left. destruct Hvincl.
        * transitivity (q', va').
          2:{
            by eapply cmra_includedN_le; last eassumption.
          }
          apply pair_includedN; split; done.
        * apply pair_includedN; split.
          { by destruct H0 as [<- ?]; simpl in *. }
          eapply dist_le in H0; last done.
          by destruct H0 as [? <-]; simpl in *.
      + rewrite <-cmra_discrete_included_iff in Hinclq.
        eapply cmra_valid_included; done.
  Qed.

  Local Lemma gmap_view_rel_raw_valid n m f :
    gmap_view_rel_raw n m f → ✓{n} f.
  Proof.
    intros Hrel k. destruct (f !! k) as [[q va]|] eqn:Hf; rewrite Hf; last done.
    specialize (Hrel _ _ Hf) as (v & Hm1 & Hmval & Hvincl & Hdval). simpl in *.
    split; simpl.
    - apply cmra_discrete_valid_iff. done.
    - destruct Hvincl as [?|Hveq].
      + eapply pair_includedN in H0 as [? ?]. eapply cmra_validN_includedN; done.
      + destruct Hveq as [? ->]. done.
  Qed.

  Local Lemma gmap_view_rel_raw_unit n :
    ∃ m, gmap_view_rel_raw n m ε.
  Proof. exists ∅. apply: map_Forall_empty. Qed.

  Local Canonical Structure gmap_view_rel : view_rel (gmapO K V) (gmap_view_fragUR K V) :=
    ViewRel gmap_view_rel_raw gmap_view_rel_raw_mono
            gmap_view_rel_raw_valid gmap_view_rel_raw_unit.

  Local Lemma gmap_view_rel_exists n f :
    (∃ m, gmap_view_rel n m f) ↔ ✓{n} f.
  Proof.
    split.
    { intros [m Hrel]. eapply gmap_view_rel_raw_valid, Hrel. }
    intros Hf.
    cut (∃ m, gmap_view_rel n m f ∧ ∀ k, f !! k = None → m !! k = None).
    { naive_solver. }
    induction f as [|k [dq v] f Hk' IH] using map_ind.
    { exists ∅. split; [|done]. apply: map_Forall_empty. }
    move: (Hf k). rewrite lookup_insert=> -[/= ??].
    destruct IH as (m & Hm & Hdom).
    { intros k'. destruct (decide (k = k')) as [->|?]; [by rewrite Hk'|].
      move: (Hf k'). by rewrite lookup_insert_ne. }
    exists (<[k:=v]> m).
    rewrite /gmap_view_rel /= /gmap_view_rel_raw map_Forall_insert //=. split_and!.
    - exists v. rewrite lookup_insert. eauto.
    - eapply map_Forall_impl; [apply Hm|]; simpl.
      intros k' [dq' ag'] (v'&?&?&?). exists v'.
      rewrite lookup_insert_ne; naive_solver.
    - intros k'. rewrite !lookup_insert_None. naive_solver.
  Qed.

  Local Lemma gmap_view_rel_unit n m : gmap_view_rel n m ε.
  Proof. apply: map_Forall_empty. Qed.

  Local Lemma gmap_view_rel_discrete :
    CmraDiscrete V → ViewRelDiscrete gmap_view_rel.
  Proof.
    intros ? n m f Hrel k [df va] Hk.
    destruct (Hrel _ _ Hk) as (v & Hm & Hvval & Hvincl & Hdval).
    exists v. split; first done.
    split; first by apply cmra_discrete_valid_iff_0.
    split; last done.
    destruct Hvincl.
    - left. by apply cmra_discrete_included_iff_0.
    - right. eapply discrete_iff_0; first by apply _. done.
  Qed.
End rel.

Local Existing Instance gmap_view_rel_discrete.

(** [gmap_view] is a notation to give canonical structure search the chance
to infer the right instances (see [auth]). *)
Notation gmap_view K V := (view (@gmap_view_rel_raw K _ _ V)).
Definition gmap_viewO (K : Type) `{Countable K} (V : cmra) : ofe :=
  viewO (gmap_view_rel K V).
Definition gmap_viewR (K : Type) `{Countable K} (V : cmra) : cmra :=
  viewR (gmap_view_rel K V).
Definition gmap_viewUR (K : Type) `{Countable K} (V : cmra) : ucmra :=
  viewUR (gmap_view_rel K V).

Section definitions.
  Context {K : Type} `{Countable K} {V : cmra}.

  Definition gmap_view_auth (dq : dfrac) (m : gmap K V) : gmap_viewR K V :=
    ●V{dq} m.
  Definition gmap_view_frag (k : K) (dq : dfrac) (v : V) : gmap_viewR K V :=
    ◯V {[k := (dq, v)]}.
End definitions.

Section lemmas.
  Context {K : Type} `{Countable K} {V : cmra}.
  Implicit Types (m : gmap K V) (k : K) (q : Qp) (dq : dfrac) (v : V).

  Global Instance : Params (@gmap_view_auth) 5 := {}.
  Global Instance gmap_view_auth_ne dq : NonExpansive (gmap_view_auth (K:=K) (V:=V) dq).
  Proof. solve_proper. Qed.
  Global Instance gmap_view_auth_proper dq : Proper ((≡) ==> (≡)) (gmap_view_auth (K:=K) (V:=V) dq).
  Proof. apply ne_proper, _. Qed.

  Global Instance : Params (@gmap_view_frag) 6 := {}.
  Global Instance gmap_view_frag_ne k oq : NonExpansive (gmap_view_frag (V:=V) k oq).
  Proof. solve_proper. Qed.
  Global Instance gmap_view_frag_proper k oq : Proper ((≡) ==> (≡)) (gmap_view_frag (V:=V) k oq).
  Proof. apply ne_proper, _. Qed.

  (* Helper lemmas *)
  Local Lemma gmap_view_rel_lookup n m k dq v :
    gmap_view_rel K V n m {[k := (dq, v)]} ↔
            ∃ v', m !! k = Some v' ∧ ✓{n} v' ∧ (v ≼{n} v' ∨ v ≡{n}≡ v') ∧ ✓ dq.
  Proof.
    split.
    - intros Hrel.
      edestruct (Hrel k) as (v' & Hval & ? & ? & ?).
      { rewrite lookup_singleton. done. }
      simpl in *. exists v'. split_and!; try assumption.
    - intros (v' & Hm & Hv' & Hvinc & Hdq). intros j [df va].
      destruct (decide (k = j)) as [<-|Hne]; last by rewrite lookup_singleton_ne.
      rewrite lookup_singleton. intros [= <- <-]. simpl.
      exists v'. split_and!; done.
  Qed.

  (** Composition and validity *)
  Lemma gmap_view_auth_dfrac_op dp dq m :
    gmap_view_auth (dp ⋅ dq) m ≡
    gmap_view_auth dp m ⋅ gmap_view_auth dq m.
  Proof. by rewrite /gmap_view_auth view_auth_dfrac_op. Qed.
  Global Instance gmap_view_auth_dfrac_is_op dq dq1 dq2 m :
    IsOp dq dq1 dq2 → IsOp' (gmap_view_auth dq m) (gmap_view_auth dq1 m) (gmap_view_auth dq2 m).
  Proof. rewrite /gmap_view_auth. apply _. Qed.

  Lemma gmap_view_auth_dfrac_op_invN n dp m1 dq m2 :
    ✓{n} (gmap_view_auth dp m1 ⋅ gmap_view_auth dq m2) → m1 ≡{n}≡ m2.
  Proof. apply view_auth_dfrac_op_invN. Qed.
  Lemma gmap_view_auth_dfrac_op_inv dp m1 dq m2 :
    ✓ (gmap_view_auth dp m1 ⋅ gmap_view_auth dq m2) → m1 ≡ m2.
  Proof. apply view_auth_dfrac_op_inv. Qed.
  Lemma gmap_view_auth_dfrac_op_inv_L `{!LeibnizEquiv V} dq m1 dp m2 :
    ✓ (gmap_view_auth dp m1 ⋅ gmap_view_auth dq m2) → m1 = m2.
  Proof. apply view_auth_dfrac_op_inv_L, _. Qed.

  Lemma gmap_view_auth_dfrac_validN m n dq : ✓{n} gmap_view_auth dq m ↔ ✓ dq.
  Proof.
    rewrite view_auth_dfrac_validN. intuition eauto using gmap_view_rel_unit.
  Qed.
  Lemma gmap_view_auth_dfrac_valid m dq : ✓ gmap_view_auth dq m ↔ ✓ dq.
  Proof.
    rewrite view_auth_dfrac_valid. intuition eauto using gmap_view_rel_unit.
  Qed.
  Lemma gmap_view_auth_valid m : ✓ gmap_view_auth (DfracOwn 1) m.
  Proof. rewrite gmap_view_auth_dfrac_valid. done. Qed.

  Lemma gmap_view_auth_dfrac_op_validN n dq1 dq2 m1 m2 :
    ✓{n} (gmap_view_auth dq1 m1 ⋅ gmap_view_auth dq2 m2) ↔ ✓ (dq1 ⋅ dq2) ∧ m1 ≡{n}≡ m2.
  Proof.
    rewrite view_auth_dfrac_op_validN. intuition eauto using gmap_view_rel_unit.
  Qed.
  Lemma gmap_view_auth_dfrac_op_valid dq1 dq2 m1 m2 :
    ✓ (gmap_view_auth dq1 m1 ⋅ gmap_view_auth dq2 m2) ↔ ✓ (dq1 ⋅ dq2) ∧ m1 ≡ m2.
  Proof.
    rewrite view_auth_dfrac_op_valid. intuition eauto using gmap_view_rel_unit.
  Qed.
  Lemma gmap_view_auth_dfrac_op_valid_L `{!LeibnizEquiv V} dq1 dq2 m1 m2 :
    ✓ (gmap_view_auth dq1 m1 ⋅ gmap_view_auth dq2 m2) ↔ ✓ (dq1 ⋅ dq2) ∧ m1 = m2.
  Proof. unfold_leibniz. apply gmap_view_auth_dfrac_op_valid. Qed.

  Lemma gmap_view_auth_op_validN n m1 m2 :
    ✓{n} (gmap_view_auth (DfracOwn 1) m1 ⋅ gmap_view_auth (DfracOwn 1) m2) ↔ False.
  Proof. apply view_auth_op_validN. Qed.
  Lemma gmap_view_auth_op_valid m1 m2 :
    ✓ (gmap_view_auth (DfracOwn 1) m1 ⋅ gmap_view_auth (DfracOwn 1) m2) ↔ False.
  Proof. apply view_auth_op_valid. Qed.

  Lemma gmap_view_frag_validN n k dq v : ✓{n} gmap_view_frag k dq v ↔ ✓ dq ∧ ✓{n} v.
  Proof.
    rewrite view_frag_validN gmap_view_rel_exists singleton_validN pair_validN.
    naive_solver.
  Qed.
  Lemma gmap_view_frag_valid k dq v : ✓ gmap_view_frag k dq v ↔ ✓ dq ∧ ✓ v.
  Proof.
    rewrite cmra_valid_validN. setoid_rewrite gmap_view_frag_validN.
    rewrite (cmra_valid_validN v).
    naive_solver eauto using O.
  Qed.

  Lemma gmap_view_frag_op k dq1 dq2 v1 v2 :
    gmap_view_frag k (dq1 ⋅ dq2) (v1 ⋅ v2) ≡ gmap_view_frag k dq1 v1 ⋅ gmap_view_frag k dq2 v2.
  Proof. rewrite -view_frag_op singleton_op -pair_op //. Qed.
  Lemma gmap_view_frag_add k q1 q2 v1 v2 :
    gmap_view_frag k (DfracOwn (q1 + q2)) (v1 ⋅ v2) ≡
      gmap_view_frag k (DfracOwn q1) v1 ⋅ gmap_view_frag k (DfracOwn q2) v2.
  Proof. rewrite -gmap_view_frag_op. done. Qed.

  Lemma gmap_view_frag_op_validN n k dq1 dq2 v1 v2 :
    ✓{n} (gmap_view_frag k dq1 v1 ⋅ gmap_view_frag k dq2 v2) ↔
      ✓ (dq1 ⋅ dq2) ∧ ✓{n} (v1 ⋅ v2).
  Proof.
    rewrite view_frag_validN gmap_view_rel_exists singleton_op singleton_validN.
    by rewrite -pair_op pair_validN.
  Qed.
  Lemma gmap_view_frag_op_valid k dq1 dq2 v1 v2 :
    ✓ (gmap_view_frag k dq1 v1 ⋅ gmap_view_frag k dq2 v2) ↔ ✓ (dq1 ⋅ dq2) ∧ ✓ (v1 ⋅ v2).
  Proof.
    rewrite view_frag_valid. setoid_rewrite gmap_view_rel_exists.
    rewrite -cmra_valid_validN singleton_op singleton_valid.
    by rewrite -pair_op pair_valid.
  Qed.
  (* FIXME: Having a [valid_L] lemma is not consistent with [auth] and [view]; they
     have [inv_L] lemmas instead that just have an equality on the RHS. *)
  (*
  Lemma gmap_view_frag_op_valid_L `{!LeibnizEquiv V} k dq1 dq2 v1 v2 :
    ✓ (gmap_view_frag k dq1 v1 ⋅ gmap_view_frag k dq2 v2) ↔ ✓ (dq1 ⋅ dq2) ∧ ✓ (v1 ⋅ v2).
  Proof. unfold_leibniz. apply gmap_view_frag_op_valid. Qed. *)

  Lemma gmap_view_both_dfrac_validN n dp m k dq v :
    ✓{n} (gmap_view_auth dp m ⋅ gmap_view_frag k dq v) ↔
     ✓ dp ∧ ✓ dq ∧ ∃ v', m !! k = Some v' ∧ ✓{n} v' ∧ (v ≼{n} v' ∨ v ≡{n}≡ v').
  Proof.
    rewrite /gmap_view_auth /gmap_view_frag.
    rewrite view_both_dfrac_validN gmap_view_rel_lookup.
    split.
    { intros [Hp (v' & Hm & ? & ? & ?)]. split_and!; try naive_solver. }
    { intros [v' ?]. split_and!; try naive_solver. }
  Qed.
  Lemma gmap_view_both_validN n m k dq v :
    ✓{n} (gmap_view_auth (DfracOwn 1) m ⋅ gmap_view_frag k dq v) ↔
       ✓ dq ∧ ∃ v', m !! k = Some v' ∧ ✓{n} v' ∧ (v ≼{n} v' ∨ v ≡{n}≡ v').
  Proof. rewrite gmap_view_both_dfrac_validN. naive_solver done. Qed.

  Lemma gmap_view_both_dfrac_valid_discrete `{!CmraDiscrete V} dp m k dq v :
    ✓ (gmap_view_auth dp m ⋅ gmap_view_frag k dq v) ↔
    ✓ dp ∧ ✓ dq ∧  ∃ v', m !! k = Some v' ∧ ✓ v' ∧ (v ≼ v' ∨ v ≡ v').
  Proof.
    rewrite /gmap_view_auth /gmap_view_frag.
    rewrite view_both_dfrac_valid. setoid_rewrite gmap_view_rel_lookup.
    split=>[[Hq Hm]|[Hq Hm]].
    - split; first done. split.
      + specialize (Hm 0%nat). naive_solver.
      + destruct (Hm 0%nat) as (? & -> & ? & ? & ?).
        exists x. split; first done.
        rewrite cmra_discrete_included_iff discrete_iff cmra_discrete_valid_iff.
        done.
    - split; first done. intros n.
      destruct Hm as [? (? & ? & ? & ?)].
      exists x. split.
      + done.
      + rewrite -cmra_discrete_included_iff -discrete_iff -cmra_discrete_valid_iff.
        split_and!; auto.
  Qed.

  Lemma gmap_view_both_dfrac_valid_L `{!CmraDiscrete V} `{!LeibnizEquiv V} dp m k dq v :
    ✓ (gmap_view_auth dp m ⋅ gmap_view_frag k dq v) ↔
    ✓ dp ∧ ✓ dq ∧  ∃ v', m !! k = Some v' ∧ ✓ v' ∧ (v ≼ v' ∨ v = v').
  Proof. setoid_rewrite <-(leibniz_equiv_iff (A:=V)).
         apply gmap_view_both_dfrac_valid_discrete. Qed.
  Lemma gmap_view_both_valid `{!CmraDiscrete V} m k dq v :
    ✓ (gmap_view_auth (DfracOwn 1) m ⋅ gmap_view_frag k dq v) ↔
    ✓ dq ∧  ∃ v', m !! k = Some v' ∧ ✓ v' ∧ (v ≼ v' ∨ v ≡ v').
  Proof. rewrite gmap_view_both_dfrac_valid_discrete. naive_solver done. Qed.
  (* FIXME: Having a [valid_L] lemma is not consistent with [auth] and [view]; they
     have [inv_L] lemmas instead that just have an equality on the RHS. *)
  (*
  Lemma gmap_view_both_valid_L `{!LeibnizEquiv V} m k dq v :
    ✓ (gmap_view_auth (DfracOwn 1) m ⋅ gmap_view_frag k dq v) ↔
    ✓ dq ∧ m !! k = Some v.
  Proof. unfold_leibniz. apply gmap_view_both_valid. Qed. *)

  (** Frame-preserving updates *)
  Lemma gmap_view_alloc m k dq v :
    m !! k = None →
    ✓ dq →
    ✓ v →
    gmap_view_auth (DfracOwn 1) m ~~> gmap_view_auth (DfracOwn 1) (<[k := v]> m) ⋅ gmap_view_frag k dq v.
  Proof.
    intros Hfresh Hdq Hvalid. apply view_update_alloc=>n bf Hrel j [df va] /=.
    rewrite lookup_op. destruct (decide (j = k)) as [->|Hne].
    - assert (bf !! k = None) as Hbf.
      { destruct (bf !! k) as [[df' va']|] eqn:Hbf; last done.
        specialize (Hrel _ _ Hbf). destruct Hrel as (v' & Hm & _).
        exfalso. rewrite Hm in Hfresh. done. }
      rewrite lookup_singleton Hbf right_id.
      intros [= <- <-]. eexists.
      rewrite lookup_insert. split; first done.
      split.
      { clear Hrel. revert n. rewrite -cmra_valid_validN. done. }
      split; last done.
      left.
      by right.
    - rewrite lookup_singleton_ne; last done.
      rewrite left_id=>Hbf.
      specialize (Hrel _ _ Hbf). destruct Hrel as (v' & ? & ? & ? & ?).
      eexists.
      split; first rewrite lookup_insert_ne //.
      split; first done.
      rewrite /= in H2.
      done.
  Qed.

  Lemma gmap_view_alloc_big m m' dq :
    m' ##ₘ m →
    ✓ dq →
    map_Forall (λ k v, ✓ v) m' →
    gmap_view_auth (DfracOwn 1) m ~~>
    gmap_view_auth (DfracOwn 1) (m' ∪ m) ⋅ ([^op map] k↦v ∈ m', gmap_view_frag k dq v).
  Proof.
    intros. induction m' as [|k v m' ? IH] using map_ind; decompose_map_disjoint.
    { rewrite big_opM_empty left_id_L right_id. done. }
    rewrite IH //.
    2:{ by eapply map_Forall_insert_1_2. }
    rewrite big_opM_insert // assoc.
    apply cmra_update_op; last done.
    rewrite -insert_union_l. apply (gmap_view_alloc _ k dq v).
    { by apply lookup_union_None. }
    { done. }
    { by apply map_Forall_insert_1_1 in H2. }
  Qed.

  Lemma gmap_view_delete m k v :
    gmap_view_auth (DfracOwn 1) m ⋅ gmap_view_frag k (DfracOwn 1) v ~~>
    gmap_view_auth (DfracOwn 1) (delete k m).
  Proof.
    apply view_update_dealloc=>n bf Hrel j [df va] Hbf.
    destruct (decide (j = k)) as [->|Hne].
    - edestruct (Hrel k) as (v' & ? & ? & ? & Hdf).
      { rewrite lookup_op Hbf lookup_singleton -Some_op. done. }
      exfalso. apply: dfrac_full_exclusive. apply Hdf.
    - edestruct (Hrel j) as (v' & ? & ? & Hm).
      { rewrite lookup_op lookup_singleton_ne // Hbf. done. }
      exists v'.
      split; first rewrite lookup_delete_ne //.
      by rewrite /= in Hm.
  Qed.

  Lemma gmap_view_delete_big m m' :
    gmap_view_auth (DfracOwn 1) m ⋅ ([^op map] k↦v ∈ m', gmap_view_frag k (DfracOwn 1) v) ~~>
    gmap_view_auth (DfracOwn 1) (m ∖ m').
  Proof.
    induction m' as [|k v m' ? IH] using map_ind.
    { rewrite right_id_L big_opM_empty right_id //. }
    rewrite big_opM_insert //.
    rewrite [gmap_view_frag _ _ _ ⋅ _]comm assoc IH gmap_view_delete.
    rewrite -delete_difference. done.
  Qed.

  Lemma gmap_view_update m k v v' :
    ✓ v' →
    gmap_view_auth (DfracOwn 1) m ⋅ gmap_view_frag k (DfracOwn 1) v ~~>
    gmap_view_auth (DfracOwn 1) (<[k := v']> m) ⋅ gmap_view_frag k (DfracOwn 1) v'.
  Proof.
    intros.
    rewrite gmap_view_delete.
    rewrite (gmap_view_alloc _ k (DfracOwn 1) v') //.
    { rewrite insert_delete_insert //. }
    { by rewrite lookup_delete. }
  Qed.

  Lemma gmap_view_update_big m m0 m1 :
    dom m0 = dom m1 →
    map_Forall (λ k v, ✓ v) m1 →
    gmap_view_auth (DfracOwn 1) m ⋅ ([^op map] k↦v ∈ m0, gmap_view_frag k (DfracOwn 1) v) ~~>
      gmap_view_auth (DfracOwn 1) (m1 ∪ m) ⋅ ([^op map] k↦v ∈ m1, gmap_view_frag k (DfracOwn 1) v).
  Proof.
    intros Hdom%eq_sym. revert m1 Hdom.
    induction m0 as [|k v m0 Hnotdom IH] using map_ind; intros m1 Hdom Hvalid.
    { rewrite dom_empty_L in Hdom.
      apply dom_empty_iff_L in Hdom as ->.
      rewrite left_id_L big_opM_empty. done. }
    rewrite dom_insert_L in Hdom.
    assert (k ∈ dom m1) as Hindom by set_solver.
    apply elem_of_dom in Hindom as [v' Hlookup].
    rewrite big_opM_insert //.
    rewrite [gmap_view_frag _ _ _ ⋅ _]comm assoc.
    rewrite (IH (delete k m1)); last first.
    { by apply map_Forall_delete. }
    { rewrite dom_delete_L Hdom.
      apply not_elem_of_dom in Hnotdom. set_solver -Hdom. }
    rewrite -assoc [_ ⋅ gmap_view_frag _ _ _]comm assoc.
    rewrite (gmap_view_update _ _ _ v').
    { rewrite (big_opM_delete _ m1 k v') // -assoc.
      rewrite insert_union_r; last by rewrite lookup_delete.
      rewrite union_delete_insert //. }
    { rewrite map_Forall_lookup in Hvalid. eapply Hvalid. done. }
  Qed.

  Print local_update.
  Lemma gmap_view_update_frag m k dq v v' :
    (∀ va, (va, v) ~l~> (va, v')) →
    gmap_view_frag k dq v ~~>
    gmap_view_frag k dq v'.
  Proof.
    intros Hup. apply view_update_frag=> a n bf Hrel j [df va] Hbf.
    destruct (decide (j = k)) as [?|Hne]; first subst.
    {

    }
  Qed.

  Lemma gmap_view_update_local m k dq mv v mv' v' :
    m !! k = Some mv →
    (mv, v) ~l~> (mv', v') →
    gmap_view_auth (DfracOwn 1) m ⋅ gmap_view_frag k dq v ~~>
    gmap_view_auth (DfracOwn 1) (<[k := mv']> m) ⋅ gmap_view_frag k dq v'.
  Proof.
    intros Hm Hup. apply view_update=> n bf Hrel j [df va] Hbf.
    destruct (decide (j = k)) as [?|Hne]; first subst.
    { (* prove the mapForall for k *)
      exists mv'. rewrite lookup_insert. split; first done.
      rewrite lookup_op lookup_singleton in Hbf.
      destruct (bf !! k) as [[? ?]|] eqn:HbfLookup.
      { (* case: k shows up in frame bf *)
        rewrite HbfLookup -Some_op /= in Hbf.
        injection Hbf as <- <-.
        edestruct (Hrel k) as (mv2 & Hm' & ? & Hincl & Hdf).
        { by rewrite lookup_op lookup_singleton HbfLookup. }
        rewrite Hm' in Hm. injection Hm as ->.
        simpl in *.
        destruct Hincl as [[bf']|].
        { (* case: frag val ≼ auth val *)
          edestruct (Hup n (Some (c0 ⋅ bf'))); first done.
          { by rewrite /= assoc. }
          simpl in *.
          split_and!; auto. left. exists (bf').
          by rewrite -assoc.
        }
        { (* case: frag val ≡ auth val *)
          edestruct (Hup n (Some c0)); first done.
          { done. }
          simpl in *.
          split_and!; auto.
        }
      }
      { (* case: k does not show up in frame bf *)
        rewrite HbfLookup /= in Hbf.
        injection Hbf as -> ->.
        edestruct (Hrel k) as (mv2 & Hm' & ? & Hincl & Hdf).
        { by rewrite lookup_op lookup_singleton HbfLookup. }
        simpl in *.
        rewrite Hm' in Hm. injection Hm as ->.
        destruct Hincl as [[bf']|].
        { (* case: frag val is ≼ auth val *)
          edestruct (Hup n (Some bf')); auto. simpl in *.
          split_and!; auto. left. by exists bf'.
        }
        { (* case: frag val ≡ auth val *)
          edestruct (Hup n None); auto.
        }
      }
    }
    { (* prove that other keys are unaffected *)
      rewrite lookup_op lookup_singleton_ne // in Hbf.
      rewrite lookup_insert_ne //.
      edestruct (Hrel j) as (mv2 & Hm' & ? & Hincl & Hdf).
      { rewrite lookup_op lookup_singleton_ne //. }
      simpl in *. exists mv2.
      split_and!; auto.
    }
  Qed.

  Lemma gmap_view_auth_persist dq m :
    gmap_view_auth dq m ~~> gmap_view_auth DfracDiscarded m.
  Proof. apply view_update_auth_persist. Qed.

  Lemma gmap_view_frag_persist k dq v :
    gmap_view_frag k dq v ~~> gmap_view_frag k DfracDiscarded v.
  Proof.
    apply view_update_frag=>m n bf Hrel j [df va] /=.
    rewrite lookup_op. destruct (decide (j = k)) as [->|Hne].
    - rewrite lookup_singleton.
      edestruct (Hrel k ((dq, v) ⋅? bf !! k)) as (v' & Hm & Hva & ? & Hdf).
      { rewrite lookup_op lookup_singleton.
        destruct (bf !! k) eqn:Hbf; by rewrite Hbf. }
      rewrite Some_op_opM. intros [= Hbf].
      exists v'. do 2 (split; first done). rewrite /= in Hdf.
      destruct (bf !! k) as [[df' va']|] eqn:Hbfk; rewrite Hbfk in Hbf; clear Hbfk.
      + simpl in *. rewrite -pair_op in Hbf.
        move:Hbf=>[= <- <-]. split; first done.
        eapply cmra_discrete_valid.
        eapply (dfrac_discard_update _ _ (Some df')).
        apply cmra_discrete_valid_iff. done.
      + simpl in *. move:Hbf=>[= <- <-]. split; done.
    - rewrite lookup_singleton_ne //.
      rewrite left_id=>Hbf.
      edestruct (Hrel j) as (v'' & ? & ? & Hm).
      { rewrite lookup_op lookup_singleton_ne // left_id. done. }
      simpl in *. eexists. do 2 (split; first done). done.
  Qed.

  (** Typeclass instances *)
  Global Instance gmap_view_frag_core_id k dq v : CoreId v → CoreId dq → CoreId (gmap_view_frag k dq v).
  Proof. apply _. Qed.

  Global Instance gmap_view_cmra_discrete : CmraDiscrete V → CmraDiscrete (gmap_viewR K V).
  Proof. apply _. Qed.

  Global Instance gmap_view_frag_mut_is_op dq dq1 dq2 k v v1 v2 :
    IsOp dq dq1 dq2 →
    IsOp v v1 v2 →
    IsOp' (gmap_view_frag k dq v) (gmap_view_frag k dq1 v1) (gmap_view_frag k dq2 v2).
  Proof. rewrite /IsOp' /IsOp /IsOp => -> ->. apply gmap_view_frag_op. Qed.
End lemmas.

(*
(** Functor *)
Program Definition gmap_viewURF (K : Type) `{Countable K} (F : oFunctor) : urFunctor := {|
  urFunctor_car A _ B _ := gmap_viewUR K (agreeR $ oFunctor_car F A B);
  urFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    viewO_map (rel:=gmap_view_rel K (agreeR $ oFunctor_car F A1 B1))
              (rel':=gmap_view_rel K (agreeR $ oFunctor_car F A2 B2))
              (gmapO_map (K:=K) (oFunctor_map F fg))
              (gmapO_map (K:=K) (prodO_map cid (agreeO_map (oFunctor_map F fg))))
|}.
Next Obligation.
  intros.
  rewrite /oFunctor_car.
Qed.
Next Obligation.
  intros K ?? F A1 ? A2 ? B1 ? B2 ? n f g Hfg.
  apply viewO_map_ne.
  - apply gmapO_map_ne, oFunctor_map_ne. done.
  - apply gmapO_map_ne. apply prodO_map_ne; first done.
    apply agreeO_map_ne, oFunctor_map_ne. done.
Qed.
Next Obligation.
  intros K ?? F A ? B ? x; simpl in *. rewrite -{2}(view_map_id x).
  apply (view_map_ext _ _ _ _)=> y.
  - rewrite /= -{2}(map_fmap_id y).
    apply map_fmap_equiv_ext=>k ??.
    apply oFunctor_map_id.
  - rewrite /= -{2}(map_fmap_id y).
    apply map_fmap_equiv_ext=>k [df va] ?.
    split; first done. simpl.
    rewrite -{2}(agree_map_id va).
    eapply agree_map_ext; first by apply _.
    apply oFunctor_map_id.
Qed.
Next Obligation.
  intros K ?? F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x; simpl in *.
  rewrite -view_map_compose.
  apply (view_map_ext _ _ _ _)=> y.
  - rewrite /= -map_fmap_compose.
    apply map_fmap_equiv_ext=>k ??.
    apply oFunctor_map_compose.
  - rewrite /= -map_fmap_compose.
    apply map_fmap_equiv_ext=>k [df va] ?.
    split; first done. simpl.
    rewrite -agree_map_compose.
    eapply agree_map_ext; first by apply _.
    apply oFunctor_map_compose.
Qed.
Next Obligation.
  intros K ?? F A1 ? A2 ? B1 ? B2 ? fg; simpl.
  (* [apply] does not work, probably the usual unification probem (Coq #6294) *)
  apply: view_map_cmra_morphism; [apply _..|]=> n m f.
  intros Hrel k [df va] Hf. move: Hf.
  rewrite !lookup_fmap.
  destruct (f !! k) as [[df' va']|] eqn:Hfk; rewrite Hfk; last done.
  simpl=>[= <- <-].
  specialize (Hrel _ _ Hfk). simpl in Hrel. destruct Hrel as (v & Hagree & Hdval & Hm).
  exists (oFunctor_map F fg v).
  rewrite Hm. split; last by auto.
  rewrite Hagree. rewrite agree_map_to_agree. done.
Qed.

Global Instance gmap_viewURF_contractive (K : Type) `{Countable K} F :
  oFunctorContractive F → urFunctorContractive (gmap_viewURF K F).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg.
  apply viewO_map_ne.
  - apply gmapO_map_ne. apply oFunctor_map_contractive. done.
  - apply gmapO_map_ne. apply prodO_map_ne; first done.
    apply agreeO_map_ne, oFunctor_map_contractive. done.
Qed.

Program Definition gmap_viewRF (K : Type) `{Countable K} (F : oFunctor) : rFunctor := {|
  rFunctor_car A _ B _ := gmap_viewR K (oFunctor_car F A B);
  rFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    viewO_map (rel:=gmap_view_rel K (oFunctor_car F A1 B1))
              (rel':=gmap_view_rel K (oFunctor_car F A2 B2))
              (gmapO_map (K:=K) (oFunctor_map F fg))
              (gmapO_map (K:=K) (prodO_map cid (agreeO_map (oFunctor_map F fg))))
|}.
Solve Obligations with apply gmap_viewURF.

Global Instance gmap_viewRF_contractive (K : Type) `{Countable K} F :
  oFunctorContractive F → rFunctorContractive (gmap_viewRF K F).
Proof. apply gmap_viewURF_contractive. Qed. *)

Global Typeclasses Opaque gmap_view_auth gmap_view_frag.
