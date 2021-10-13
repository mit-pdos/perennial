From Coq.QArith Require Import Qcanon.
From iris.algebra Require Export view gmap frac dfrac gset.
From iris.algebra Require Import local_updates proofmode_classes big_op.
From iris.prelude Require Import options.

(** *

Like gmap_view.v from Iris, except that we parameterize by an additional
step-indexed relation, R. Recall that in gmap_view, at step index n if there is
a fragment k ↦ v, then the auth map m must have m !! k = v' where v is
equivalent to v' at n.  Here, instead, we would merely require that R n v' v
holds.

The idea is that by making R a relation that captures some notion of
"approximation", we allow for the fragments to have an approximate view of the
values associated with keys.

However one limitation of this formulation is that all fragments containing some key k
have to have the same approximation.

*)

(* But do we really want A to have to be countable ? *)
Local Definition gmap_rel_view_fragUR (K : Type) `{Countable K} (V : ofe) : ucmra :=
  gmapUR K (prodR dfracR (agreeR V)).

Record gmap_val_rel (V : ofe) := GValRel {
  gval_rel_holds :> nat → V → V → Prop;
  gval_rel_refl : ∀ n v, gval_rel_holds n v v;
  gval_rel_mono n1 n2 a1 a2 b1 b2 :
    gval_rel_holds n1 a1 b1 →
    a1 ≡{n2}≡ a2 →
    b1 ≡{n2}≡ b2 →
    n2 ≤ n1 →
    gval_rel_holds n2 a2 b2;
}.

Class GvalRelDiscrete {A} (rel : gmap_val_rel A) :=
  gval_rel_discrete n a b : rel 0 a b → rel n a b.

(** View relation. *)
Section rel.
  Context (K : Type) `{Countable K} (V : ofe).
  Context (R: gmap_val_rel V).
  Implicit Types (m : gmap K V) (k : K) (v : V) (n : nat).
  Implicit Types (f : gmap K (dfrac * agree V)).

  Local Definition gmap_rel_view_rel_raw n m f : Prop :=
    map_Forall (λ k dv, ∃ vf vm, dv.2 ≡{n}≡ to_agree vf ∧ ✓ dv.1 ∧ m !! k = Some vm ∧ R n vm vf) f.

  Local Lemma gmap_rel_view_rel_raw_mono n1 n2 m1 m2 f1 f2 :
    gmap_rel_view_rel_raw n1 m1 f1 →
    m1 ≡{n2}≡ m2 →
    f2 ≼{n2} f1 →
    n2 ≤ n1 →
    gmap_rel_view_rel_raw n2 m2 f2.
  Proof.
    intros Hrel Hm Hf Hn k [q va] Hk.
    (* For some reason applying the lemma in [Hf] does not work... *)
    destruct (lookup_includedN n2 f2 f1) as [Hf' _]. specialize (Hf' Hf). clear Hf.
    specialize (Hf' k). rewrite Hk in Hf'.
    apply option_includedN in Hf'.
    destruct Hf' as [[=]|(? & [q' va'] & [= <-] & Hf1 & Hincl)].
    specialize (Hrel _ _ Hf1) as (vf & vm & Hagree & Hdval & Hm1 & HR). simpl in *.
    specialize (Hm k).
    edestruct (dist_Some_inv_l _ _ _ _ Hm Hm1) as (v' & Hm2 & Hv).
    exists vf, v'. rewrite assoc. split; last first.
    { split; first done. eapply gval_rel_mono; eauto. }
    destruct Hincl as [[Heqq Heqva]|[Hinclq Hinclva]%pair_includedN].
    - simpl in *. split.
      + rewrite Heqva. eapply dist_le; last eassumption. done.
      + rewrite <-discrete_iff in Heqq; last by apply _.
        fold_leibniz. subst q'. done.
    - split.
      + etrans; last first.
        { eapply dist_le; last eassumption. done. }
        eapply agree_valid_includedN; last done.
        eapply cmra_validN_le; last eassumption.
        rewrite Hagree. done.
      + rewrite <-cmra_discrete_included_iff in Hinclq.
        eapply cmra_valid_included; done.
  Qed.

  Local Lemma gmap_rel_view_rel_raw_valid n m f :
    gmap_rel_view_rel_raw n m f → ✓{n} f.
  Proof.
    intros Hrel k. destruct (f !! k) as [[q va]|] eqn:Hf; rewrite Hf; last done.
    specialize (Hrel _ _ Hf) as (? & ? & Hagree & Hdval & Hm1). simpl in *.
    split; simpl.
    - apply cmra_discrete_valid_iff. done.
    - rewrite Hagree. done.
  Qed.

  Local Lemma gmap_rel_view_rel_raw_unit n :
    ∃ m, gmap_rel_view_rel_raw n m ε.
  Proof. exists ∅. apply: map_Forall_empty. Qed.

  Local Canonical Structure gmap_rel_view_rel : view_rel (gmapO K V) (gmap_rel_view_fragUR K V) :=
    ViewRel gmap_rel_view_rel_raw gmap_rel_view_rel_raw_mono
            gmap_rel_view_rel_raw_valid gmap_rel_view_rel_raw_unit.

  Local Lemma gmap_rel_view_rel_exists n (f : gmap K (dfrac * agreeR V)) :
    (∃ m, gmap_rel_view_rel n m f) ↔ ✓{n} f.
  Proof.
    split.
    { intros [m Hrel]. eapply gmap_rel_view_rel_raw_valid, Hrel. }
    intros Hf.
    cut (∃ m, gmap_rel_view_rel n m f ∧ ∀ k, f !! k = None → m !! k = None).
    { naive_solver. }
    induction f as [|k [dq ag] f Hk' IH] using map_ind.
    { exists ∅. split; [|done]. apply: map_Forall_empty. }
    move: (Hf k). rewrite lookup_insert=> -[/= ??].
    destruct (to_agree_uninjN n ag) as [v ?]; [done|].
    destruct IH as (m & Hm & Hdom).
    { intros k'. destruct (decide (k = k')) as [->|?]; [by rewrite Hk'|].
      move: (Hf k'). by rewrite lookup_insert_ne. }
    exists (<[k:=v]> m).
    rewrite /gmap_rel_view_rel /= /gmap_rel_view_rel_raw map_Forall_insert //=. split_and!.
    - exists v, v. rewrite lookup_insert. split_and!; eauto. apply gval_rel_refl.
    - eapply map_Forall_impl; [apply Hm|]; simpl.
      intros k' [dq' ag'] (v'&?&?&?). exists v'.
      rewrite lookup_insert_ne; naive_solver.
    - intros k'. rewrite !lookup_insert_None. naive_solver.
  Qed.

  Local Lemma gmap_rel_view_rel_unit n m : gmap_rel_view_rel n m ε.
  Proof. apply: map_Forall_empty. Qed.

  Local Lemma gmap_rel_view_rel_discrete :
    OfeDiscrete V → GvalRelDiscrete R → ViewRelDiscrete gmap_rel_view_rel.
  Proof.
    intros ?? n m f Hrel k [df va] Hk.
    destruct (Hrel _ _ Hk) as (v1 & v2 & Hagree & Hdval & Hm & HR).
    exists v1, v2. split_and!; try by auto.
    - eapply discrete_iff; first by apply _.
      eapply discrete_iff; first by apply _.
      done.
  Qed.
End rel.

Local Existing Instance gmap_rel_view_rel_discrete.

(** [gmap_rel_view] is a notation to give canonical structure search the chance
to infer the right instances (see [auth]). *)
Notation gmap_rel_view K V := (view (@gmap_rel_view_rel_raw K _ _ V)).
Definition gmap_rel_viewO (K : Type) `{Countable K} (V : ofe) R : ofe :=
  viewO (gmap_rel_view_rel K V R).
Definition gmap_rel_viewR (K : Type) `{Countable K} (V : ofe) R : cmra :=
  viewR (gmap_rel_view_rel K V R).
Definition gmap_rel_viewUR (K : Type) `{Countable K} (V : ofe) R : ucmra :=
  viewUR (gmap_rel_view_rel K V R).

Section definitions.
  Context {K : Type} `{Countable K} {V : ofe} (R : gmap_val_rel V).

  Definition gmap_rel_view_auth (q : frac) (m : gmap K V) : gmap_rel_viewR K V R :=
    ●V{#q} m.
  Definition gmap_rel_view_frag (k : K) (dq : dfrac) (v : V) : gmap_rel_viewR K V R :=
    ◯V {[k := (dq, to_agree v)]}.
End definitions.

Section lemmas.
  Context {K : Type} `{Countable K} {V : ofe} {R: gmap_val_rel V}.
  Implicit Types (m : gmap K V) (k : K) (q : Qp) (dq : dfrac) (v : V).

  Global Instance : Params (@gmap_rel_view_auth) 5 := {}.
  Global Instance gmap_rel_view_auth_ne q : NonExpansive (gmap_rel_view_auth (K:=K) (V:=V) R q).
  Proof. solve_proper. Qed.
  Global Instance gmap_rel_view_auth_proper q : Proper ((≡) ==> (≡)) (gmap_rel_view_auth (K:=K) (V:=V) R q).
  Proof. apply ne_proper, _. Qed.

  Global Instance : Params (@gmap_rel_view_frag) 6 := {}.
  Global Instance gmap_rel_view_frag_ne k oq : NonExpansive (gmap_rel_view_frag (V:=V) R k oq).
  Proof. solve_proper. Qed.
  Global Instance gmap_rel_view_frag_proper k oq : Proper ((≡) ==> (≡)) (gmap_rel_view_frag (V:=V) R k oq).
  Proof. apply ne_proper, _. Qed.

  (* Helper lemmas *)
  Local Lemma gmap_rel_view_rel_lookup' n m k dq v :
    gmap_rel_view_rel K V R n m {[k := (dq, to_agree v)]} ↔ ∃ vm, ✓ dq ∧ m !! k = Some vm ∧ R n vm v.
  Proof.
    split.
    - intros Hrel.
      edestruct (Hrel k) as (vf' & vm' & Hagree & Hval & -> & HR).
      { rewrite lookup_singleton. done. }
      simpl in *. apply (inj _) in Hagree. exists vm'. split_and!; auto.
      eapply gval_rel_mono; try eassumption; auto.
    - intros [vm' (Hq&Hlookup&HR)] j [df va].
      destruct (decide (k = j)) as [<-|Hne]; last by rewrite lookup_singleton_ne.
      rewrite lookup_singleton. intros [= <- <-]. simpl.
      exists v, vm'. split_and!; eauto.
  Qed.

  Local Lemma gmap_rel_view_rel_lookup n m k dq v :
    gmap_rel_view_rel K V R n m {[k := (dq, to_agree v)]} ↔ ∃ vm, ✓ dq ∧ m !! k ≡{n}≡ Some vm ∧ R n vm v.
  Proof.
    split.
    - intros (vm&?&Hlookup&?)%gmap_rel_view_rel_lookup'. exists vm; split_and!; eauto.
      rewrite Hlookup; reflexivity.
    - intros [Hval (Hq&(vm' & Hm & Hv')%dist_Some_inv_r'&HR)] j [df va].
      destruct (decide (k = j)) as [<-|Hne]; last by rewrite lookup_singleton_ne.
      rewrite lookup_singleton. intros [= <- <-]. simpl.
      exists v, vm'. split_and!; eauto. eapply gval_rel_mono; try eassumption; eauto.
  Qed.

  (** Composition and validity *)
  Lemma gmap_rel_view_auth_frac_op p q m :
    gmap_rel_view_auth R (p + q) m ≡ gmap_rel_view_auth R p m ⋅ gmap_rel_view_auth R q m.
  Proof. by rewrite /gmap_rel_view_auth -dfrac_op_own view_auth_dfrac_op. Qed.
  Global Instance gmap_rel_view_auth_frac_is_op q q1 q2 m :
    IsOp q q1 q2 → IsOp' (gmap_rel_view_auth R q m) (gmap_rel_view_auth R q1 m) (gmap_rel_view_auth R q2 m).
  Proof. rewrite /gmap_rel_view_auth. apply _. Qed.

  Lemma gmap_rel_view_auth_frac_op_invN n p m1 q m2 :
    ✓{n} (gmap_rel_view_auth R p m1 ⋅ gmap_rel_view_auth R q m2) → m1 ≡{n}≡ m2.
  Proof. apply view_auth_dfrac_op_invN. Qed.
  Lemma gmap_rel_view_auth_frac_op_inv p m1 q m2 :
    ✓ (gmap_rel_view_auth R p m1 ⋅ gmap_rel_view_auth R q m2) → m1 ≡ m2.
  Proof. apply view_auth_dfrac_op_inv. Qed.
  Lemma gmap_rel_view_auth_frac_op_inv_L `{!LeibnizEquiv V} q m1 p m2 :
    ✓ (gmap_rel_view_auth R p m1 ⋅ gmap_rel_view_auth R q m2) → m1 = m2.
  Proof. apply view_auth_dfrac_op_inv_L, _. Qed.

  Lemma gmap_rel_view_auth_frac_valid m q : ✓ gmap_rel_view_auth R q m ↔ (q ≤ 1)%Qp.
  Proof.
    rewrite view_auth_dfrac_valid. intuition eauto using gmap_rel_view_rel_unit.
  Qed.
  Lemma gmap_rel_view_auth_valid m : ✓ gmap_rel_view_auth R 1 m.
  Proof. rewrite gmap_rel_view_auth_frac_valid. done. Qed.

  Lemma gmap_rel_view_auth_frac_op_validN n q1 q2 m1 m2 :
    ✓{n} (gmap_rel_view_auth R q1 m1 ⋅ gmap_rel_view_auth R q2 m2) ↔ ✓ (q1 + q2)%Qp ∧ m1 ≡{n}≡ m2.
  Proof.
    rewrite view_auth_dfrac_op_validN. intuition eauto using gmap_rel_view_rel_unit.
  Qed.
  Lemma gmap_rel_view_auth_frac_op_valid q1 q2 m1 m2 :
    ✓ (gmap_rel_view_auth R q1 m1 ⋅ gmap_rel_view_auth R q2 m2) ↔ (q1 + q2 ≤ 1)%Qp ∧ m1 ≡ m2.
  Proof.
    rewrite view_auth_dfrac_op_valid. intuition eauto using gmap_rel_view_rel_unit.
  Qed.
  Lemma gmap_rel_view_auth_frac_op_valid_L `{!LeibnizEquiv V} q1 q2 m1 m2 :
    ✓ (gmap_rel_view_auth R q1 m1 ⋅ gmap_rel_view_auth R q2 m2) ↔ ✓ (q1 + q2)%Qp ∧ m1 = m2.
  Proof. unfold_leibniz. apply gmap_rel_view_auth_frac_op_valid. Qed.

  Lemma gmap_rel_view_auth_op_validN n m1 m2 :
    ✓{n} (gmap_rel_view_auth R 1 m1 ⋅ gmap_rel_view_auth R 1 m2) ↔ False.
  Proof. apply view_auth_op_validN. Qed.
  Lemma gmap_rel_view_auth_op_valid m1 m2 :
    ✓ (gmap_rel_view_auth R 1 m1 ⋅ gmap_rel_view_auth R 1 m2) ↔ False.
  Proof. apply view_auth_op_valid. Qed.

  Lemma gmap_rel_view_frag_validN n k dq v : ✓{n} gmap_rel_view_frag R k dq v ↔ ✓ dq.
  Proof.
    rewrite view_frag_validN gmap_rel_view_rel_exists singleton_validN pair_validN.
    naive_solver.
  Qed.
  Lemma gmap_rel_view_frag_valid k dq v : ✓ gmap_rel_view_frag R k dq v ↔ ✓ dq.
  Proof.
    rewrite cmra_valid_validN. setoid_rewrite gmap_rel_view_frag_validN.
    naive_solver eauto using O.
  Qed.

  Lemma gmap_rel_view_frag_op k dq1 dq2 v :
    gmap_rel_view_frag R k (dq1 ⋅ dq2) v ≡ gmap_rel_view_frag R k dq1 v ⋅ gmap_rel_view_frag R k dq2 v.
  Proof. rewrite -view_frag_op singleton_op -pair_op agree_idemp //. Qed.
  Lemma gmap_rel_view_frag_add k q1 q2 v :
    gmap_rel_view_frag R k (DfracOwn (q1 + q2)) v ≡
      gmap_rel_view_frag R k (DfracOwn q1) v ⋅ gmap_rel_view_frag R k (DfracOwn q2) v.
  Proof. rewrite -gmap_rel_view_frag_op. done. Qed.

  Lemma gmap_rel_view_frag_op_validN n k dq1 dq2 v1 v2 :
    ✓{n} (gmap_rel_view_frag R k dq1 v1 ⋅ gmap_rel_view_frag R k dq2 v2) ↔
      ✓ (dq1 ⋅ dq2) ∧ v1 ≡{n}≡ v2.
  Proof.
    rewrite view_frag_validN gmap_rel_view_rel_exists singleton_op singleton_validN.
    by rewrite -pair_op pair_validN to_agree_op_validN.
  Qed.
  Lemma gmap_rel_view_frag_op_valid k dq1 dq2 v1 v2 :
    ✓ (gmap_rel_view_frag R k dq1 v1 ⋅ gmap_rel_view_frag R k dq2 v2) ↔ ✓ (dq1 ⋅ dq2) ∧ v1 ≡ v2.
  Proof.
    rewrite view_frag_valid. setoid_rewrite gmap_rel_view_rel_exists.
    rewrite -cmra_valid_validN singleton_op singleton_valid.
    by rewrite -pair_op pair_valid to_agree_op_valid.
  Qed.
  (* FIXME: Having a [valid_L] lemma is not consistent with [auth] and [view]; they
     have [inv_L] lemmas instead that just have an equality on the RHS. *)
  Lemma gmap_rel_view_frag_op_valid_L `{!LeibnizEquiv V} k dq1 dq2 v1 v2 :
    ✓ (gmap_rel_view_frag R k dq1 v1 ⋅ gmap_rel_view_frag R k dq2 v2) ↔ ✓ (dq1 ⋅ dq2) ∧ v1 = v2.
  Proof. unfold_leibniz. apply gmap_rel_view_frag_op_valid. Qed.

  Lemma gmap_rel_view_both_frac_validN' n q m k dq v :
    ✓{n} (gmap_rel_view_auth R q m ⋅ gmap_rel_view_frag R k dq v) ↔
      ∃ vm, (q ≤ 1)%Qp ∧ ✓ dq ∧ m !! k = Some vm ∧ R n vm v.
  Proof.
    rewrite /gmap_rel_view_auth /gmap_rel_view_frag.
    rewrite view_both_dfrac_validN gmap_rel_view_rel_lookup'.
    naive_solver.
  Qed.
  Lemma gmap_rel_view_both_frac_validN n q m k dq v :
    ✓{n} (gmap_rel_view_auth R q m ⋅ gmap_rel_view_frag R k dq v) ↔
      ∃ vm, (q ≤ 1)%Qp ∧ ✓ dq ∧ m !! k ≡{n}≡ Some vm ∧ R n vm v.
  Proof.
    rewrite /gmap_rel_view_auth /gmap_rel_view_frag.
    rewrite view_both_dfrac_validN gmap_rel_view_rel_lookup.
    naive_solver.
  Qed.
  Lemma gmap_rel_view_both_validN' n m k dq v :
    ✓{n} (gmap_rel_view_auth R 1 m ⋅ gmap_rel_view_frag R k dq v) ↔
      ∃ vm, ✓ dq ∧ m !! k = Some vm ∧ R n vm v.
  Proof. rewrite gmap_rel_view_both_frac_validN'. naive_solver done. Qed.
  Lemma gmap_rel_view_both_validN n m k dq v :
    ✓{n} (gmap_rel_view_auth R 1 m ⋅ gmap_rel_view_frag R k dq v) ↔
      ∃ vm, ✓ dq ∧ m !! k ≡{n}≡ Some vm ∧ R n vm v.
  Proof. rewrite gmap_rel_view_both_frac_validN. naive_solver done. Qed.

  Lemma gmap_rel_view_both_frac_valid q m k dq v :
    ✓ (gmap_rel_view_auth R q m ⋅ gmap_rel_view_frag R k dq v) ↔
    ∃ vm, (q ≤ 1)%Qp ∧ ✓ dq ∧ m !! k = Some vm ∧ (∀ n, R n vm v).
  Proof.
    rewrite /gmap_rel_view_auth /gmap_rel_view_frag.
    rewrite view_both_dfrac_valid. setoid_rewrite gmap_rel_view_rel_lookup'.
    split=>[[Hq Hm]|[vm [Hq Hm]]].
    - destruct (Hm 0%nat) as (vm&Hq'&Hlookup&HR).
      exists vm. split_and!; try eauto.
      { intros n. edestruct (Hm n); naive_solver. }
    - split; first done. intros n. exists vm. split.
      + apply Hm.
      + naive_solver.
  Qed.
  Lemma gmap_rel_view_both_frac_valid_L `{!LeibnizEquiv V} q m k dq v :
    ✓ (gmap_rel_view_auth R q m ⋅ gmap_rel_view_frag R k dq v) ↔
    ∃ vm, ✓ q ∧ ✓ dq ∧ m !! k = Some vm ∧ (∀ n, R n vm v).
  Proof.
    rewrite gmap_rel_view_both_frac_valid.
    unfold_leibniz. naive_solver.
  Qed.
  Lemma gmap_rel_view_both_valid m k dq v :
    ✓ (gmap_rel_view_auth R 1 m ⋅ gmap_rel_view_frag R k dq v) ↔
    ∃ vm, ✓ dq ∧ m !! k = Some vm ∧ (∀ n, R n vm v).
  Proof. rewrite gmap_rel_view_both_frac_valid. naive_solver done. Qed.
  (* FIXME: Having a [valid_L] lemma is not consistent with [auth] and [view]; they
     have [inv_L] lemmas instead that just have an equality on the RHS. *)
  Lemma gmap_rel_view_both_valid_L `{!LeibnizEquiv V} m k dq v :
    ✓ (gmap_rel_view_auth R 1 m ⋅ gmap_rel_view_frag R k dq v) ↔
    ∃ vm, ✓ dq ∧ m !! k = Some vm ∧ (∀ n, R n vm v).
  Proof. apply gmap_rel_view_both_valid. Qed.

  (** Frame-preserving updates *)
  Lemma gmap_rel_view_alloc m k dq v :
    m !! k = None →
    ✓ dq →
    gmap_rel_view_auth R 1 m ~~> gmap_rel_view_auth R 1 (<[k := v]> m) ⋅ gmap_rel_view_frag R k dq v.
  Proof.
    intros Hfresh Hdq. apply view_update_alloc=>n bf Hrel j [df va] /=.
    rewrite lookup_op. destruct (decide (j = k)) as [->|Hne].
    - assert (bf !! k = None) as Hbf.
      { destruct (bf !! k) as [[df' va']|] eqn:Hbf; last done.
        specialize (Hrel _ _ Hbf). destruct Hrel as (v' & vm'  & _ & _ & Hm & HR).
        exfalso. rewrite Hm in Hfresh. done. }
      rewrite lookup_singleton Hbf right_id.
      intros [= <- <-]. eexists v, v.
      do 2 (split; first done).
      rewrite lookup_insert. split; first done.
      apply gval_rel_refl.
    - rewrite lookup_singleton_ne; last done.
      rewrite left_id=>Hbf.
      specialize (Hrel _ _ Hbf). destruct Hrel as (v' & vm' & ? & ? & Hm & HR).
      eexists _, vm'. do 2 (split; first done).
      rewrite lookup_insert_ne //.
  Qed.

  Lemma gmap_rel_view_alloc_big m m' dq :
    m' ##ₘ m →
    ✓ dq →
    gmap_rel_view_auth R 1 m ~~>
      gmap_rel_view_auth R 1 (m' ∪ m) ⋅ ([^op map] k↦v ∈ m', gmap_rel_view_frag R k dq v).
  Proof.
    intros. induction m' as [|k v m' ? IH] using map_ind; decompose_map_disjoint.
    { rewrite big_opM_empty left_id_L right_id. done. }
    rewrite IH //.
    rewrite big_opM_insert // assoc.
    apply cmra_update_op; last done.
    rewrite -insert_union_l. apply (gmap_rel_view_alloc _ k dq); last done.
    by apply lookup_union_None.
  Qed.

  Lemma gmap_rel_view_delete m k v :
    gmap_rel_view_auth R 1 m ⋅ gmap_rel_view_frag R k (DfracOwn 1) v ~~>
    gmap_rel_view_auth R 1 (delete k m).
  Proof.
    apply view_update_dealloc=>n bf Hrel j [df va] Hbf /=.
    destruct (decide (j = k)) as [->|Hne].
    - edestruct (Hrel k) as (vf' & vm' & _ & Hdf & _ & HR).
      { rewrite lookup_op Hbf lookup_singleton -Some_op. done. }
      exfalso. apply: dfrac_full_exclusive. apply Hdf.
    - edestruct (Hrel j) as (vf' & vm' & ? & ? & Hm & HR).
      { rewrite lookup_op lookup_singleton_ne // Hbf. done. }
      exists vf', vm'. do 2 (split; first done).
      rewrite lookup_delete_ne //.
  Qed.

  Lemma gmap_rel_view_delete_big m m' :
    gmap_rel_view_auth R 1 m ⋅ ([^op map] k↦v ∈ m', gmap_rel_view_frag R k (DfracOwn 1) v) ~~>
    gmap_rel_view_auth R 1 (m ∖ m').
  Proof.
    induction m' as [|k v m' ? IH] using map_ind.
    { rewrite right_id_L big_opM_empty right_id //. }
    rewrite big_opM_insert //.
    rewrite [gmap_rel_view_frag R _ _ _ ⋅ _]comm assoc IH gmap_rel_view_delete.
    rewrite -delete_difference. done.
  Qed.

  Lemma gmap_rel_view_update m k v v' :
    gmap_rel_view_auth R 1 m ⋅ gmap_rel_view_frag R k (DfracOwn 1) v ~~>
      gmap_rel_view_auth R 1 (<[k := v']> m) ⋅ gmap_rel_view_frag R k (DfracOwn 1) v'.
  Proof.
    rewrite gmap_rel_view_delete.
    rewrite (gmap_rel_view_alloc _ k (DfracOwn 1) v') //; last by rewrite lookup_delete.
    rewrite insert_delete_insert //.
  Qed.

  Lemma gmap_rel_view_update_big m m0 m1 :
    dom (gset K) m0 = dom (gset K) m1 →
    gmap_rel_view_auth R 1 m ⋅ ([^op map] k↦v ∈ m0, gmap_rel_view_frag R k (DfracOwn 1) v) ~~>
      gmap_rel_view_auth R 1 (m1 ∪ m) ⋅ ([^op map] k↦v ∈ m1, gmap_rel_view_frag R k (DfracOwn 1) v).
  Proof.
    intros Hdom%eq_sym. revert m1 Hdom.
    induction m0 as [|k v m0 Hnotdom IH] using map_ind; intros m1 Hdom.
    { rewrite dom_empty_L in Hdom.
      apply dom_empty_iff_L in Hdom as ->.
      rewrite left_id_L big_opM_empty. done. }
    rewrite dom_insert_L in Hdom.
    assert (k ∈ dom (gset K) m1) as Hindom by set_solver.
    apply elem_of_dom in Hindom as [v' Hlookup].
    rewrite big_opM_insert //.
    rewrite [gmap_rel_view_frag R _ _ _ ⋅ _]comm assoc.
    rewrite (IH (delete k m1)); last first.
    { rewrite dom_delete_L Hdom.
      apply not_elem_of_dom in Hnotdom. set_solver -Hdom. }
    rewrite -assoc [_ ⋅ gmap_rel_view_frag R _ _ _]comm assoc.
    rewrite (gmap_rel_view_update _ _ _ v').
    rewrite (big_opM_delete _ m1 k v') // -assoc.
    rewrite insert_union_r; last by rewrite lookup_delete.
    rewrite union_delete_insert //.
  Qed.

  Lemma gmap_rel_view_persist k dq v :
    gmap_rel_view_frag R k dq v ~~> gmap_rel_view_frag R k DfracDiscarded v.
  Proof.
    apply view_update_frag=>m n bf Hrel j [df va] /=.
    rewrite lookup_op. destruct (decide (j = k)) as [->|Hne].
    - rewrite lookup_singleton.
      edestruct (Hrel k ((dq, to_agree v) ⋅? bf !! k)) as (vf' & vm' & Hdf & Hva & Hm & HR).
      { rewrite lookup_op lookup_singleton.
        destruct (bf !! k) eqn:Hbf; by rewrite Hbf. }
      rewrite Some_op_opM. intros [= Hbf].
      exists vf', vm'. rewrite assoc; split; last done.
      destruct (bf !! k) as [[df' va']|] eqn:Hbfk; rewrite Hbfk in Hbf; clear Hbfk.
      + simpl in *. rewrite -pair_op in Hbf.
        move:Hbf=>[= <- <-]. split; first done.
        eapply cmra_discrete_valid.
        eapply (dfrac_discard_update _ _ (Some df')).
        apply cmra_discrete_valid_iff. done.
      + simpl in *. move:Hbf=>[= <- <-]. split; done.
    - rewrite lookup_singleton_ne //.
      rewrite left_id=>Hbf.
      edestruct (Hrel j) as (vf'' & vm'' & ? & ? & Hm & HR).
      { rewrite lookup_op lookup_singleton_ne // left_id. done. }
      simpl in *. eexists _, _. do 2 (split; first done). done.
  Qed.

  (** Typeclass instances *)
  Global Instance gmap_rel_view_frag_core_id k dq v : CoreId dq → CoreId (gmap_rel_view_frag R k dq v).
  Proof. apply _. Qed.

  Global Instance gmap_rel_view_cmra_discrete :
    OfeDiscrete V → GvalRelDiscrete R → CmraDiscrete (gmap_rel_viewR K V R).
  Proof. apply _. Qed.

  Global Instance gmap_rel_view_frag_mut_is_op dq dq1 dq2 k v :
    IsOp dq dq1 dq2 →
    IsOp' (gmap_rel_view_frag R k dq v) (gmap_rel_view_frag R k dq1 v) (gmap_rel_view_frag R k dq2 v).
  Proof. rewrite /IsOp' /IsOp => ->. apply gmap_rel_view_frag_op. Qed.
End lemmas.

Typeclasses Opaque gmap_rel_view_auth gmap_rel_view_frag.
