From Coq.QArith Require Import Qcanon.
From iris.algebra Require Export view gmap frac dfrac gset.
From iris.algebra Require Import local_updates proofmode_classes big_op.
From iris.prelude Require Import options.

(** *

Like gmap_view.v from Iris, except that fragments might only "approximate" the
authoritative copy of a value.

More precisely, recall that in gmap_view, at step index n if there is a fragment
k ↦ v, then the auth map m must have m !! k = v' where v is equivalent to v' at
n. In this library, we instead further parameterize things by a step-indexed
relation R, and we allow fragments to not just have the key value, but
auxilliary information a, so that a fragment can be thought of as points-tos of the form
k ↦ (v, a). The existence of such a fragment at step index n implies that there
exists some vm such that m !! k = vm and the relation R n vm v a.

Ownership of k can be fractional so we might have that k ↦{q1} (v1, a1) and k
↦{q2} (v2, a2), in which case we can conclude the usual restrictions on q1 and
q2 summing up to <= 1, v1 = v2, and that there must be some vm such that R n vm
v1 a1 and R n vm v2 a2 for all n. This allows us to enforce that the auxilliary
information a1 and a2 have to be "coherent" in some sense.

The intended use case is to model the status of an asynchronous disk, where with
k ↦ (b, bs), b would be the current block contents of k, and bs would be a set of
block contents that could be there after a crash.

*)

Local Definition gmap_rel_view_fragUR (K : Type) `{Countable K} (VA : Type) (V: ofe) (A: Type)
      `{Countable A} : ucmra :=
  gmapUR K (prodR dfracR (prodR (agreeR V) (gsetR A))).

Record gmap_val_rel (VA: ofe) (V : ofe) (A : Type) := GValRel {
  gval_rel_holds :> nat → VA → V → A → Prop;
  gval_rel_mono n1 n2 va1 va2 v1 v2 a :
    gval_rel_holds n1 va1 v1 a →
    va1 ≡{n2}≡ va2 →
    v1 ≡{n2}≡ v2 →
    n2 ≤ n1 →
    gval_rel_holds n2 va2 v2 a;
}.

Class GvalRelDiscrete {VA} V A (rel : gmap_val_rel VA V A) :=
  gval_rel_discrete n va v a : rel 0 va v a → rel n va v a.

(** View relation. *)
Section rel.
  Context (K : Type) `{Countable K} (VA : ofe) (V : ofe) (A : Type) `{Countable A}.
  Context (R: gmap_val_rel VA V A).
  Implicit Types (m : gmap K VA) (k : K) (va : VA) (aset : gset A) (v : V) (n : nat).
  Implicit Types (f : gmap K (dfrac * (agree V * gset A))).

  Local Definition gmap_rel_view_rel_raw n m f : Prop :=
    map_Forall (λ k dv, ∃ vf aset vm, dv.2 ≡{n}≡ (to_agree vf, aset) ∧
                                      ✓ dv.1 ∧
                                      m !! k = Some vm ∧
                                      (∀ a, a ∈ aset → R n vm vf a)) f.

  Local Lemma gmap_rel_view_rel_raw_mono n1 n2 m1 m2 f1 f2 :
    gmap_rel_view_rel_raw n1 m1 f1 →
    m1 ≡{n2}≡ m2 →
    f2 ≼{n2} f1 →
    n2 ≤ n1 →
    gmap_rel_view_rel_raw n2 m2 f2.
  Proof.
    intros Hrel Hm Hf Hn k [q [v aset]] Hk.
    (* For some reason applying the lemma in [Hf] does not work... *)
    destruct (lookup_includedN n2 f2 f1) as [Hf' _]. specialize (Hf' Hf). clear Hf.
    specialize (Hf' k). rewrite Hk in Hf'.
    apply option_includedN in Hf'.
    destruct Hf' as [[=]|(? & [q' [v' aset']] & [= <-] & Hf1 & Hincl)].
    specialize (Hrel _ _ Hf1) as (vf & asetf & vm & (Hagree & Haset) & Hdval & Hm1 & HR). simpl in *.
    specialize (Hm k).
    edestruct (dist_Some_inv_l _ _ _ _ Hm Hm1) as (vm' & Hm2 & Hv).
    assert (Hsub: aset ⊆ aset').
    {
      apply gset_included.
      destruct Hincl as [[Heqq [Heqv Heqaset]]|[Hinclq [Hinclv Hinclaset]%pair_includedN]%pair_includedN].
      { simpl in Heqaset. rewrite Heqaset. reflexivity. }
      { eauto. }
    }
    apply leibniz_equiv_iff in Haset. subst.
    exists vf, aset, vm'. rewrite assoc. split; last first.
    { split; first done. intros a Hin. eapply gval_rel_mono; eauto. }
    destruct Hincl as [[Heqq [Heqv Heqaset]]|[Hinclq [Hinclv Hinclaset]%pair_includedN]%pair_includedN].
    - simpl in *. split.
      + rewrite Heqv. eapply dist_le; last eassumption. done.
      + rewrite <-discrete_iff in Heqq; last by apply _.
        fold_leibniz. subst q'. done.
    - split.
      + f_equiv. etrans; last first.
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
    specialize (Hrel _ _ Hf) as (? & ? & ? & Hagree & Hdval & Hm1). simpl in *.
    split; simpl.
    - apply cmra_discrete_valid_iff. done.
    - rewrite Hagree. done.
  Qed.

  Local Lemma gmap_rel_view_rel_raw_unit n :
    ∃ m, gmap_rel_view_rel_raw n m ε.
  Proof. exists ∅. apply: map_Forall_empty. Qed.

  Local Canonical Structure gmap_rel_view_rel : view_rel (gmapO K VA) (gmap_rel_view_fragUR K VA V A) :=
    ViewRel gmap_rel_view_rel_raw gmap_rel_view_rel_raw_mono
            gmap_rel_view_rel_raw_valid gmap_rel_view_rel_raw_unit.

  Local Lemma gmap_rel_view_rel_exists_l1 n (f : gmap K (dfrac * (agreeR V * gset A))) :
    (∃ m, gmap_rel_view_rel n m f) → ✓{n} f.
  Proof.
    { intros [m Hrel]. eapply gmap_rel_view_rel_raw_valid, Hrel. }
  Qed.

  Local Lemma gmap_rel_view_rel_exists_l n (f : gmap K (dfrac * (agreeR V * gset A))) :
    (∃ m, gmap_rel_view_rel n m f) →
    ✓{n} f ∧
    (∀ k q v aset, f !! k ≡{n}≡ Some (q, (to_agree v, aset)) →
                   ∃ vm, ∀ a, a ∈ aset → R n vm v a).
  Proof.
    intros Hm. split; first by apply gmap_rel_view_rel_exists_l1.
    destruct Hm as [m Hrel]. intros k q v aset Hf.
    apply dist_Some_inv_r' in Hf as (x&Hflookup&Heq).
    edestruct (Hrel k) as (v'&aset'&vm'&Heq'&Hval&Hlookup&HR); first eassumption.
    exists vm'. intros.
    destruct x as [? [ag aset'']].
    simpl in Heq'.
    destruct Heq as [Heqa Heqb]. simpl in Heqb.
    revert Heq'. rewrite -Heqb. destruct 1 as (Heqag&Heq). simpl in Heq.
    apply leibniz_equiv_iff in Heq. subst. 
    eapply gval_rel_mono; first eauto; eauto.
    simpl in Heqag.
    eapply (inj _) in Heqag.
    auto.
  Qed.

  Local Lemma gmap_rel_view_rel_exists n (f : gmap K (dfrac * (agreeR V * gset A))) :
    (∀ k q v aset, f !! k ≡{n}≡ Some (q, (to_agree v, aset)) → ∃ vm, ∀ a, a ∈ aset → R n vm v a) →
    (∃ m, gmap_rel_view_rel n m f) ↔ ✓{n} f.
  Proof.
    intros Hspec.
    split; first apply gmap_rel_view_rel_exists_l1.
    intros Hf.
    cut (∃ m, gmap_rel_view_rel n m f ∧ ∀ k, f !! k = None → m !! k = None).
    { naive_solver. }
    induction f as [|k [dq [ag aset]] f Hk' IH] using map_ind.
    { exists ∅. split; [|done]. apply: map_Forall_empty. }
    move: (Hf k). rewrite lookup_insert=> -[/= ?[??]].
    destruct (to_agree_uninjN n ag) as [v ?]; [done|].
    destruct IH as (m & Hm & Hdom).
    { intros k'. destruct (decide (k = k')) as [->|?]; [rewrite Hk'|].
      * intros ???. inversion 1.
      * intros. eapply Hspec; eauto.
        rewrite lookup_insert_ne; eauto. }
    { intros k'. destruct (decide (k = k')) as [->|?]; [by rewrite Hk'|].
      move: (Hf k'). rewrite lookup_insert_ne //. }
    edestruct (Hspec k) as (va&Hva).
    { rewrite lookup_insert //. repeat f_equiv; eauto. symmetry. eauto. }
    exists (<[k:=va]> m).
    rewrite /gmap_rel_view_rel /= /gmap_rel_view_rel_raw map_Forall_insert //=. split_and!.
    - exists v, aset, va. rewrite lookup_insert. split_and!; eauto. f_equiv; eauto.
    - eapply map_Forall_impl; [apply Hm|]; simpl.
      intros k' [dq' ag'] (v'&?&?&?). exists v'.
      rewrite lookup_insert_ne; naive_solver.
    - intros k'. rewrite !lookup_insert_None. naive_solver.
  Qed.

  Local Lemma gmap_rel_view_rel_unit n m : gmap_rel_view_rel n m ε.
  Proof. apply: map_Forall_empty. Qed.

  Local Lemma gmap_rel_view_rel_discrete :
    OfeDiscrete V → GvalRelDiscrete V A R → ViewRelDiscrete gmap_rel_view_rel.
  Proof.
    intros ?? n m f Hrel k [df va] Hk.
    destruct (Hrel _ _ Hk) as (v1 & aset & v2 & Hagree & Hdval & Hm & HR).
    exists v1, aset, v2. split_and!; try by auto.
    - eapply discrete_iff; first by apply _.
      eapply discrete_iff; first by apply _.
      done.
  Qed.
End rel.

Local Existing Instance gmap_rel_view_rel_discrete.

(** [gmap_rel_view] is a notation to give canonical structure search the chance
to infer the right instances (see [auth]). *)
Notation gmap_rel_view K V := (view (@gmap_rel_view_rel_raw K _ _ V)).
Definition gmap_rel_viewO (K : Type) `{Countable K} VA (V : ofe) A `{Countable A} R : ofe :=
  viewO (gmap_rel_view_rel K VA V A R).
Definition gmap_rel_viewR (K : Type) `{Countable K} VA (V : ofe) A `{Countable A} R : cmra :=
  viewR (gmap_rel_view_rel K VA V A R).
Definition gmap_rel_viewUR (K : Type) `{Countable K} VA (V : ofe) A `{Countable A} R : ucmra :=
  viewUR (gmap_rel_view_rel K VA V A R).

Section definitions.
  Context {K : Type} `{Countable K} {VA} {V : ofe} {A} `{Countable A} (R : gmap_val_rel VA V A).

  Definition gmap_rel_view_auth (q : frac) (m : gmap K VA) : gmap_rel_viewR K VA V A R :=
    ●V{#q} m.
  Definition gmap_rel_view_frag (k : K) (dq : dfrac) (a : A) (v : V) : gmap_rel_viewR K VA V A R :=
    ◯V {[k := (dq, (to_agree v, {[a]}))]}.
End definitions.

Section lemmas.
  Context {K : Type} `{Countable K} {VA} {V : ofe} {A} `{Countable A} (R : gmap_val_rel VA V A).
  Implicit Types (m : gmap K VA) (k : K) (q : Qp) (dq : dfrac) (va : VA) (v : V) (a : A).

  Global Instance : Params (@gmap_rel_view_auth) 5 := {}.
  Global Instance gmap_rel_view_auth_ne q : NonExpansive (gmap_rel_view_auth (K:=K) (VA:=VA) (V:=V) R q).
  Proof. solve_proper. Qed.
  Global Instance gmap_rel_view_auth_proper q :
    Proper ((≡) ==> (≡)) (gmap_rel_view_auth (K:=K) (VA:=VA) (V:=V) R q).
  Proof. apply ne_proper, _. Qed.

  Global Instance : Params (@gmap_rel_view_frag) 6 := {}.
  Global Instance gmap_rel_view_frag_ne k oq a :
    NonExpansive (gmap_rel_view_frag (VA:=VA) (V:=V) (A:=A) R k oq a).
  Proof. solve_proper. Qed.
  Global Instance gmap_rel_view_frag_proper k oq a :
    Proper ((≡) ==> (≡)) (gmap_rel_view_frag (V:=V) R k oq a).
  Proof. apply ne_proper, _. Qed.

  (* Helper lemmas *)
  Local Lemma gmap_rel_view_rel_lookup' n m k dq v a :
    gmap_rel_view_rel K VA V A R n m {[k := (dq, (to_agree v, {[a]}))]} ↔
                      ∃ vm, ✓ dq ∧ m !! k = Some vm ∧ R n vm v a.
  Proof.
    split.
    - intros Hrel.
      edestruct (Hrel k) as (vf' & aset' & vm' & [Hagree Heq] & Hval & -> & HR).
      { rewrite lookup_singleton. done. }
      simpl in *. apply (inj _) in Hagree. exists vm'. split_and!; auto.
      eapply gval_rel_mono; try eassumption; auto.
      apply leibniz_equiv_iff in Heq.
      symmetry in Hagree. eapply gval_rel_mono; try eassumption; eauto.
      apply HR. set_solver.
    - intros [vm' (Hq&Hlookup&HR)] j [df [v' aset]].
      destruct (decide (k = j)) as [<-|Hne]; last by rewrite lookup_singleton_ne.
      rewrite lookup_singleton. intros [= <- <-]. simpl.
      exists v, aset, vm'. split_and!; eauto.
      intros a' Hin.
      assert (a' = a) as -> by set_solver.
      eauto.
  Qed.

  Local Lemma gmap_rel_view_rel_lookup n m k dq v a :
    gmap_rel_view_rel K VA V A R n m {[k := (dq, (to_agree v, {[a]}))]} ↔
                      ∃ vm, ✓ dq ∧ m !! k ≡{n}≡ Some vm ∧ R n vm v a.
  Proof.
    split.
    - intros (vm&?&Hlookup&?)%gmap_rel_view_rel_lookup'. exists vm; split_and!; eauto.
      rewrite Hlookup; reflexivity.
    - intros [va (Hq&(vm' & Hm & Hv')%dist_Some_inv_r'&HR)] j [df [v' aset']].
      destruct (decide (k = j)) as [<-|Hne]; last by rewrite lookup_singleton_ne.
      rewrite lookup_singleton. intros [= <- <-]. simpl.
      exists v, aset', vm'. split_and!; eauto. intros a' Hin.
      eapply gval_rel_mono; try eassumption; eauto.
      assert (a' = a) as -> by set_solver. auto.
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
  Lemma gmap_rel_view_auth_frac_op_inv_L `{!LeibnizEquiv VA} q m1 p m2 :
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
  Lemma gmap_rel_view_auth_frac_op_valid_L `{!LeibnizEquiv VA} q1 q2 m1 m2 :
    ✓ (gmap_rel_view_auth R q1 m1 ⋅ gmap_rel_view_auth R q2 m2) ↔ ✓ (q1 + q2)%Qp ∧ m1 = m2.
  Proof. unfold_leibniz. apply gmap_rel_view_auth_frac_op_valid. Qed.

  Lemma gmap_rel_view_auth_op_validN n m1 m2 :
    ✓{n} (gmap_rel_view_auth R 1 m1 ⋅ gmap_rel_view_auth R 1 m2) ↔ False.
  Proof. apply view_auth_op_validN. Qed.
  Lemma gmap_rel_view_auth_op_valid m1 m2 :
    ✓ (gmap_rel_view_auth R 1 m1 ⋅ gmap_rel_view_auth R 1 m2) ↔ False.
  Proof. apply view_auth_op_valid. Qed.

  Lemma gmap_rel_view_frag_validN1 n k dq a v :
    ✓{n} gmap_rel_view_frag R k dq a v → ✓ dq.
  Proof.
    rewrite view_frag_validN. intros Hval%gmap_rel_view_rel_exists_l1. revert Hval.
    { rewrite singleton_validN ?pair_validN. naive_solver. }
  Qed.

  Lemma gmap_rel_view_frag_validN n k dq a v :
    (∃ vm, R n vm v a) →
    ✓{n} gmap_rel_view_frag R k dq a v ↔ ✓ dq.
  Proof.
    intros HR.
    rewrite view_frag_validN gmap_rel_view_rel_exists.
    { rewrite singleton_validN ?pair_validN. naive_solver. }
    intros k' q' v' aset' Hlookup. destruct HR as (vm&HR). exists vm. intros a' Hin.
    apply dist_Some_inv_r' in Hlookup as (?&Heq1&Heq2).
    revert Heq1. rewrite lookup_singleton_Some. intros (->&<-).
    destruct Heq2 as [? [Hag Hset]].
    simpl in Hag, Hset. apply leibniz_equiv_iff in Hset. subst.
    assert (a' = a) as -> by set_solver.
    apply (inj _) in Hag. eapply gval_rel_mono; first eassumption; eauto.
  Qed.

  Lemma gmap_rel_view_frag_valid k dq a v :
    (∀ n, ∃ vm, R n vm v a) →
    ✓ gmap_rel_view_frag R k dq a v ↔ ✓ dq.
  Proof.
    intros Hwit.
    rewrite cmra_valid_validN. split.
    - intros. unshelve (eapply gmap_rel_view_frag_validN; eauto); exact O.
    - intros. eapply gmap_rel_view_frag_validN; eauto.
  Qed.

  Lemma gmap_rel_view_frag_op k dq1 dq2 a v :
    gmap_rel_view_frag R k (dq1 ⋅ dq2) a v ≡ gmap_rel_view_frag R k dq1 a v ⋅ gmap_rel_view_frag R k dq2 a v.
  Proof.
    rewrite -view_frag_op singleton_op -?pair_op agree_idemp // gset_op union_idemp //.
  Qed.
  Lemma gmap_rel_view_frag_add k q1 q2 a v :
    gmap_rel_view_frag R k (DfracOwn (q1 + q2)) a v ≡
      gmap_rel_view_frag R k (DfracOwn q1) a v ⋅ gmap_rel_view_frag R k (DfracOwn q2) a v.
  Proof. rewrite -gmap_rel_view_frag_op. done. Qed.

  Lemma gmap_rel_view_frag_op_validN_l1 n k dq1 dq2 a1 a2 v1 v2 :
    ✓{n} (gmap_rel_view_frag R k dq1 a1 v1 ⋅ gmap_rel_view_frag R k dq2 a2 v2) →
      ✓ (dq1 ⋅ dq2) ∧ v1 ≡{n}≡ v2.
  Proof.
    rewrite view_frag_validN.
    intros Hrel%gmap_rel_view_rel_exists_l1.
    revert Hrel. rewrite singleton_op singleton_validN.
    rewrite -?pair_op ?pair_validN to_agree_op_validN //.
    set_solver.
  Qed.

  Lemma gmap_rel_view_frag_op_validN_l n k dq1 dq2 a1 a2 v1 v2 :
    ✓{n} (gmap_rel_view_frag R k dq1 a1 v1 ⋅ gmap_rel_view_frag R k dq2 a2 v2) →
      ✓ (dq1 ⋅ dq2) ∧ v1 ≡{n}≡ v2 ∧ ∃ vm, R n vm v1 a1 ∧ R n vm v1 a2.
  Proof.
    intros Hr. edestruct (gmap_rel_view_frag_op_validN_l1) as (Hq1&Heq); eauto.
    split_and!; auto.
    revert Hr. rewrite /gmap_rel_view_frag.
    rewrite -view_frag_op singleton_op -?pair_op gset_op.
    assert (to_agree v1 ≡{n}≡ to_agree v2) as <-; auto.
    { by f_equiv. }
    rewrite agree_idemp view_frag_validN. intros (?&Hm)%gmap_rel_view_rel_exists_l.
    edestruct (Hm k) as (vm&Hm').
    { rewrite lookup_insert. reflexivity. }
    exists vm. split; eapply Hm'; set_solver.
  Qed.

  Lemma gmap_rel_view_frag_op_validN n k dq1 dq2 a1 a2 v1 v2 :
    ✓{n} (gmap_rel_view_frag R k dq1 a1 v1 ⋅ gmap_rel_view_frag R k dq2 a2 v2) ↔
      ✓ (dq1 ⋅ dq2) ∧ v1 ≡{n}≡ v2 ∧ (∃ vm, R n vm v1 a1 ∧ R n vm v1 a2).
  Proof.
    split; first by (apply gmap_rel_view_frag_op_validN_l).
    intros [Hqval [Hvequiv Hexm]].
    rewrite view_frag_validN gmap_rel_view_rel_exists; last first.
    { intros k' q' v' aset'. simpl.
      rewrite singleton_op -?pair_op => Hlookup.
      symmetry in Hlookup. eapply dist_Some_inv_l in Hlookup as (z&Heq1&Heq2); eauto.
      apply lookup_singleton_Some in Heq1 as [? ?]. subst.
      destruct Hexm as (vm&HR1&HR2).
      exists vm. intros a Hin.
      destruct Heq2 as [_ [Hvagree Haset]].
      simpl in Haset. apply leibniz_equiv_iff in Haset. rewrite Haset in Hin. set_unfold in Hin.
      simpl in Hvagree.
      assert (v' ≡{n}≡ v1).
      { symmetry. apply to_agree_includedN. exists (to_agree v2). auto. }
      destruct Hin as [ -> | -> ]; eauto using gval_rel_mono.
    }
    rewrite singleton_op singleton_validN -?pair_op ?pair_validN to_agree_op_validN. naive_solver.
  Qed.

  Lemma gmap_rel_view_frag_op_valid_l k dq1 dq2 a1 a2 v1 v2 :
    ✓ (gmap_rel_view_frag R k dq1 a1 v1 ⋅ gmap_rel_view_frag R k dq2 a2 v2) →
      ✓ (dq1 ⋅ dq2) ∧ v1 ≡ v2 ∧ (∀ n, ∃ vm, R n vm v1 a1 ∧ R n vm v1 a2).
  Proof.
    intros Hrel.
    split_and!.
    - revert Hrel. rewrite cmra_valid_validN. intros Hrel.
      specialize (Hrel O). edestruct (gmap_rel_view_frag_op_validN_l); naive_solver. 
    - revert Hrel. rewrite cmra_valid_validN. intros Hrel.
      apply equiv_dist => n.
      specialize (Hrel n). edestruct (gmap_rel_view_frag_op_validN_l); naive_solver.
    - intros n. revert Hrel. rewrite cmra_valid_validN. intros Hrel.
      specialize (Hrel n). edestruct (gmap_rel_view_frag_op_validN_l); naive_solver.
  Qed.

  Lemma gmap_rel_view_frag_op_valid k dq1 dq2 a1 a2 v1 v2 :
    ✓ (gmap_rel_view_frag R k dq1 a1 v1 ⋅ gmap_rel_view_frag R k dq2 a2 v2) ↔
      ✓ (dq1 ⋅ dq2) ∧ v1 ≡ v2 ∧ (∀ n, ∃ vm, R n vm v1 a1 ∧ R n vm v1 a2).
  Proof.
    split; first eapply gmap_rel_view_frag_op_valid_l.
    intros [Hqval [Hvequiv Hexm]].
    rewrite cmra_valid_validN. intros n.
    apply gmap_rel_view_frag_op_validN. split_and!; auto.
  Qed.

  (* FIXME: Having a [valid_L] lemma is not consistent with [auth] and [view]; they
     have [inv_L] lemmas instead that just have an equality on the RHS. *)
  Lemma gmap_rel_view_frag_op_valid_L `{!LeibnizEquiv V} k dq1 dq2 a1 a2 v1 v2 :
    ✓ (gmap_rel_view_frag R k dq1 a1 v1 ⋅ gmap_rel_view_frag R k dq2 a2 v2) ↔
    ✓ (dq1 ⋅ dq2) ∧ v1 = v2 ∧ (∀ n, ∃ vm, R n vm v1 a1 ∧ R n vm v1 a2).
  Proof. unfold_leibniz. apply gmap_rel_view_frag_op_valid. Qed.

  Lemma gmap_rel_view_both_frac_validN' n q m k dq a v :
    ✓{n} (gmap_rel_view_auth R q m ⋅ gmap_rel_view_frag R k dq a v) ↔
      ∃ vm, (q ≤ 1)%Qp ∧ ✓ dq ∧ m !! k = Some vm ∧ R n vm v a.
  Proof.
    rewrite /gmap_rel_view_auth /gmap_rel_view_frag.
    rewrite view_both_dfrac_validN gmap_rel_view_rel_lookup'.
    naive_solver.
  Qed.
  Lemma gmap_rel_view_both_frac_validN n q m k dq a v :
    ✓{n} (gmap_rel_view_auth R q m ⋅ gmap_rel_view_frag R k dq a v) ↔
      ∃ vm, (q ≤ 1)%Qp ∧ ✓ dq ∧ m !! k ≡{n}≡ Some vm ∧ R n vm v a.
  Proof.
    rewrite /gmap_rel_view_auth /gmap_rel_view_frag.
    rewrite view_both_dfrac_validN gmap_rel_view_rel_lookup.
    naive_solver.
  Qed.
  Lemma gmap_rel_view_both_validN' n m k dq a v :
    ✓{n} (gmap_rel_view_auth R 1 m ⋅ gmap_rel_view_frag R k dq a v) ↔
      ∃ vm, ✓ dq ∧ m !! k = Some vm ∧ R n vm v a.
  Proof. rewrite gmap_rel_view_both_frac_validN'. naive_solver done. Qed.
  Lemma gmap_rel_view_both_validN n m k dq a v :
    ✓{n} (gmap_rel_view_auth R 1 m ⋅ gmap_rel_view_frag R k dq a v) ↔
      ∃ vm, ✓ dq ∧ m !! k ≡{n}≡ Some vm ∧ R n vm v a.
  Proof. rewrite gmap_rel_view_both_frac_validN. naive_solver done. Qed.

  Lemma gmap_rel_view_both_frac_valid q m k dq a v :
    ✓ (gmap_rel_view_auth R q m ⋅ gmap_rel_view_frag R k dq a v) ↔
    ∃ vm, (q ≤ 1)%Qp ∧ ✓ dq ∧ m !! k = Some vm ∧ (∀ n, R n vm v a).
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
  Lemma gmap_rel_view_both_frac_valid_L `{!LeibnizEquiv V} q m k dq a v :
    ✓ (gmap_rel_view_auth R q m ⋅ gmap_rel_view_frag R k dq a v) ↔
    ∃ vm, ✓ q ∧ ✓ dq ∧ m !! k = Some vm ∧ (∀ n, R n vm v a).
  Proof.
    rewrite gmap_rel_view_both_frac_valid.
    unfold_leibniz. naive_solver.
  Qed.
  Lemma gmap_rel_view_both_valid m k dq a v :
    ✓ (gmap_rel_view_auth R 1 m ⋅ gmap_rel_view_frag R k dq a v) ↔
    ∃ vm, ✓ dq ∧ m !! k = Some vm ∧ (∀ n, R n vm v a).
  Proof. rewrite gmap_rel_view_both_frac_valid. naive_solver done. Qed.
  (* FIXME: Having a [valid_L] lemma is not consistent with [auth] and [view]; they
     have [inv_L] lemmas instead that just have an equality on the RHS. *)
  Lemma gmap_rel_view_both_valid_L `{!LeibnizEquiv V} m k dq a v :
    ✓ (gmap_rel_view_auth R 1 m ⋅ gmap_rel_view_frag R k dq a v) ↔
    ∃ vm, ✓ dq ∧ m !! k = Some vm ∧ (∀ n, R n vm v a).
  Proof. apply gmap_rel_view_both_valid. Qed.

  (** Frame-preserving updates *)
  Lemma gmap_rel_view_alloc m k dq vm a v :
    (∀ n, R n vm v a) →
    m !! k = None →
    ✓ dq →
    gmap_rel_view_auth R 1 m ~~> gmap_rel_view_auth R 1 (<[k := vm]> m) ⋅ gmap_rel_view_frag R k dq a v.
  Proof.
    intros HRnew Hfresh Hdq. apply view_update_alloc=>n bf Hrel j [df va] /=.
    rewrite lookup_op. destruct (decide (j = k)) as [->|Hne].
    - assert (bf !! k = None) as Hbf.
      { destruct (bf !! k) as [[df' va']|] eqn:Hbf; last done.
        specialize (Hrel _ _ Hbf). destruct Hrel as (v' & aset & vm' & _ & _ & Hm & HR).
        exfalso. rewrite Hm in Hfresh. done. }
      rewrite lookup_singleton Hbf right_id.
      intros [= <- <-]. eexists v, {[a]}, vm.
      do 2 (split; first done).
      rewrite lookup_insert. split; first done.
      set_unfold; naive_solver.
    - rewrite lookup_singleton_ne; last done.
      rewrite left_id=>Hbf.
      specialize (Hrel _ _ Hbf). destruct Hrel as (v' & aset & vm' & ? & ? & Hm & HR).
      eexists _, aset, vm'. do 2 (split; first done).
      rewrite lookup_insert_ne //.
  Qed.

  Lemma gmap_rel_view_alloc_big m (m' : gmap K (VA * (V * A))) dq :
    (∀ k vm v a, m' !! k = Some (vm, (v, a)) → ∀ n, R n vm v a) →
    (fst <$> m') ##ₘ m →
    ✓ dq →
    gmap_rel_view_auth R 1 m ~~>
      gmap_rel_view_auth R 1 ((fst <$> m') ∪ m) ⋅
      ([^op map] k↦v ∈ snd <$> m', gmap_rel_view_frag R k dq (snd v) (fst v)).
  Proof.
    intros HR Hdisj Hq. induction m' as [|k [va [v a]] m' Hlookup IH] using map_ind;
                          try (rewrite fmap_insert in Hdisj); decompose_map_disjoint.
    { rewrite ?fmap_empty big_opM_empty left_id_L right_id. done. }
    rewrite IH //; last first.
    { intros. eapply HR. rewrite lookup_insert_ne; eauto. set_solver. }
    rewrite ?fmap_insert big_opM_insert //; last first.
    { rewrite lookup_fmap Hlookup //=. }
    rewrite assoc.
    apply cmra_update_op; last done.
    rewrite -insert_union_l. apply (gmap_rel_view_alloc _ k dq); last done.
    { intros n. eapply (HR k). rewrite lookup_insert //. }
    apply lookup_union_None; split; auto.
    rewrite lookup_fmap Hlookup //.
  Qed.

  Lemma gmap_rel_view_delete m k v a :
    gmap_rel_view_auth R 1 m ⋅ gmap_rel_view_frag R k (DfracOwn 1) a v ~~>
    gmap_rel_view_auth R 1 (delete k m).
  Proof.
    apply view_update_dealloc=>n bf Hrel j [df va] Hbf /=.
    destruct (decide (j = k)) as [->|Hne].
    - edestruct (Hrel k) as (vf' & aset' & vm' & _ & Hdf & _ & HR).
      { rewrite lookup_op Hbf lookup_singleton -Some_op. done. }
      exfalso. apply: dfrac_full_exclusive. apply Hdf.
    - edestruct (Hrel j) as (vf' & aset' & vm' & ? & ? & Hm & HR).
      { rewrite lookup_op lookup_singleton_ne // Hbf. done. }
      exists vf', aset', vm'. do 2 (split; first done).
      rewrite lookup_delete_ne //.
  Qed.

  (*
  Lemma gmap_rel_view_delete_big m m' :
    gmap_rel_view_auth R 1 m ⋅ ([^op map] k↦av ∈ m', gmap_rel_view_frag R k (DfracOwn 1) v) ~~>
    gmap_rel_view_auth R 1 (m ∖ m').
  Proof.
    induction m' as [|k v m' ? IH] using map_ind.
    { rewrite right_id_L big_opM_empty right_id //. }
    rewrite big_opM_insert //.
    rewrite [gmap_rel_view_frag R _ _ _ ⋅ _]comm assoc IH gmap_rel_view_delete.
    rewrite -delete_difference. done.
  Qed.
   *)

  Lemma gmap_rel_view_update m k a v vm' a' v' :
    (∀ n, R n vm' v' a') →
    gmap_rel_view_auth R 1 m ⋅ gmap_rel_view_frag R k (DfracOwn 1) a v ~~>
      gmap_rel_view_auth R 1 (<[k := vm']> m) ⋅ gmap_rel_view_frag R k (DfracOwn 1) a' v'.
  Proof.
    intros HR.
    rewrite gmap_rel_view_delete.
    rewrite (gmap_rel_view_alloc _ k (DfracOwn 1) vm' a' v') //; last by rewrite lookup_delete.
    { rewrite insert_delete_insert //. }
  Qed.

  Lemma gmap_rel_view_update_approx m dq k a v a' :
    (∀ vm n, m !! k = Some vm → R n vm v a → R n vm v a') →
    gmap_rel_view_auth R 1 m ⋅ gmap_rel_view_frag R k dq a v ~~>
      gmap_rel_view_auth R 1 m ⋅ gmap_rel_view_frag R k dq a' v.
  Proof.
    intros HR. apply view_update. intros n bf Hrel.
    intros j [dq' [v' aset']].
    destruct (decide (j = k)) as [->|Hne].
    - intros Hlook.
      destruct (bf !! k) as [[dq'' [v'' aset'']]|] eqn:Heqbf.
      * edestruct (Hrel k) as (vh & aseth & vmh & Hequiv1 & Hdq & ? & HRh).
        { rewrite lookup_op Heqbf lookup_singleton -Some_op -?pair_op. reflexivity. }
        simpl. simpl in Hequiv1.
        rewrite lookup_op Heqbf lookup_singleton -Some_op -?pair_op in Hlook.

        eexists v, aset', vmh. split_and!; eauto.
        ** f_equiv. inversion Hlook. symmetry.
           apply agree_valid_includedN; last first.
           { econstructor; eauto. }
           { destruct Hequiv1 as [Heq1 _]. simpl in Heq1. rewrite Heq1. econstructor. }
        ** inversion Hlook; eauto.
        ** inversion Hlook; subst.
           inversion Hequiv1 as [Hequiva Hequivb%leibniz_equiv_iff]. simpl in Hequivb. subst.
           assert (Hvh: vh ≡{n}≡ v).
           { simpl in Hequiva. symmetry. apply to_agree_includedN.
             econstructor; symmetry; eauto. }
           set_unfold; intros ? [->|?].
           { eapply HR; eauto. eapply gval_rel_mono; eauto. }
           { eapply gval_rel_mono; eauto. }
      * edestruct (Hrel k) as (vh & aseth & vmh & Hequiv1 & Hdq & ? & HRh).
        { rewrite lookup_op Heqbf lookup_singleton //=. }
        simpl. simpl in Hequiv1.
        rewrite lookup_op Heqbf lookup_singleton //= in Hlook.
        eexists v, aset', vmh. split_and!; eauto.
        ** f_equiv. inversion Hlook. eauto.
        ** inversion Hlook; subst; eauto.
        ** inversion Hlook; subst.
           inversion Hequiv1 as [Hequiva Hequivb%leibniz_equiv_iff]. simpl in Hequivb. subst.
           set_unfold; intros ? ->.
           { eapply HR; eauto. eapply gval_rel_mono; eauto. apply to_agree_injN. eauto. }
    - rewrite lookup_op lookup_singleton_ne //= left_id. intros Heqbf.
      * edestruct (Hrel j) as (vh & aseth & vmh & Hequiv1 & Hdq & ? & HRh).
        { rewrite lookup_op Heqbf lookup_singleton_ne //=. }
        simpl. simpl in Hequiv1.
        eexists vh, aset', vmh. split_and!; eauto.
        ** f_equiv. inversion Hequiv1; eauto.
        ** inversion Hequiv1 as [Hequiva Hequivb%leibniz_equiv_iff]. simpl in Hequivb. subst. eauto.
  Qed.

  (*
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
   *)

  Lemma gmap_rel_view_persist k dq a v :
    gmap_rel_view_frag R k dq a v ~~> gmap_rel_view_frag R k DfracDiscarded a v.
  Proof.
    apply view_update_frag=>m n bf Hrel j [df va] /=.
    rewrite lookup_op. destruct (decide (j = k)) as [->|Hne].
    - rewrite lookup_singleton.
      edestruct (Hrel k ((dq, (to_agree v, {[a]})) ⋅? bf !! k)) as (vf' & aset' & vm' & Hdf & Hva & Hm & HR).
      { rewrite lookup_op lookup_singleton.
        destruct (bf !! k) eqn:Hbf; by rewrite Hbf. }
      rewrite Some_op_opM. intros [= Hbf].
      exists vf', aset', vm'. rewrite assoc; split; last done.
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
      simpl in *. eexists _, _, _. do 2 (split; first done). done.
  Qed.

  (** Typeclass instances *)
  Global Instance gmap_rel_view_frag_core_id k dq a v : CoreId dq → CoreId (gmap_rel_view_frag R k dq a v).
  Proof. apply _. Qed.

  Global Instance gmap_rel_view_cmra_discrete :
    OfeDiscrete VA →
    OfeDiscrete V → GvalRelDiscrete V A R → CmraDiscrete (gmap_rel_viewR K VA V A R).
  Proof. apply _. Qed. 

  Global Instance gmap_rel_view_frag_mut_is_op dq dq1 dq2 k a v :
    IsOp dq dq1 dq2 →
    IsOp' (gmap_rel_view_frag R k dq a v) (gmap_rel_view_frag R k dq1 a v) (gmap_rel_view_frag R k dq2 a v).
  Proof. rewrite /IsOp' /IsOp => ->. apply gmap_rel_view_frag_op. Qed.
End lemmas.

Typeclasses Opaque gmap_rel_view_auth gmap_rel_view_frag.
