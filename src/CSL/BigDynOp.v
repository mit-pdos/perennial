From iris.algebra Require Export big_op.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type*".
Local Existing Instances monoid_ne monoid_assoc monoid_comm
  monoid_left_id monoid_right_id monoid_proper
  monoid_homomorphism_rel_po monoid_homomorphism_rel_proper
  monoid_homomorphism_op_proper
  monoid_homomorphism_ne weak_monoid_homomorphism_proper.
Require Import EqualDec.
Require Export SemanticsHelpers.

(* Adapted from the big_op.v files from Iris. Extends those operators to work over DynMaps *)

Definition big_opDM `{Monoid M o} A (Ref Model: A -> Type)
      (f: ∀ {T}, Ref T → Model T → M) (m: DynMap Ref Model) :=
  big_opL o (λ _ k, match getDyn m (projT2 k) with
                    | None => monoid_unit
                    | Some v => f (projT2 k) v
                    end) (dynMap_dom m).

(*
Instance: Params (@big_opDM) 8 := {}.
*)
Arguments big_opDM {M} o {_ A Ref Model} _ _ : simpl never.
Typeclasses Opaque big_opDM.
Notation "'[^' o 'dmap]' k ↦ x ∈ m , P" := (big_opDM o (λ _ k x, P) m)
  (at level 200, o at level 1, m at level 10, k, x at level 1, right associativity,
   format "[^  o  dmap]  k ↦ x  ∈  m ,  P") : stdpp_scope.
Notation "'[^' o 'dmap]' x ∈ m , P" := (big_opDM o (λ _ _ x, P) m)
  (at level 200, o at level 1, m at level 10, x at level 1, right associativity,
   format "[^ o  dmap]  x  ∈  m ,  P") : stdpp_scope.
Notation "'[^' o 'dmap]' ( k : 'Ref' a ) ↦ x ∈ m , P" := (big_opDM o (λ a k x, P) m)
  (at level 200, o at level 1, m at level 10, k, x at level 1, right associativity, only printing,
   format "[^  o  dmap]  ( k :  Ref  a ) ↦ x  ∈  m ,  P") : stdpp_scope.

(** ** Big ops over DynMaps *)
Section monoid.
  Context `{Monoid M o}.
  Infix "`o`" := o (at level 50, left associativity).
  Context {A : Type} {Ref Model : A → Type}.
  Context `{dec : EqualDec {x : A & Ref x}}.
  Implicit Types m : DynMap Ref Model.
  Implicit Types f g : ∀ {T}, Ref T → Model T → M.

  Lemma big_opDM_forall R f g m :
    Reflexive R → Proper (R ==> R ==> R) o →
    (∀ {T} (k: Ref T) x, getDyn m k = Some x → R (f _ k x) (g _ k x)) →
    R ([^o dmap] k ↦ x ∈ m, f _ k x) ([^o dmap] k ↦ x ∈ m, g _ k x).
  Proof.
    intros ?? Hf. apply (big_opL_gen_proper R); auto.
    intros k [i x] (v&Heq)%dynMap_dom_lookup; eauto.
    rewrite Heq; eauto.
  Qed.

  Lemma big_opDM_ext f g m :
    (∀ {T} (k: Ref T) x, getDyn m k = Some x → f _ k x = g _ k x) →
    ([^o dmap] k ↦ x ∈ m, f _ k x) = ([^o dmap] k ↦ x ∈ m, g _ k x).
  Proof. apply big_opDM_forall; apply _. Qed.
  Lemma big_opDM_proper f g m :
    (∀ {T} (k: Ref T) x, getDyn m k = Some x → f _ k x ≡ g _ k x) →
    ([^o dmap] k ↦ x ∈ m, f _ k x) ≡ ([^o dmap] k ↦ x ∈ m, g _ k x).
  Proof. apply big_opDM_forall; apply _. Qed.
  Lemma big_opDM_proper_map f m1 m2 :
    m1 ≡ m2 →
    ([^o dmap] k ↦ x ∈ m1, f _ k x) ≡ ([^o dmap] k ↦ x ∈ m2, f _ k x).
  Proof.
    intros Hequiv. unfold big_opDM.
    rewrite big_opL_permutation; last by (rewrite Hequiv; reflexivity).
    eapply big_opL_proper => ???.
    by rewrite Hequiv.
  Qed.

  Global Instance big_opDM_ne n :
    Proper (forall_relation (λ T, pointwise_relation (Ref T) (pointwise_relation (Model T) (dist n)))
                            ==> eq ==> dist n)
           (big_opDM o (A:=A) (Ref:=Ref) (Model:=Model)).
  Proof. intros f g Hf m ? <-. apply big_opDM_forall; apply _ || intros; apply Hf. Qed.
  Global Instance big_opDM_proper' :
    Proper (forall_relation (λ T, pointwise_relation (Ref T) (pointwise_relation (Model T) (≡)))
                            ==> (≡) ==> (≡))
           (big_opDM o (A:=A) (Ref:=Ref) (Model:=Model)).
  Proof.
    intros f g Hf m1 m2 Hequiv.
    rewrite big_opDM_proper_map //.
    apply big_opDM_forall; apply _ || intros; apply Hf.
  Qed.
  Global Instance big_opDM_proper'' :
    Proper (eq ==> (≡) ==> (≡))
           (big_opDM o (A:=A) (Ref:=Ref) (Model:=Model)).
  Proof. intros ?? <- ?? ?. eapply big_opDM_proper'; eauto. intros ??. reflexivity. Qed.

  Lemma big_opDM_empty f : ([^o dmap] k↦x ∈ (∅ : DynMap Ref Model), f _ k x) = monoid_unit.
  Proof. rewrite /big_opDM //=. Qed.

  Lemma big_opDM_updDyn {T} f m (i: Ref T) (x: Model T):
    getDyn m i = None →
    ([^o dmap] k↦y ∈ updDyn (dec := dec) i x m, f _ k y) ≡ f _ i x `o` [^o dmap] k↦y ∈ m, f _ k y.
  Proof.
    intros Hnone. rewrite /big_opDM //= decide_False //= ?getDyn_updDyn //=; last first.
    { rewrite -dynMap_dom_spec => Hfalse. by apply Hfalse, getDyn_lookup_none. }
    f_equiv. apply big_opL_proper => k y. intros (v&Heq)%dynMap_dom_lookup.
    rewrite getDyn_updDyn_ne1 // => ?; subst. rewrite Hnone // in Heq.
  Qed.

  Lemma big_opDM_delete {T} f m (i: Ref T) x :
    getDyn m i = Some x →
    ([^o dmap] k↦y ∈ m, f _ k y) ≡ f _ i x `o` [^o dmap] k↦y ∈ deleteDyn (dec := dec) i m, f _ k y.
  Proof.
    rewrite -big_opDM_updDyn ?getDyn_deleteDyn // => Hsome.
    by rewrite updDyn_deleteDyn updDyn_identity.
  Qed.

  Lemma big_opDM_singleton {T} f (i: Ref T) x :
    ([^o dmap] k↦y ∈ updDyn (dec := dec) i x ∅, f _ k y) ≡ f _ i x.
  Proof.
    rewrite big_opDM_updDyn/=; last auto using lookup_empty.
    by rewrite big_opDM_empty right_id.
  Qed.

  Lemma big_opDM_unit m : ([^o dmap] k↦y ∈ m, monoid_unit) ≡ (monoid_unit : M).
  Proof.
    etransitivity; last eapply big_opL_unit.
    unfold big_opDM. eapply big_opL_proper.
    intros ??; by destruct getDyn.
  Qed.

  Lemma big_opDM_insert_override {T} f m (i: Ref T) x x' :
    getDyn m i = Some x → f _ i x ≡ f _ i x' →
    ([^o dmap] k↦y ∈ updDyn (dec := dec) i x' m, f _ k y) ≡ ([^o dmap] k↦y ∈ m, f _ k y).
  Proof.
    intros ? Hx. rewrite -updDyn_deleteDyn big_opDM_updDyn ?getDyn_deleteDyn //.
    by rewrite -Hx -big_opDM_delete.
  Qed.

  Lemma big_opDM_opDM f g m :
    ([^o dmap] k↦x ∈ m, f _ k x `o` g _ k x )
    ≡ ([^o dmap] k↦x ∈ m, f _ k x) `o` ([^o dmap] k↦x ∈ m, g _ k x).
  Proof.
    rewrite /big_opM -big_opL_op. eapply big_opL_proper => k [??] Heq.
    destruct (getDyn) => //=. by rewrite right_id.
  Qed.
End monoid.

Section homomorphisms.
  Context `{Monoid M1 o1, Monoid M2 o2}.
  Context {A : Type} {Ref Model : A → Type}.
  Context `{dec : EqualDec {x : A & Ref x}}.
  Infix "`o1`" := o1 (at level 50, left associativity).
  Infix "`o2`" := o2 (at level 50, left associativity).
  (** The ssreflect rewrite tactic only works for relations that have a
  [RewriteRelation] instance. For the purpose of this section, we want to
  rewrite with arbitrary relations, so we declare any relation to be a
  [RewriteRelation]. *)
  Local Instance: ∀ {A} (R : relation A), RewriteRelation R := {}.

  Lemma morphism_commute_lookup (h: M1 → M2) `{!MonoidHomomorphism o1 o2 R h}
      (f : ∀ T, Ref T → Model T → M1) (m: DynMap Ref Model) x:
    R (h match getDyn m (projT2 x) with
      | Some v => f (projT1 x) (projT2 x) v
      | None => monoid_unit
      end)
      (match getDyn m (projT2 x) with
       | Some v => h (f (projT1 x) (projT2 x) v)
       | None => monoid_unit
       end).
  Proof.
    destruct getDyn; eauto.
    - reflexivity.
    - by rewrite monoid_homomorphism_unit.
  Qed.

  Lemma big_opDM_commute (h : M1 → M2) `{!MonoidHomomorphism o1 o2 R h}
      (f : ∀ T, Ref T → Model T → M1) (m: DynMap Ref Model) :
    R (h ([^o1 dmap] k↦x ∈ m, f _ k x)) ([^o2 dmap] k↦x ∈ m, h (f _ k x)).
  Proof.
    rewrite /big_opDM. rewrite big_opL_commute.
    apply big_opL_gen_proper; try apply _.
    intros. by rewrite morphism_commute_lookup.
  Qed.

  Lemma big_opDM_commute1 (h : M1 → M2) `{!WeakMonoidHomomorphism o1 o2 R h}
       (f : ∀ T, Ref T → Model T → M1) (m: DynMap Ref Model) :
    m ≢ ∅ → R (h ([^o1 dmap] k↦x ∈ m, f _ k x)) ([^o2 dmap] k↦x ∈ m, h (f _ k x)).
  Proof.
    intros. rewrite /big_opDM big_opL_commute1.
    - apply big_opL_gen_proper; try apply _.
      intros ?? (v&->)%dynMap_dom_lookup. reflexivity.
    - by rewrite -dynMap_dom_empty_iff.
  Qed.
End homomorphisms.


From iris.bi Require Import derived_laws_sbi plainly big_op.
Import interface.bi derived_laws_bi.bi derived_laws_sbi.bi.

(** ** Separating conjunctions over DynMaps *)
Notation "'[∗' 'dmap]' k ↦ x ∈ m , P" := (big_opDM bi_sep (λ _ k x, P) m)
  (at level 200, m at level 10, k, x at level 1, right associativity,
   format "[∗  dmap]  k ↦ x  ∈  m ,  P") : bi_scope.
Notation "'[∗' 'dmap]' ( k : 'Ref' a ) ↦ x ∈ m , P" := (big_opDM bi_sep (λ a k x, P) m)
  (at level 200, m at level 10, k, x at level 1, right associativity, only printing,
   format "[∗  dmap]  ( k :  Ref  a ) ↦ x  ∈  m ,  P") : stdpp_scope.


Section prop.
Context {PROP : bi}.
Implicit Types P Q : PROP.
Implicit Types Ps Qs : list PROP.
  Context {A : Type} {Ref Model : A → Type}.
  Context `{dec : EqualDec {x : A & Ref x}}.
  Implicit Types m : DynMap Ref Model.
  Implicit Types Φ Ψ : ∀ {T}, Ref T → Model T → PROP.

  Lemma big_sepDM_mono Φ Ψ m :
    (∀ a k x, getDyn m k = Some x → Φ a k x ⊢ Ψ a k x) →
    ([∗ dmap] k ↦ x ∈ m, Φ _ k x) ⊢ [∗ dmap] k ↦ x ∈ m, Ψ _ k x.
  Proof. apply big_opDM_forall; apply _ || auto. Qed.
  Lemma big_sepDM_proper Φ Ψ m :
    (∀ a k x, getDyn m k = Some x → Φ a k x ⊣⊢ Ψ a k x) →
    ([∗ dmap] k ↦ x ∈ m, Φ _ k x) ⊣⊢ ([∗ dmap] k ↦ x ∈ m, Ψ _ k x).
  Proof. apply big_opDM_proper. Qed.
  (*
  Lemma big_sepDM_subseteq `{BiAffine PROP} Φ m1 m2 :
    m2 ⊆ m1 → ([∗ dmap] k ↦ x ∈ m1, Φ k x) ⊢ [∗ dmap] k ↦ x ∈ m2, Φ k x.
  Proof. intros. by apply big_sepL_submseteq, map_to_list_submseteq. Qed.
   *)

  Global Instance big_sepDM_mono' :
    Proper (forall_relation (λ T, pointwise_relation (Ref T) (pointwise_relation (Model T) (⊢)))
                            ==> (≡) ==> (⊢))
           (big_opDM (@bi_sep PROP) (A:=A) (Ref:=Ref) (Model:=Model)).
  Proof. intros f g Hf m ? <-. apply big_sepDM_mono=> ????; apply Hf. Qed.

  Lemma big_sepDM_empty Φ : ([∗ dmap] k↦x ∈ (∅: DynMap Ref Model), Φ _ k x) ⊣⊢ emp.
  Proof. by rewrite big_opDM_empty. Qed.
  Lemma big_sepDM_empty' `{BiAffine PROP} P Φ : P ⊢ [∗ dmap] k↦x ∈ (∅: DynMap Ref Model), Φ _ k x.
  Proof. rewrite big_sepDM_empty. apply: affine. Qed.

  Lemma big_sepDM_updDyn {T} Φ m (i: Ref T) x :
    getDyn m i = None →
    ([∗ dmap] k↦y ∈ updDyn (dec:=dec) i x m, Φ _ k y) ⊣⊢ Φ _ i x ∗ [∗ dmap] k↦y ∈ m, Φ _ k y.
  Proof. apply big_opDM_updDyn. Qed.

  Lemma big_sepDM_delete {T} Φ m (i: Ref T) x :
    getDyn m i = Some x →
    ([∗ dmap] k↦y ∈ m, Φ _ k y) ⊣⊢ Φ _ i x ∗ [∗ dmap] k↦y ∈ deleteDyn (dec:=dec) i m, Φ _ k y.
  Proof. apply big_opDM_delete. Qed.

  Lemma big_sepDM_delete_1 {T} Φ m (i: Ref T) x :
    getDyn m i = Some x →
    ([∗ dmap] k↦y ∈ m, Φ _ k y) ⊢ Φ _ i x ∗ [∗ dmap] k↦y ∈ deleteDyn (dec:=dec) i m, Φ _ k y.
  Proof.
    intros.
    iDestruct (big_sepDM_delete Φ _ _ H) as "(H&_)".
    iApply "H".
  Qed.

  Lemma big_sepDM_updDyn_2 {T} Φ m (i: Ref T) x :
    TCOr (∀ x, Affine (Φ _ i x)) (Absorbing (Φ _ i x)) →
    Φ _ i x -∗ ([∗ dmap] k↦y ∈ m, Φ _ k y) -∗ [∗ dmap] k↦y ∈ updDyn (dec:=dec) i x m, Φ _ k y.
  Proof.
    intros Ha. apply wand_intro_r. destruct (getDyn m i) as [y|] eqn:Hi; last first.
    { by rewrite -big_sepDM_updDyn. }
    assert (TCOr (Affine (Φ _ i y)) (Absorbing (Φ _ i x))).
    { destruct Ha; try apply _. }
    rewrite big_sepDM_delete // assoc.
    rewrite (sep_elim_l (Φ _ i x)) -big_sepDM_updDyn ?getDyn_deleteDyn //.
    by rewrite updDyn_deleteDyn.
  Qed.

  Lemma big_sepDM_lookup_acc {T} Φ m (i: Ref T) x :
    getDyn m i = Some x →
    ([∗ dmap] k↦y ∈ m, Φ _ k y) ⊢ Φ _ i x ∗ (Φ _ i x -∗ ([∗ dmap] k↦y ∈ m, Φ _ k y)).
  Proof.
    intros. rewrite big_sepDM_delete //. by apply sep_mono_r, wand_intro_l.
  Qed.

  Lemma big_sepDM_lookup {T} Φ m (i: Ref T) x `{!Absorbing (Φ _ i x)} :
    getDyn m i = Some x → ([∗ dmap] k↦y ∈ m, Φ _ k y) ⊢ Φ _ i x.
  Proof. intros. rewrite big_sepDM_lookup_acc //. by rewrite sep_elim_l. Qed.

  (*
  Lemma big_sepM_lookup_dom (Φ : K → PROP) m i `{!Absorbing (Φ i)} :
    is_Some (m !! i) → ([∗ map] k↦_ ∈ m, Φ k) ⊢ Φ i.
  Proof. intros [x ?]. by eapply (big_sepM_lookup (λ i x, Φ i)). Qed.
   *)

  Lemma big_sepDM_singleton {T} Φ (i: Ref T) x :
    ([∗ dmap] k↦y ∈ updDyn (dec := dec) i x ∅, Φ _ k y) ⊣⊢ Φ _ i x.
  Proof. by rewrite big_opDM_singleton. Qed.

  Lemma big_sepDM_insert_override {T} Φ m (i: Ref T) x x' :
    getDyn m i = Some x → (Φ _ i x ⊣⊢ Φ _ i x') →
    ([∗ dmap] k↦y ∈ updDyn (dec := dec) i x' m, Φ _ k y) ⊣⊢ ([∗ dmap] k↦y ∈ m, Φ _ k y).
  Proof. apply big_opDM_insert_override. Qed.

  Lemma big_sepDM_insert_override_1 {T} Φ m (i: Ref T) x x' :
    getDyn m i = Some x →
    ([∗ dmap] k↦y ∈ updDyn (dec := dec) i x' m, Φ _ k y) ⊢
      (Φ _ i x' -∗ Φ _ i x) -∗ ([∗ dmap] k↦y ∈ m, Φ _ k y).
  Proof.
    intros ?. apply wand_intro_l.
    rewrite -updDyn_deleteDyn big_sepDM_updDyn ?getDyn_deleteDyn //.
    by rewrite assoc wand_elim_l -big_sepDM_delete.
  Qed.

  Lemma big_sepDM_insert_override_2 {T} Φ m (i: Ref T) x x' :
    getDyn m i = Some x →
    ([∗ dmap] k↦y ∈ m, Φ _ k y) ⊢
      (Φ _ i x -∗ Φ _ i x') -∗ ([∗ dmap] k↦y ∈ updDyn (dec := dec) i x' m, Φ _ k y).
  Proof.
    intros ?. apply wand_intro_l.
    rewrite {1}big_sepDM_delete //; rewrite assoc wand_elim_l.
    rewrite -updDyn_deleteDyn big_sepDM_updDyn ?getDyn_deleteDyn //.
  Qed.

  Lemma big_sepDM_insert_acc {T} Φ m (i: Ref T) x :
    getDyn m i = Some x →
    ([∗ dmap] k↦y ∈ m, Φ _ k y) ⊢
      Φ _ i x ∗ (∀ x', Φ _ i x' -∗ ([∗ dmap] k↦y ∈ updDyn (dec := dec) i x' m, Φ _ k y)).
  Proof.
    intros ?. rewrite {1}big_sepDM_delete //. apply sep_mono; [done|].
    apply forall_intro=> x'.
    rewrite -updDyn_deleteDyn big_sepDM_updDyn ?getDyn_deleteDyn //.
    by apply wand_intro_l.
  Qed.

  (*
  Lemma big_sepDM_union Φ m1 m2 :
    m1 ##ₘ m2 →
    ([∗ map] k↦y ∈ m1 ∪ m2, Φ k y)
    ⊣⊢ ([∗ map] k↦y ∈ m1, Φ k y) ∗ ([∗ map] k↦y ∈ m2, Φ k y).
  Proof. apply big_opM_union. Qed.
   *)

  Lemma big_sepDM_sepDM Φ Ψ m :
    ([∗ dmap] k↦x ∈ m, Φ _ k x ∗ Ψ _ k x)
    ⊣⊢ ([∗ dmap] k↦x ∈ m, Φ _ k x) ∗ ([∗ dmap] k↦x ∈ m, Ψ _ k x).
  Proof. apply big_opDM_opDM. Qed.

  Lemma big_sepDM_and Φ Ψ m :
    ([∗ dmap] k↦x ∈ m, Φ _ k x ∧ Ψ _ k x)
    ⊢ ([∗ dmap] k↦x ∈ m, Φ _ k x) ∧ ([∗ dmap] k↦x ∈ m, Ψ _ k x).
  Proof. auto using and_intro, big_sepDM_mono, and_elim_l, and_elim_r. Qed.

  Lemma big_sepDM_persistently `{BiAffine PROP} Φ m :
    (<pers> ([∗ dmap] k↦x ∈ m, Φ _ k x)) ⊣⊢ ([∗ dmap] k↦x ∈ m, <pers> (Φ _ k x)).
  Proof. apply (big_opDM_commute _). Qed.

  Lemma big_sepDM_forall `{BiAffine PROP} Φ m :
    (∀ a k x, Persistent (Φ a k x)) →
    ([∗ dmap] k↦x ∈ m, Φ _ k x) ⊣⊢ (∀ a k x, ⌜getDyn m k = Some x⌝ → Φ a k x).
  Proof.
    intros. apply (anti_symm _).
    { apply forall_intro=> a; apply forall_intro=> k; apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply: big_sepDM_lookup. }
    rewrite /big_opDM big_sepL_forall.
    iIntros "H". iIntros (a (k&x) (v&Heq)%dynMap_dom_lookup).
    rewrite Heq. by iApply "H".
  Qed.

  Lemma big_sepDM_impl Φ Ψ m :
    ([∗ dmap] k↦x ∈ m, Φ _ k x) -∗
    □ (∀ a k x, ⌜ getDyn m k = Some x⌝ → Φ a k x -∗ Ψ _ k x) -∗
    [∗ dmap] k↦x ∈ m, Ψ _ k x.
  Proof.
    iIntros "H #Himpl". rewrite /big_opDM. iApply (big_sepL_impl with "H").
    iAlways; iIntros (n (a&k) (v&Heq)%dynMap_dom_lookup).
    rewrite Heq. iIntros "H". unshelve (by iApply ("Himpl" $! a k v _)); eauto.
  Qed.

  Global Instance big_sepDM_empty_persistent Φ :
    Persistent ([∗ dmap] k↦x ∈ (∅: DynMap Ref Model), Φ _ k x).
  Proof. rewrite /big_opDM. apply _. Qed.
  Global Instance big_sepDM_persistent Φ m :
    (∀ a k x, Persistent (Φ a k x)) → Persistent ([∗ dmap] k↦x ∈ m, Φ _ k x).
  Proof. intros. apply big_sepL_persistent=> _ [??]; apply _. Qed.

  Global Instance big_sepDM_empty_affine Φ :
    Affine ([∗ dmap] k↦x ∈ (∅: DynMap Ref Model), Φ _ k x).
  Proof. rewrite /big_opDM. apply _. Qed.
  Global Instance big_sepDM_affine Φ m :
    (∀ a k x, Affine (Φ a k x)) → Affine ([∗ dmap] k↦x ∈ m, Φ _ k x).
  Proof. intros. apply big_sepL_affine=> _ [??]. destruct getDyn; apply _. Qed.
End prop.

Section sprop.
Context {PROP : sbi}.
Implicit Types P Q : PROP.
Implicit Types Ps Qs : list PROP.
  Context {A : Type} {Ref Model : A → Type}.
  Implicit Types m : DynMap Ref Model.
  Implicit Types Φ Ψ : ∀ {T}, Ref T → Model T → PROP.

  Global Instance big_sepDM_timeless Φ m :
    Timeless (emp: PROP)%I →
    (∀ a k x, Timeless (Φ a k x)) → Timeless ([∗ dmap] k↦x ∈ m, Φ _ k x).
  Proof. intros. eapply big_sepL_timeless=> _ [??]; apply _. Qed.
End sprop.

(* TODO: upstream this *)
Section big_op.
Context `{Monoid M o}.
Implicit Types xs : list M.
Infix "`o`" := o (at level 50, left associativity).
Section gset.
  Context `{Countable A} `{Countable B}.
  Implicit Types X : gset A.
  Implicit Types f : A → M.

  Lemma set_map_union_singleton (h: A → B) X x:
    set_map h ({[x]} ∪ X) = ({[h x]} ∪ (set_map h X) : gset B).
  Proof. set_solver. Qed.

  Lemma big_opS_fmap (h: A → B) X (g: B → M):
    (∀ x y, h x = h y → x = y) →
    ([^o set] x ∈ set_map h X, g x) ≡ ([^o set] x ∈ X, g (h x)).
  Proof.
    intros Hinj.
    induction X as [|x X ? IH] using set_ind_L => //=; [ by rewrite big_opS_eq | ].
    rewrite set_map_union_singleton.
    rewrite ?big_opS_union.
    - rewrite ?big_opS_singleton IH //.
    - set_solver.
    - cut ((h x) ∉ (set_map h X : gset _)); first by set_solver.
      intros (x'&Heq&Hin)%elem_of_map.
      apply Hinj in Heq. subst. auto.
  Qed.
End gset.
End big_op.

Section bi_big_op.
Context {PROP : bi}.
Implicit Types P Q : PROP.
Implicit Types Ps Qs : list PROP.
Implicit Types A : Type.
Section map.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → PROP.

  Lemma big_sepM_mono_with_inv' P Φ Ψ m :
    (∀ k x, m !! k = Some x → P ∗ Φ k x ⊢ P ∗ Ψ k x) →
    P ∗ ([∗ map] k ↦ x ∈ m, Φ k x) ⊢ P ∗ [∗ map] k ↦ x ∈ m, Ψ k x.
  Proof.
    intros Hwand.
    induction m as [|i x m ? IH] using map_ind; auto using big_sepM_empty'.
    by rewrite big_opM_eq.
    rewrite ?big_sepM_insert //.
    iIntros "(HP&Hi&H)".
    iDestruct (Hwand with "[$]") as "(?&$)".
    { by rewrite lookup_insert. }
    iApply IH; eauto.
    { iIntros (k x' Hlookup). iApply Hwand.
      destruct (decide (i = k)).
      - subst. congruence.
      - rewrite lookup_insert_ne //.
    }
    iFrame.
  Qed.

  Lemma big_sepM_mono_with_inv P Φ Ψ m :
    (∀ k x, m !! k = Some x → P ∗ Φ k x ⊢ P ∗ Ψ k x) →
    P -∗ ([∗ map] k ↦ x ∈ m, Φ k x) -∗ P ∗ [∗ map] k ↦ x ∈ m, Ψ k x.
  Proof.
    iIntros (?) "HP H". iApply (big_sepM_mono_with_inv' with "[HP H]"); eauto.
    iFrame.
  Qed.
End map.
End bi_big_op.
