From iris.algebra Require Export big_op.
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
Notation "'[^' o 'dmap]' k ↦ x ∈ m , P" := (big_opDM o (λ k x, P) m)
  (at level 200, o at level 1, m at level 10, k, x at level 1, right associativity,
   format "[^  o  dmap]  k ↦ x  ∈  m ,  P") : stdpp_scope.
Notation "'[^' o 'dmap]' x ∈ m , P" := (big_opDM o (λ _ x, P) m)
  (at level 200, o at level 1, m at level 10, x at level 1, right associativity,
   format "[^ o  dmap]  x  ∈  m ,  P") : stdpp_scope.

(** ** Big ops over DynMaps *)
Section DynMap.
  Context `{Monoid M o}.
  Infix "`o`" := o (at level 50, left associativity).
  Context {A : Type} {Ref Model : A → Type}.
  Context `{dec : EqualDec {x : A & Ref x}}.
  Implicit Types m : DynMap Ref Model.
  Implicit Types f g : ∀ {T}, Ref T → Model T → M.

  Lemma big_opDM_forall R f g m :
    Reflexive R → Proper (R ==> R ==> R) o →
    (∀ {T} (k: Ref T) x, getDyn m k = Some x → R (f _ k x) (g _ k x)) →
    R ([^o dmap] k ↦ x ∈ m, f k x) ([^o dmap] k ↦ x ∈ m, g k x).
  Proof.
    intros ?? Hf. apply (big_opL_forall R); auto.
    intros k [i x] ?%elem_of_list_lookup_2.
    destruct (getDyn) eqn:?; last (exfalso; eapply dynMap_dom_spec); eauto.
    by apply getDyn_lookup_none.
  Qed.

  Lemma big_opDM_ext f g m :
    (∀ {T} (k: Ref T) x, getDyn m k = Some x → f _ k x = g _ k x) →
    ([^o dmap] k ↦ x ∈ m, f k x) = ([^o dmap] k ↦ x ∈ m, g k x).
  Proof. apply big_opDM_forall; apply _. Qed.
  Lemma big_opDM_proper f g m :
    (∀ {T} (k: Ref T) x, getDyn m k = Some x → f _ k x ≡ g _ k x) →
    ([^o dmap] k ↦ x ∈ m, f k x) ≡ ([^o dmap] k ↦ x ∈ m, g k x).
  Proof. apply big_opDM_forall; apply _. Qed.
  Lemma big_opDM_proper_map f m1 m2 :
    m1 ≡ m2 →
    ([^o dmap] k ↦ x ∈ m1, f k x) ≡ ([^o dmap] k ↦ x ∈ m2, f k x).
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

  Lemma big_opDM_empty f : ([^o dmap] k↦x ∈ (∅ : DynMap Ref Model), f k x) = monoid_unit.
  Proof. rewrite /big_opDM //=. Qed.

  Lemma big_opDM_updDyn {T} f m (i: Ref T) (x: Model T):
    getDyn m i = None →
    ([^o dmap] k↦y ∈ updDyn (dec := dec) i x m, f k y) ≡ f _ i x `o` [^o dmap] k↦y ∈ m, f k y.
  Proof.
    intros Hnone. rewrite /big_opDM //= decide_False //= ?getDyn_updDyn //=; last first.
    { rewrite -dynMap_dom_spec => Hfalse. by apply Hfalse, getDyn_lookup_none. }
    f_equiv. apply big_opL_proper => k y. intros Hlookup%elem_of_list_lookup_2.
    rewrite getDyn_updDyn_ne1 //.
    intros Heq. subst. apply dynMap_dom_spec in Hlookup. apply Hlookup.
    by apply getDyn_lookup_none.
  Qed.

  Lemma big_opDM_delete {T} f m (i: Ref T) x :
    getDyn m i = Some x →
    ([^o dmap] k↦y ∈ m, f k y) ≡ f _ i x `o` [^o dmap] k↦y ∈ deleteDyn (dec := dec) i m, f k y.
  Proof.
    rewrite -big_opDM_updDyn ?getDyn_deleteDyn // => Hsome.
    by rewrite updDyn_deleteDyn updDyn_identity.
  Qed.

  Lemma big_opM_singleton {T} f (i: Ref T) x :
    ([^o dmap] k↦y ∈ updDyn (dec := dec) i x ∅, f k y) ≡ f _ i x.
  Proof.
    rewrite big_opDM_updDyn/=; last auto using lookup_empty.
    by rewrite big_opDM_empty right_id.
  Qed.

  Lemma big_opDM_unit m : ([^o dmap] k↦y ∈ m, (λ _ _ _, monoid_unit) k y) ≡ (monoid_unit : M).
  Proof.
    etransitivity; last eapply big_opL_unit.
    unfold big_opDM. eapply big_opL_proper.
    intros ??; by destruct getDyn.
  Qed.

  Lemma big_opM_insert_override {T} f m (i: Ref T) x x' :
    getDyn m i = Some x → f _ i x ≡ f _ i x' →
    ([^o dmap] k↦y ∈ updDyn (dec := dec) i x' m, f k y) ≡ ([^o dmap] k↦y ∈ m, f k y).
  Proof.
    intros ? Hx. rewrite -updDyn_deleteDyn big_opDM_updDyn ?getDyn_deleteDyn //.
    by rewrite -Hx -big_opDM_delete.
  Qed.

  Lemma big_opM_opM f g m :
    ([^o dmap] k↦x ∈ m, (λ _ k x, f _ k x `o` g _ k x) k x )
    ≡ ([^o dmap] k↦x ∈ m, f k x) `o` ([^o dmap] k↦x ∈ m, g k x).
  Proof.
    rewrite /big_opM -big_opL_opL. eapply big_opL_proper => k [??] Heq.
    destruct (getDyn) => //=. by rewrite right_id.
  Qed.
End DynMap.

