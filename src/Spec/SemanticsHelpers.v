From Classes Require Import EqualDec.
From stdpp Require Import base.

From Transitions Require Import Relations.
From Perennial Require Import Spec.Proc.

Set Implicit Arguments.

Arguments existT {A P} _ _.
Import EqNotations.

Import RelationNotations.

(* modeling non-atomic operations as pairs of begin/end ops *)
Inductive NonAtomicArgs T :=
| FinishArgs (args:T)
| Begin.
Arguments Begin {T}.
(* NOTE: this does not allow dependent return values *)
Definition retT T (args:NonAtomicArgs T) T' : Type := if args then T' else unit.

(* nonAtomicOp takes an operation partially applied to some key identifying
  the object (assuming the operation does separate over some resources, such as
  addresses or references) *)
Definition nonAtomicOp {Op ArgT T}
           (op: forall (args:NonAtomicArgs ArgT), Op (retT args T))
  : ArgT -> proc Op T :=
  fun args => Bind (Call (op Begin)) (fun _ => Call (op (FinishArgs args))).


(* this is represented as an inductive rather than a combination of ObjΣ and a
  boolean state to make misuse harder (there's no reasonable way to use the
  state without knowing the status) *)
Inductive NonAtomicState ObjΣ : Type :=
| Clean (s:ObjΣ)
| Dirty (s:ObjΣ).

Definition readClean {State} ObjΣ (s: NonAtomicState ObjΣ) : relation State State ObjΣ :=
  match s with
  | Clean s => pure s
  | Dirty _ => error
  end.

Definition readDirty {State} ObjΣ (s: NonAtomicState ObjΣ) : relation State State ObjΣ :=
  match s with
  | Clean _ => error
  | Dirty s  => pure s
  end.

Definition nonAtomicStep
           {ArgT} (args: NonAtomicArgs ArgT) {T} (* the operation *)
           {ObjΣ} (obj_s: NonAtomicState ObjΣ)
           {State}
           (mkDirty: ObjΣ -> relation State State unit)
           (opStep: ObjΣ -> ArgT -> relation State State T)
  : relation State State (retT args T) :=
  match args with
  | Begin => s <- readClean obj_s;
              mkDirty s
  | FinishArgs x => s <- readDirty obj_s;
                     opStep s x
  end.

Record DynMap A (Ref: A -> Type) (Model: A -> Type) :=
  { dynMap : sigT Ref -> option (sigT Model);
    dynMap_wf : forall T v, match dynMap (existT T v) with
                       | Some (existT T' _) => T' = T
                       | None => True
                       end;
    dynMap_dom : list (sigT Ref);
    dynMap_dom_spec : forall x, dynMap x <> None <-> x ∈ dynMap_dom;
    dynMap_dom_nodup : NoDup dynMap_dom;
}.

Module OptionNotations.
  Delimit Scope option_monad with opt.
  Notation "'Some!' x <- a ; f" :=
    (match a with
     | Some x => f
     | _ => None
     end)
      (right associativity, at level 70, x pattern) : option_monad.

  Notation "'left!' H <- a ; f" :=
    (match a with
     | left H => f
     | right _ => None
     end)
      (right associativity, at level 60, f at level 200) : option_monad.

  Notation "'ret!' a" := (Some a) (at level 60) : option_monad.
End OptionNotations.

Import EqualDecNotation.
Import OptionNotations.
Local Open Scope option_monad.

Definition getDyn A (Ref Model: A -> Type)
           (m: DynMap Ref Model) a (r: Ref a) : option (Model a).
Proof.
  pose proof (m.(dynMap_wf) _ r).
  destruct (m.(dynMap) (existT a r)); [ apply Some | exact None ].
  destruct s.
  exact (rew H in m0).
Defined.

Require Import Program.

Lemma getDyn_lookup1 A (Ref Model: A -> Type)
      (m: DynMap Ref Model) a (r: Ref a) (v: Model a) :
  m.(dynMap) (existT _ r) = Some (existT _ v) →
  getDyn m a r = Some v.
Proof.
  unfold getDyn. destruct m as [map wf]. simpl.
  generalize (wf a r). generalize (map (existT a r)).
  intros ret Heq. clear.
  destruct ret as [(?&?)|]; inversion 1.
  subst. apply Eqdep.EqdepTheory.inj_pair2 in H2; subst; auto.
Qed.

Lemma getDyn_lookup2 A (Ref Model: A -> Type)
      (m: DynMap Ref Model) a (r: Ref a) (v: Model a) :
  getDyn m a r = Some v →
  m.(dynMap) (existT _ r) = Some (existT _ v).
Proof.
  unfold getDyn. destruct m as [map wf]. simpl.
  generalize (wf a r). generalize (map (existT a r)).
  intros ret Heq. clear.
  destruct ret as [(?&?)|]; inversion 1.
  subst. unfold eq_rect. auto.
Qed.

Lemma getDyn_lookup_none A (Ref Model: A -> Type)
      (m: DynMap Ref Model) a (r: Ref a) :
  getDyn m a r = None <->
  m.(dynMap) (existT _ r) = None.
Proof.
  unfold getDyn. destruct m as [map wf]. simpl.
  generalize (wf a r). generalize (map (existT a r)).
  intros ret Heq. clear.
  destruct ret as [(?&?)|]; [| intuition].
  split; inversion 1.
Qed.

Lemma getDyn_lookup_none1 A (Ref Model: A -> Type)
      (m: DynMap Ref Model) a (r: Ref a) :
  m.(dynMap) (existT _ r) = None ->
  getDyn m a r = None.
Proof. edestruct getDyn_lookup_none; eauto. Qed.

Lemma getDyn_lookup_none2 A (Ref Model: A -> Type)
      (m: DynMap Ref Model) a (r: Ref a) :
  getDyn m a r = None ->
  m.(dynMap) (existT _ r) = None.
Proof. edestruct getDyn_lookup_none; eauto. Qed.

Arguments getDyn {A Ref Model} m {a} r.
From stdpp Require Import list.

Instance In_dec {T} {dec: EqualDec T} (a: T) (l: list T):
  Decision (a ∈ l).
Proof.
  assert (EqDecision T).
  { unfold EqDecision, EqualDec, Decision in *; eauto. }
  apply _.
Qed.

(*
Instance In_dec {T} {dec: EqualDec T} (a: T) l:
  Decision (In a l).
Proof.
  assert (EqDecision T).
  { unfold EqDecision, EqualDec, Decision in *; eauto. }
  edestruct (@elem_of_list_dec _ _ a l).
  * left. by apply elem_of_list_In.
  * right. intros Hfalse. eapply n. by apply elem_of_list_In.
Qed.
*)

Definition updDyn A (Ref Model: A -> Type) {dec: EqualDec (sigT Ref)}
           a (v: Ref a) (x: Model a) (m: DynMap Ref Model) : DynMap Ref Model.
Proof.
  refine {| dynMap := fun r => if r == existT a v then ret! existT a x else m.(dynMap) r;
            dynMap_dom := if decide ((existT a v) ∈ m.(dynMap_dom)) then
                            m.(dynMap_dom)
                          else
                            existT a v :: m.(dynMap_dom) |}.
  { intros.
    destruct (existT _ v0 == existT _ v).
    - inversion e; auto.
    - apply (m.(dynMap_wf) _ v0). }
  { intros (a'&v').
    destruct (existT _ _ == existT _ v).
    - abstract (split; auto; intros _; inversion e; subst;
                apply Eqdep.EqdepTheory.inj_pair2 in e; subst; auto;
                case (decide); eauto; intros; by left).
    - abstract (rewrite dynMap_dom_spec; split; case (decide); auto; intros ?;
                [ by right | rewrite elem_of_cons; intros [|]; eauto; congruence ]).
  }
  { case (decide).
    - intros; apply dynMap_dom_nodup.
    - intros Hnotin. econstructor; [| apply dynMap_dom_nodup]; auto.
  }
Defined.

Lemma remove_elem_of {A: Type} dec (l: list A) (x : A):
  ~ x ∈ (remove dec x l).
Proof.
  induction l; eauto; simpl; eauto.
  * inversion 1.
  * destruct dec; subst; eauto. rewrite elem_of_cons; intuition.
Qed.

Lemma remove_elem_of_ne {A: Type} dec (l: list A) (x y : A):
  ~ (y = x) -> y ∈ (remove dec x l) <-> y ∈ l.
Proof.
  induction l; eauto.
  intros Hneq. simpl. destruct dec; subst; rewrite ?elem_of_cons.
  * rewrite IHl; intuition.
  * rewrite ?IHl; eauto.
Qed.

Lemma remove_In_ne {A: Type} dec (l: list A) (x y : A):
  ~ (x = y) -> In y (remove dec x l) <-> In y l.
Proof.
  induction l; eauto.
  intros Hneq. simpl. destruct dec; subst.
  * rewrite IHl; intuition.
  * simpl. rewrite IHl; eauto.
Qed.

Lemma remove_NoDup {A: Type} dec (l: list A) (x : A):
  NoDup l → NoDup (remove dec x l).
Proof.
  induction 1; simpl. econstructor.
  destruct dec; subst; eauto.
  econstructor; eauto. rewrite elem_of_list_In, remove_In_ne; eauto.
  by rewrite <-elem_of_list_In.
Qed.

Definition deleteDyn A (Ref Model: A -> Type) {dec: EqualDec (sigT Ref)}
           a (v: Ref a) (m: DynMap Ref Model) : DynMap Ref Model.
Proof.
  refine {| dynMap := fun r => if r == existT a v then None else m.(dynMap) r;
            dynMap_dom := remove dec (existT a v) m.(dynMap_dom) |}.
  intros.
  destruct (existT _ v0 == existT _ v).
  - auto.
  - apply (m.(dynMap_wf) _ v0).
  - { intros (a'&v').
      destruct (existT _ _ == existT _ v).
      - split; auto; intros Hin.
        * by eauto.
        * inversion e. subst.
          apply Eqdep.EqdepTheory.inj_pair2 in e; subst; auto.
          exfalso; eapply remove_elem_of; eauto.
      - rewrite dynMap_dom_spec. rewrite remove_elem_of_ne; auto.
    }
  - apply remove_NoDup, dynMap_dom_nodup.
Defined.

Arguments updDyn {A Ref Model dec a} v x m.
Arguments deleteDyn {A Ref Model dec a} v m.

Instance empty_dynmap A Ref Model : Empty (@DynMap A Ref Model).
refine {| dynMap := fun _ => None; dynMap_dom := nil |}.
- intros; auto.
- abstract (intros; split; try inversion 1; congruence).
- econstructor.
Defined.

Global Instance DynMap_equiv A (Ref Model: A → Type) : Equiv (DynMap Ref Model) := λ m m',
  ∀ a (r: Ref a), getDyn m r = getDyn m' r.

Global Instance getDyn_Proper A (Ref Model: A → Type) :
  Proper (equiv ==> forall_relation (λ a : A, pointwise_relation (Ref a) eq))
         (@getDyn A Ref Model).
Proof. intros m1 m2 Hequiv. eauto. Qed.

Global Instance DynMap_equivalence A (Ref Model: A → Type):
  Equivalence (@equiv (DynMap Ref Model) (@DynMap_equiv _ Ref Model)).
Proof.
  split.
  - intros m a r; eauto.
  - intros m1 m2 a r; eauto.
  - intros m1 m2 m3 ?? a r. etransitivity; eauto.
Qed.

Lemma getDyn_deleteDyn A (Ref Model: A -> Type) {dec: EqualDec (sigT Ref)}
      (m: DynMap Ref Model) a (r: Ref a) :
  getDyn (deleteDyn r m) r = None.
Proof.
  intros.
  unfold getDyn, deleteDyn. destruct m as [map wf]. simpl.
  destruct (equal); [| congruence]; eauto.
Qed.

Lemma getDyn_deleteDyn_ne1 A (Ref Model: A -> Type) {dec: EqualDec (sigT Ref)}
      (m: DynMap Ref Model) a (r1: Ref a) (r2: sigT Ref) :
  ~ (existT _ r1 = r2) ->
  getDyn (deleteDyn r1 m) (projT2 r2) = getDyn m (projT2 r2).
Proof.
  unfold getDyn, deleteDyn; simpl. destruct equal; [| by congruence].
  intros. exfalso. destruct r2. simpl in *. inversion e; subst.
  apply Eqdep.EqdepTheory.inj_pair2 in e; subst. intuition.
Qed.

Lemma getDyn_deleteDyn_ne2 A (Ref Model: A -> Type) {dec: EqualDec (sigT Ref)}
      (m: DynMap Ref Model) a (r1 r2: Ref a) :
  ~ (r1 = r2) ->
  getDyn (deleteDyn r1 m) r2 =
  getDyn m r2.
Proof.
  replace r2 with (projT2 (existT _ r2)) by auto.
  intros. apply (getDyn_deleteDyn_ne1 _ (r2 := (existT a r2))).
  intros Heq. apply Eqdep.EqdepTheory.inj_pair2 in Heq; subst. intuition.
Qed.

Lemma updDyn_deleteDyn A (Ref Model: A -> Type) {dec: EqualDec (sigT Ref)}
      (m: DynMap Ref Model) a (r: Ref a) x:
  updDyn r x (deleteDyn r m) ≡ updDyn r x m.
Proof.
  intros a' r'.
  unfold getDyn, updDyn, deleteDyn; simpl.
  destruct (equal); eauto.
Qed.

Lemma getDyn_updDyn A (Ref Model: A -> Type) {dec: EqualDec (sigT Ref)}
      (m: DynMap Ref Model) a x (r: Ref a) :
  getDyn (updDyn r x m) r = Some x.
Proof.
  unfold getDyn, updDyn; simpl. destruct equal; [| by congruence].
  f_equal. rewrite <-Eqdep.Eq_rect_eq.eq_rect_eq; auto.
Qed.

Lemma getDyn_updDyn_ne1 A (Ref Model: A -> Type) {dec: EqualDec (sigT Ref)}
      (m: DynMap Ref Model) a x (r1: Ref a) (r2: sigT Ref) :
  ~ (existT _ r1 = r2) ->
  getDyn (updDyn r1 x m) (projT2 r2) = getDyn m (projT2 r2).
Proof.
  unfold getDyn, updDyn; simpl. destruct equal; [| by congruence].
  intros. exfalso. destruct r2. simpl in *. inversion e; subst.
  apply Eqdep.EqdepTheory.inj_pair2 in e; subst. intuition.
Qed.

Lemma getDyn_updDyn_ne2 A (Ref Model: A -> Type) {dec: EqualDec (sigT Ref)}
      (m: DynMap Ref Model) a x (r1 r2: Ref a) :
  ~ (r1 = r2) ->
  getDyn (updDyn r1 x m) r2 = getDyn m r2.
Proof.
  replace r2 with (projT2 (existT _ r2)) by auto.
  intros. apply (getDyn_updDyn_ne1 _ _ (r2 := (existT a r2))).
  intros Heq. apply Eqdep.EqdepTheory.inj_pair2 in Heq; subst. intuition.
Qed.

Global Instance updDyn_Proper A (Ref Model: A → Type) {dec: EqualDec (sigT Ref)}
       a (r: Ref a) (x: Model a):
  Proper (equiv ==> equiv) (updDyn r x).
Proof.
  intros m1 m2 Hequiv a' r'.
  destruct (dec (existT _ r) (existT _ r')).
  - inversion e. subst.
    apply Eqdep.EqdepTheory.inj_pair2 in e; subst.
    by rewrite ?getDyn_updDyn.
  - rewrite ?(getDyn_updDyn_ne1 _ _ (r2 := existT a' r')); eauto.
Qed.

Global Instance deleteDyn_Proper A (Ref Model: A → Type) {dec: EqualDec (sigT Ref)}
       a (r: Ref a):
  Proper (equiv ==> equiv) (deleteDyn (Model := Model) r).
Proof.
  intros m1 m2 Hequiv a' r'.
  destruct (dec (existT _ r) (existT _ r')).
  - inversion e. subst.
    apply Eqdep.EqdepTheory.inj_pair2 in e; subst.
    by rewrite ?getDyn_deleteDyn.
  - rewrite ?(getDyn_deleteDyn_ne1 _ (r2 := existT a' r')); eauto.
Qed.

Lemma updDyn_identity A (Ref Model: A -> Type) {dec: EqualDec (sigT Ref)}
      (m: DynMap Ref Model) a (r: Ref a) x:
  getDyn m r = Some x →
  updDyn r x m ≡ m.
Proof.
  intros Hlookup a' r'.
  destruct (dec (existT _ r) (existT _ r')).
  * inversion e; subst. apply Eqdep.EqdepTheory.inj_pair2 in e; subst.
    by rewrite getDyn_updDyn.
  * replace r' with (projT2 (existT _ r')) by auto.
    rewrite (getDyn_updDyn_ne1 _ _ (r2 := existT a' r')); eauto.
Qed.

Lemma dynMap_dom_spec' A (Ref Model: A -> Type)
      (m: DynMap Ref Model) a (x: Ref a):
  getDyn m x <> None <-> existT _ x ∈ dynMap_dom m.
Proof. by rewrite <-dynMap_dom_spec, getDyn_lookup_none. Qed.

Lemma dynMap_dom_non_spec A (Ref Model: A -> Type)
      (m: DynMap Ref Model) a (x: Ref a):
  getDyn m x = None <-> ¬ existT _ x ∈ dynMap_dom m.
Proof.
  rewrite <-dynMap_dom_spec'. destruct getDyn; auto; split; firstorder.
Qed.

Lemma dynMap_equiv_perm_dom A (Ref Model: A -> Type)
      (m1 m2: DynMap Ref Model):
  m1 ≡ m2 →
  dynMap_dom m1 ≡ₚ dynMap_dom m2.
Proof.
  intros Hequiv.
  apply NoDup_Permutation; eauto using dynMap_dom_nodup.
  intros (a&x). by rewrite <-?dynMap_dom_spec', Hequiv.
Qed.

Global Instance dynMap_dom_Proper A (Ref Model: A → Type) :
  Proper (equiv ==> (≡ₚ)) (@dynMap_dom A Ref Model).
Proof. intros m1 m2 Hequiv. eapply dynMap_equiv_perm_dom; eauto. Qed.

Lemma dynMap_dom_empty_iff A (Ref Model: A -> Type)
      (m: DynMap Ref Model):
  m ≡ ∅ <-> dynMap_dom m = [].
Proof.
  split.
  - intros Hequiv. apply Permutation_nil. rewrite Hequiv; eauto.
  - intros Hdom a k. unfold getDyn at 2; simpl. rewrite dynMap_dom_non_spec, Hdom.
    inversion 1.
Qed.

Lemma dynMap_dom_lookup A (Ref Model: A -> Type)
      (m: DynMap Ref Model) (k : nat) (y : {a : A & Ref a}):
  m.(dynMap_dom) !! k = Some y ->
  exists v, getDyn m (projT2 y) = Some v.
Proof.
  intros Hin%elem_of_list_lookup_2.
  replace y with (existT _ (projT2 y)) in Hin by (destruct y; eauto).
  rewrite <-dynMap_dom_spec' in Hin.
  destruct getDyn as [?|] eqn:Heq; eauto; congruence.
Qed.
