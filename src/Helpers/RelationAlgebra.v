Require Import Helpers.Instances.
Require Import Helpers.Helpers.
Require Import Morphisms.

Set Implicit Arguments.
Generalizable All Variables.

Section OutputRelations.

  Context (A:Type).

  (* an output relation: a homogenous relation over A that also emits some value
  of type [T] *)
  Definition relation T := A -> A -> T -> Prop.

  (** Several operations on relations *)
  Definition and_then {T1 T2} (r1: relation T1) (r2: T1 -> relation T2) :
    relation T2 :=
    fun x z o2 => exists o1 y, r1 x y o1 /\ (r2 o1) y z o2.

  Notation "p1 ;; p2" := (and_then p1 (fun _ => p2))
                           (at level 55, p2 at next level, right associativity).
  Notation "x <- p1 ; p2" := (and_then p1 (fun x => p2))
                               (at level 54, right associativity).

  Definition pure T (o0:T) : relation T :=
    fun x y o => x = y /\ o = o0.

  Definition identity {T} : relation T :=
    fun x y o => x = y.

  Definition rel_or T (r1 r2: relation T) : relation T :=
    fun x y o => r1 x y o \/ r2 x y o.

  Infix "+" := rel_or.

  Inductive seq_star `(r: relation T) : relation T :=
  | seq_star_refl : forall x o,
      seq_star r x x o
  | seq_star_one_more : forall x y z o1 o2,
      r x y o1 ->
      seq_star r y z o2 ->
      seq_star r x z o2
  .

  Inductive bind_star `(r: T -> relation T) : T -> relation T :=
  | bind_star_pure : forall (o:T) x,
      bind_star r o x x o
  | bind_star_one_more : forall (o1:T) x y z o2 o3,
      r o1 x y o2 ->
      bind_star r o2 y z o3 ->
      bind_star r o1 x z o3
  .

  (** Notions of equivalence and implication *)

  Definition rimpl {T} (r1 r2: relation T) :=
    forall x y o, r1 x y o -> r2 x y o.

  Global Instance rimpl_preorder T : PreOrder (rimpl (T:=T)) :=
    ltac:(firstorder).

  Definition requiv {T} (r1 r2: relation T) :=
    forall x y o, r1 x y o <-> r2 x y o.

  Global Instance requiv_equivalence : Equivalence (requiv (T:=T)) :=
    RelInstance.

  Infix "--->" := rimpl (at level 60, no associativity).
  Infix "<--->" := requiv (at level 60, no associativity).

  Global Instance rimpl_requiv_sub : subrelation (requiv (T:=T)) rimpl :=
    ltac:(firstorder).

  Theorem rimpl_to_requiv T (r1 r2: relation T) :
    r1 ---> r2 ->
    r2 ---> r1 ->
    r1 <---> r2.
  Proof.
    firstorder.
  Qed.

  Theorem rimpl_or T (r1 r2: relation T) :
    r1 ---> r2 ->
    r1 + r2 <---> r2.
  Proof.
    firstorder.
  Qed.

  (** Various equivalence and implication proofs *)
  Hint Unfold Proper respectful pointwise_relation : t.
  Hint Unfold Basics.flip Basics.impl : t.
  Hint Unfold and_then rel_or pure identity : t.

  Ltac t :=
    autounfold with t;
    repeat match goal with
           | |- _ <---> _ => split
           | |- _ ---> _ => unfold "--->"
           | [ H: ?r <---> _,
                  H': ?r ?x ?y ?o |- _ ] =>
             add_hypothesis (proj1 (H x y o) H')
           | [ H: _ <---> ?r,
                  H': ?r ?x ?y ?o |- _ ] =>
             add_hypothesis (proj2 (H x y o) H')
           | [ H: ?r ---> _,
                  H': ?r ?x ?y ?o |- _ ] =>
             add_hypothesis (H x y o H')
           | _ => progress propositional
           | _ => solve [ eauto 10 ]
           | [ H: _ \/ _  |- _ ] => destruct H
        end.


  (* first some respectful/congruence rules *)
  Global Instance or_respects_equiv :
    Proper (requiv ==> requiv ==> requiv) (rel_or (T:=T)).
  Proof.
    t.
  Qed.

  Global Instance or_respects_impl :
    Proper (rimpl ==> rimpl ==> rimpl) (rel_or (T:=T)).
  Proof.
    t.
  Qed.

  Theorem and_then_monotonic T1 T2 (r1 r1': relation T1) (r2 r2': T1 -> relation T2) :
    r1 ---> r1' ->
    (forall x, r2 x ---> r2' x) ->
    and_then r1 r2 ---> and_then r1' r2'.
  Proof.
    t.
    specialize (H0 o1); t.
  Qed.

  Global Instance and_then_respectful :
    Proper (rimpl ==> pointwise_relation _ rimpl ==> rimpl) (and_then (T1:=T1) (T2:=T2)).
  Proof.
    unfold Proper, "==>"; intros.
    apply and_then_monotonic; auto.
  Qed.

  Theorem and_then_equiv_cong T1 T2 (r1 r1': relation T1) (r2 r2': T1 -> relation T2) :
    r1 <---> r1' ->
    (forall x, r2 x <---> r2' x) ->
    and_then r1 r2 <---> and_then r1' r2'.
  Proof.
    t.
    specialize (H0 o1); t.
    specialize (H0 o1); t.
  Qed.

  Theorem bind_identity1 T1 T2 (r: relation T2) :
    (_ <- identity (T:=T1); r) ---> r.
  Proof.
    t.
  Qed.

  Theorem bind_identity T1 T2 (r: relation T2) (_:Inhabited T1) :
    (_ <- identity (T:=T1); r) <---> r.
  Proof.
    t.
  Qed.

  Global Instance and_then_respectful_equiv :
    Proper (requiv ==> pointwise_relation _ requiv ==> requiv) (and_then (T1:=T1) (T2:=T2)).
  Proof.
    unfold Proper, "==>"; intros.
    apply and_then_equiv_cong; auto.
  Qed.

  Hint Constructors seq_star.

  Global Instance seq_star_respectful T :
    Proper (rimpl ==> rimpl) (seq_star (T:=T)).
  Proof.
    t.
    induction H0; eauto.
  Qed.

  Hint Constructors bind_star.

  Global Instance bind_star_respectful T :
    Proper (pointwise_relation _ rimpl ==> pointwise_relation _ rimpl) (bind_star (T:=T)).
  Proof.
    t.
    induction H0; eauto.
    specialize (H o1); eauto.
  Qed.

  Theorem and_then_monotonic_r T1 T2 (r1 r2: relation T1) (rx: T1 -> relation T2) :
    r1 ---> r2 ->
    and_then r1 rx ---> and_then r2 rx.
  Proof.
    intros.
    rewrite H; reflexivity.
  Qed.

  Theorem rel_or_symmetric T (r1 r2: relation T) :
    r1 + r2 <---> r2 + r1.
  Proof.
    t.
  Qed.

  Theorem rel_or_assoc T (r1 r2 r3: relation T) :
    r1 + (r2 + r3) <---> r1 + r2 + r3.
  Proof.
    t.
  Qed.

  Theorem rel_or_monotonic T (r1 r2: relation T) r :
    r1 ---> r2 ->
    r1 + r ---> r2 + r.
  Proof.
    t.
  Qed.

  Theorem rel_or_introl T (r1 r2: relation T) :
    r1 ---> r1 + r2.
  Proof.
    t.
  Qed.

  Theorem rel_or_intror T (r1 r2: relation T) :
    r2 ---> r1 + r2.
  Proof.
    t.
  Qed.

  Theorem rel_or_elim T (r1 r2: relation T) r :
    r1 ---> r ->
    r2 ---> r ->
    r1 + r2 ---> r.
  Proof.
    t.
  Qed.

  Theorem bind_left_id T1 T2 (v:T1) (r: T1 -> relation T2) :
    and_then (pure v) r <---> r v.
  Proof.
    t.
  Qed.

  Theorem bind_assoc T1 T2 T3
          (r1: relation T1)
          (r2: T1 -> relation T2)
          (r3: T2 -> relation T3) :
    and_then (and_then r1 r2) r3 <--->
             and_then r1 (fun v => and_then (r2 v) r3).
  Proof.
    t.
  Qed.

  Theorem seq_star_to_bind_star : forall (r: relation unit),
      seq_star r <---> bind_star (fun _ => r) tt.
  Proof.
    t.
    - induction H;
        repeat match goal with
               | [ u: unit |- _ ] => destruct u
               end; eauto.
    - induction H; intros; subst;
        repeat match goal with
               | [ u: unit |- _ ] => destruct u
               end; eauto.
  Qed.

  Lemma bind_star_fun_ext T (r r': T -> relation T) (init: T) :
    (forall x, r x <---> r' x) ->
    bind_star r init <---> bind_star r' init.
  Proof.
    t.
    - induction H0; eauto.
      specialize (H o1); t.
    - induction H0; eauto.
      specialize (H o1); t.
  Qed.

  Theorem bind_star_unit : forall (r: unit -> relation unit) u,
      bind_star r u <---> seq_star (r tt).
  Proof.
    intros.
    destruct u.
    rewrite seq_star_to_bind_star.
    apply bind_star_fun_ext; intros.
    destruct x; reflexivity.
  Qed.

  Global Instance rimpl_equiv_proper T (r: relation T) :
    Proper (requiv ==> Basics.flip Basics.impl) (rimpl r).
  Proof.
    t.
  Qed.

  Definition rimpl_refl T (r: relation T) : r ---> r := ltac:(reflexivity).
  Definition requiv_refl T (r: relation T) : r <---> r := ltac:(reflexivity).

  Hint Resolve rimpl_refl requiv_refl.

  Theorem bind_dist_r T1 T2 (r1 r2: relation T1) (r3: T1 -> relation T2) :
    and_then (r1 + r2) r3 <---> (and_then r1 r3) + (and_then r2 r3).
  Proof.
    t.
  Qed.

  Theorem bind_dist_l T1 T2 (r1: relation T1) (r2 r3: T1 -> relation T2) :
    and_then r1 (fun v => r2 v + r3 v) <---> and_then r1 r2 + and_then r1 r3.
  Proof.
    t.
  Qed.

  Theorem star_ind T (r x: relation T) :
    identity ---> x ->
    r;; x ---> x ->
    seq_star r ---> x.
  Proof.
    t.
    induction H1; eauto.
  Qed.

  Theorem star_expand T (r: relation T) :
    seq_star r <---> identity + (r;; seq_star r).
  Proof.
    apply rimpl_to_requiv.
    - apply star_ind; t.
    - t.
  Qed.

  Global Instance and_then_pointwise T1 T2 (r: relation T1) :
    Proper (pointwise_relation _ (Basics.flip rimpl) ==> Basics.flip (rimpl (T:=T2)))
           (and_then r).
  Proof.
    t.
    specialize (H o1); t.
  Qed.

  Theorem star_duplicate T (r: relation T) :
    seq_star r <---> seq_star r;; seq_star r.
  Proof.
    t.
    induction H; t.
  Qed.

  Theorem star_one T (r: relation T) :
    r ---> seq_star r.
  Proof.
    t.
  Qed.

  Lemma star_monotonic T (r1 r2: relation T) :
    r1 ---> r2 ->
    seq_star r1 ---> seq_star r2.
  Proof.
    intros.
    rewrite H; reflexivity.
  Qed.

  Ltac cong :=
    let solver := try reflexivity; try solve [ t ] in
    match goal with
    | |- and_then _ _ ---> and_then _ _ =>
      apply and_then_monotonic; intros;
      solver
    | |- seq_star _ ---> seq_star _ =>
      apply star_monotonic;
      solver
    end.

  Theorem denesting T (r1 r2: relation T) :
    seq_star (r1 + r2) <--->
             seq_star r1;; (seq_star (r2;; seq_star r1)).
  Proof.
    apply rimpl_to_requiv.
    - apply star_ind; t.
    - setoid_rewrite star_duplicate at 4; cong.
      cong.

      apply star_ind; try solve [ t ].
      setoid_rewrite star_duplicate at 3; cong.

      setoid_rewrite star_duplicate at 2; cong.
      cong.

      Grab Existential Variables.
      all: trivial.
  Qed.

End OutputRelations.

Module RelationNotations.
Notation "r1 ---> r2" := (rimpl r1 r2)
                           (at level 60, no associativity, format "r1  '/' ---> '/'  r2").
Notation "r1 <---> r2" := (requiv r1 r2)
                           (at level 60, no associativity, format "r1  '/' <---> '/'  r2").
  Infix "+" := rel_or.

Notation "p1 ;; p2" := (and_then p1 (fun _ => p2))
                         (at level 55, right associativity).
Notation "x <- p1 ; p2" := (and_then p1 (fun x => p2))
                            (at level 54, right associativity,
                            format "x  <-  p1 ;  '/' p2").
End RelationNotations.

Ltac rel_congruence :=
  let solver := try reflexivity in
  match goal with
  | |- rimpl (and_then _ ?rx) (and_then _ ?rx) =>
    apply and_then_monotonic_r; intros;
    solver
  | |- rimpl (and_then _ _) (and_then _ _) =>
    apply and_then_monotonic; intros;
    solver
  | |- rimpl (seq_star _) (seq_star _) =>
    apply star_monotonic;
    solver
  end.
