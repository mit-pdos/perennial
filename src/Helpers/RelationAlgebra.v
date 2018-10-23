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

  Definition and_then {T1 T2} (r1: relation T1) (r2: T1 -> relation T2) :
    relation T2 :=
    fun x z o2 => exists o1 y, r1 x y o1 /\ (r2 o1) y z o2.

  Definition seq {T1 T2} (r1: relation T1) (r2: relation T2)
    : relation T2 :=
    and_then r1 (fun _ => r2).

  Definition fmap T1 T2 (f: T1 -> T2) (r:relation T1) : relation T2 :=
    fun x y o => exists o0, r x y o0 /\ o = f o0.

  Definition pure T (o0:T) : relation T :=
    fun x y o => x = y /\ o = o0.

  Definition map_out T1 T2 (f: T1 -> T2) : T1 -> relation T2 :=
    fun v => fmap f (pure v).

  Definition rel_or T (r1 r2: relation T) : relation T :=
    fun x y o => r1 x y o \/ r2 x y o.

  Inductive seq_star `(r: relation T) : relation T :=
  | seq_star_refl : forall x o,
      seq_star r x x o
  | seq_star_one_more : forall x y z o1 o2,
      r x y o1 ->
      seq_star r y z o2 ->
      seq_star r x z o2
  .

  Inductive bind_star `(r: T -> relation T) : T -> relation T :=
  | bind_star_pure : forall (o:T) x y,
      bind_star r o x y o
  | bind_star_one_more : forall (o1:T) x y z o2 o3,
      r o1 x y o2 ->
      bind_star r o2 y z o3 ->
      bind_star r o1 x z o3
  .

  Definition rimpl {T} (r1 r2: relation T) :=
    forall x y o, r1 x y o -> r2 x y o.

  Global Instance rimpl_preorder T : PreOrder (rimpl (T:=T)).
  Proof.
    unfold rimpl.
    RelInstance_t; eauto.
  Qed.

  Definition requiv {T} (r1 r2: relation T) :=
    forall x y o, r1 x y o <-> r2 x y o.

  Infix "--->" := rimpl (at level 40, no associativity).
  Infix "<--->" := requiv (at level 40, no associativity).

  Global Instance rimpl_requiv_sub : subrelation (requiv (T:=T)) rimpl :=
    ltac:(firstorder).

  Global Instance requiv_equivalence : Equivalence (requiv (T:=T)) :=
    RelInstance.

  Hint Unfold Proper respectful pointwise_relation : t.
  Hint Unfold seq and_then rel_or pure : t.

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
           | _ => eauto 10
        end.

  Global Instance seq_respects_equiv :
    Proper (requiv ==> requiv ==> requiv) (seq (T1:=T1) (T2:=T2)).
  Proof.
    t.
  Qed.

  Global Instance seq_respects_impl :
    Proper (rimpl ==> rimpl ==> rimpl) (seq (T1:=T1) (T2:=T2)).
  Proof.
    t.
  Qed.

  Global Instance or_respects_equiv :
    Proper (requiv ==> requiv ==> requiv) (rel_or (T:=T)).
  Proof.
    t.
    (intuition idtac); t.
    (intuition idtac); t.
  Qed.

  Global Instance or_respects_impl :
    Proper (rimpl ==> rimpl ==> rimpl) (rel_or (T:=T)).
  Proof.
    t.
    (intuition idtac); t.
  Qed.

  Theorem rel_or_introl T (r1 r2: relation T) :
    r1 ---> rel_or r1 r2.
  Proof.
    t.
  Qed.

  Theorem rel_or_intror T (r1 r2: relation T) :
    r2 ---> rel_or r1 r2.
  Proof.
    t.
  Qed.

  Theorem seq_assoc
          `(r1: relation T1)
          `(r2: relation T2)
          `(r3: relation T3) :
    seq (seq r1 r2) r3 <---> seq r1 (seq r2 r3).
  Proof.
    t.
  Qed.

  Theorem bind_left_id T1 T2 (v:T1) (r: T1 -> relation T2) :
    and_then (pure v) r <---> r v.
  Proof.
    t.
  Qed.

  Theorem seq_left_id T1 T2 (v:T1) (r: relation T2) :
    seq (pure v) r <---> r.
  Proof.
    unfold seq; apply bind_left_id.
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

  Theorem bind_seq_assoc T1 T2 T3
          (r1: relation T1)
          (r2: T1 -> relation T2)
          (r3: relation T3) :
    seq (and_then r1 r2) r3 <--->
             and_then r1 (fun v => seq (r2 v) r3).
  Proof.
    t.
  Qed.

  Theorem and_then_cong T1 T2 (r1 r1': relation T1) (r2 r2': T1 -> relation T2) :
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
    apply and_then_cong; auto.
  Qed.

  Definition rimpl_refl T (r: relation T) : r ---> r := ltac:(reflexivity).
  Definition requiv_refl T (r: relation T) : r <---> r := ltac:(reflexivity).

End OutputRelations.

Infix ";;" := seq (at level 21, left associativity).
