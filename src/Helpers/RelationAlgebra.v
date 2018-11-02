Require Import Setoid.
Require Import Morphisms.

Require Import Tactical.Propositional.
Require Import Tactical.Misc.
Require Import Helpers.Instances.

Set Implicit Arguments.
Generalizable All Variables.

Section OutputRelations.

  (* an output relation: a heterogeneous relation from [A] to [B] that also
  emits some value of type [T] *)
  Definition relation A B T := A -> B -> T -> Prop.

  (** Several operations on relations *)
  Definition and_then {A B C} {T1 T2}
             (r1: relation A B T1)
             (r2: T1 -> relation B C T2) :
    relation A C T2 :=
    fun x z o2 => exists o1 y, r1 x y o1 /\ (r2 o1) y z o2.

  Notation "p1 ;; p2" := (and_then p1 (fun _ => p2))
                           (at level 55, p2 at next level, right associativity).
  Notation "x <- p1 ; p2" := (and_then p1 (fun x => p2))
                               (at level 54, right associativity).

  Definition pure A T (o0:T) : relation A A T :=
    fun x y o => x = y /\ o = o0.

  Definition identity {A} {T} : relation A A T :=
    fun x y o => x = y.

  Definition any {A B} {T} : relation A B T :=
    fun x y o => True.

  Definition reads {A} {T} (f: A -> T) : relation A A T :=
    fun x y o => o = f x /\ x = y.

  Definition puts {A} (f: A -> A) : relation A A unit :=
    fun x y o => y = f x.

  Definition predicate A := A -> Prop.
  Definition test {A} (P: predicate A) : relation A A unit :=
    fun x y _ => P x /\ x = y.

  Definition rel_or A B T (r1 r2: relation A B T) : relation A B T :=
    fun x y o => r1 x y o \/ r2 x y o.

  Definition rel_and A B T (r1 r2: relation A B T) : relation A B T :=
    fun x y o => r1 x y o /\ r2 x y o.

  Infix "+" := rel_or.
  Infix "∩" := (rel_and) (at level 50).

  Inductive seq_star A `(r: relation A A T) : relation A A T :=
  | seq_star_refl : forall x o,
      seq_star r x x o
  | seq_star_one_more : forall x y z o1 o2,
      r x y o1 ->
      seq_star r y z o2 ->
      (* TODO: rewrite to return the value from the last iteration *)
      seq_star r x z o2
  .

  Inductive bind_star A `(r: T -> relation A A T) : T -> relation A A T :=
  | bind_star_pure : forall (o:T) x,
      bind_star r o x x o
  | bind_star_one_more : forall (o1:T) x y z o2 o3,
      r o1 x y o2 ->
      bind_star r o2 y z o3 ->
      bind_star r o1 x z o3
  .

  (** Notions of equivalence and implication *)

  Definition rimpl {A B} {T} (r1 r2: relation A B T) :=
    forall x y o, r1 x y o -> r2 x y o.

  Global Instance rimpl_preorder T : PreOrder (rimpl (A:=A) (B:=B) (T:=T)) :=
    ltac:(firstorder).

  Definition requiv {A B} {T} (r1 r2: relation A B T) :=
    forall x y o, r1 x y o <-> r2 x y o.

  Global Instance requiv_equivalence : Equivalence (requiv (A:=A) (B:=B) (T:=T)) :=
    RelInstance.

  Infix "--->" := rimpl (at level 60, no associativity).
  Infix "<--->" := requiv (at level 60, no associativity).

  Global Instance rimpl_requiv_sub : subrelation (requiv (A:=A) (B:=B) (T:=T)) rimpl :=
    ltac:(firstorder).

  Global Instance rimpl_proper_basics_flip A B T (r: relation A B T) :
    Proper
      (Basics.flip rimpl ==> Basics.flip Basics.impl) (rimpl r) :=
    ltac:(firstorder).

  Theorem rimpl_to_requiv A B T (r1 r2: relation A B T) :
    r1 ---> r2 ->
    r2 ---> r1 ->
    r1 <---> r2.
  Proof.
    firstorder.
  Qed.

  Theorem requiv_to_rimpl1 A B T (r1 r2: relation A B T) :
    r1 <---> r2 ->
    r1 ---> r2.
  Proof.
    firstorder.
  Qed.

  Theorem requiv_to_rimpl2 A B T (r1 r2: relation A B T) :
    r1 <---> r2 ->
    r2 ---> r1.
  Proof.
    firstorder.
  Qed.

  Theorem requiv_to_rimpls A B T (r1 r2: relation A B T) :
    r1 <---> r2 ->
    r1 ---> r2 /\ r2 ---> r1.
  Proof.
    firstorder.
  Qed.

  Hint Immediate rimpl_to_requiv requiv_to_rimpl1 requiv_to_rimpl2.

  Theorem rimpl_or A B T (r1 r2: relation A B T) :
    r1 ---> r2 ->
    r1 + r2 <---> r2.
  Proof.
    firstorder.
  Qed.

  Theorem rel_forall_intro A B T X (r : relation A B T) (rpred: X -> relation A B T) :
    (forall x, r ---> (rpred x)) ->
    r ---> (fun a b t => forall x, rpred x a b t).
  Proof.
    firstorder.
  Qed.

  (** Various equivalence and implication proofs *)
  Hint Unfold Proper respectful pointwise_relation : t.
  Hint Unfold Basics.flip Basics.impl : t.
  Hint Unfold and_then rel_or rel_and pure any identity reads : t.

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
           | [ u: unit |- _ ] => destruct u
           | [ |- exists (_:unit), _ ] => exists tt
           | _ => progress propositional
           | _ => solve [ eauto 10 ]
           | [ H: _ \/ _  |- _ ] => destruct H
        end.


  (* first some respectful/congruence rules *)
  Global Instance or_respects_equiv :
    Proper (requiv ==> requiv ==> requiv) (rel_or (A:=A) (B:=B) (T:=T)).
  Proof.
    t.
  Qed.

  Global Instance or_respects_impl :
    Proper (rimpl ==> rimpl ==> rimpl) (rel_or (A:=A) (B:=B) (T:=T)).
  Proof.
    t.
  Qed.

  Theorem and_then_monotonic A B C T1 T2
          (r1 r1': relation A B T1) (r2 r2': T1 -> relation B C T2) :
    r1 ---> r1' ->
    (forall x, r2 x ---> r2' x) ->
    and_then r1 r2 ---> and_then r1' r2'.
  Proof.
    t.
    specialize (H0 o1); t.
  Qed.

  Theorem and_then_monotonic_wit A B C T1 T2
          (r1 r1': relation A B T1) (r2 r2': T1 -> relation B C T2) :
    r1 ---> r1' ->
    (forall a b x, r1 a b x -> (r2 x ---> r2' x)) ->
    and_then r1 r2 ---> and_then r1' r2'.
  Proof.
    t.
    specialize (H0 x y0 o1) as H0.
    t.
  Qed.

  Global Instance and_then_respectful :
    Proper (rimpl ==> pointwise_relation _ rimpl ==> rimpl) (and_then (A:=A) (B:=B) (C:=C) (T1:=T1) (T2:=T2)).
  Proof.
    unfold Proper, "==>"; intros.
    apply and_then_monotonic; auto.
  Qed.

  Theorem and_then_equiv_cong A B C T1 T2
          (r1 r1': relation A B T1)
          (r2 r2': T1 -> relation B C T2) :
    r1 <---> r1' ->
    (forall x, r2 x <---> r2' x) ->
    and_then r1 r2 <---> and_then r1' r2'.
  Proof.
    t.
    specialize (H0 o1); t.
    specialize (H0 o1); t.
  Qed.

  Theorem bind_identity1 A B T1 T2 (r: relation A B T2) :
    (_ <- identity (T:=T1); r) ---> r.
  Proof.
    t.
  Qed.

  Theorem bind_identity A B T1 T2 (r: relation A B T2) (_:Inhabited T1) :
    (_ <- identity (T:=T1); r) <---> r.
  Proof.
    t.
  Qed.

  Theorem reads_identity A T (f: A -> T) :
    reads f ---> identity.
  Proof.
    t.
  Qed.

  Global Instance and_then_respectful_equiv :
    Proper (requiv ==> pointwise_relation _ requiv ==> requiv) (and_then (A:=A) (B:=B) (C:=C) (T1:=T1) (T2:=T2)).
  Proof.
    unfold Proper, "==>"; intros.
    apply and_then_equiv_cong; auto.
  Qed.

  Hint Constructors seq_star.

  Global Instance seq_star_respectful :
    Proper (rimpl ==> rimpl) (seq_star (A:=A) (T:=T)).
  Proof.
    t.
    induction H0; eauto.
  Qed.

  Global Instance seq_star_equiv_respectful :
    Proper (requiv ==> requiv) (seq_star (A:=A) (T:=T)).
  Proof.
    t.
    eapply seq_star_respectful; eauto.
    eapply seq_star_respectful; eauto.
  Qed.

  Hint Constructors bind_star.

  Global Instance bind_star_respectful :
    Proper (pointwise_relation _ rimpl ==> eq ==> rimpl) (bind_star (A:=A) (T:=T)).
  Proof.
    t.
    induction H0; eauto.
    specialize (H o1); eauto.
  Qed.

  Theorem and_then_monotonic_r A B C T1 T2
          (r1 r2: relation A B T1) (rx: T1 -> relation B C T2) :
    r1 ---> r2 ->
    and_then r1 rx ---> and_then r2 rx.
  Proof.
    intros.
    rewrite H; reflexivity.
  Qed.

  Theorem rel_and_symmetric A B T (r1 r2: relation A B T) :
    r1 ∩ r2 <---> r2 ∩ r1.
  Proof.
    t.
  Qed.

  Theorem rel_and_assoc A B T (r1 r2 r3: relation A B T) :
    r1 ∩ (r2 ∩ r3) <---> r1 ∩ r2 ∩ r3.
  Proof.
    t.
  Qed.

  Theorem rel_and_monotonic A B T (r1 r2: relation A B T) r :
    r1 ---> r2 ->
    r1 ∩ r ---> r2 ∩ r.
  Proof.
    t.
  Qed.

  Theorem rel_and_intro A B T r (r1 r2: relation A B T) :
    r ---> r1 ->
    r ---> r2 ->
    r ---> r1 ∩ r2.
  Proof.
    t.
  Qed.

  Theorem rel_and_eliml A B T (r1 r2: relation A B T) :
    r1 ∩ r2 ---> r1.
  Proof.
    t.
  Qed.

  Theorem rel_and_elimr A B T (r1 r2: relation A B T) :
    r1 ∩ r2 ---> r2.
  Proof.
    t.
  Qed.

  Theorem rel_or_symmetric A B T (r1 r2: relation A B T) :
    r1 + r2 <---> r2 + r1.
  Proof.
    t.
  Qed.

  Theorem rel_or_assoc A B T (r1 r2 r3: relation A B T) :
    r1 + (r2 + r3) <---> r1 + r2 + r3.
  Proof.
    t.
  Qed.

  Theorem rel_or_idem A B T (r: relation A B T) :
    r + r <---> r.
  Proof.
    t.
  Qed.

  Theorem rel_or_monotonic A B T (r1 r2: relation A B T) r :
    r1 ---> r2 ->
    r1 + r ---> r2 + r.
  Proof.
    t.
  Qed.

  Theorem rel_or_introl A B T (r1 r2: relation A B T) :
    r1 ---> r1 + r2.
  Proof.
    t.
  Qed.

  Theorem rel_or_intror A B T (r1 r2: relation A B T) :
    r2 ---> r1 + r2.
  Proof.
    t.
  Qed.

  Theorem rel_or_elim A B T (r1 r2: relation A B T) r :
    r1 ---> r ->
    r2 ---> r ->
    r1 + r2 ---> r.
  Proof.
    t.
  Qed.

  Theorem rel_or_elim_rx A B T (r1 r2: relation A B T)
          C T' (rx: T -> relation B C T') r :
    and_then r1 rx ---> r ->
    and_then r2 rx ---> r ->
    and_then (r1 + r2) rx ---> r.
  Proof.
    t.
  Qed.

  Theorem bind_left_id A B T1 T2 (v:T1) (r: T1 -> relation A B T2) :
    and_then (pure v) r <---> r v.
  Proof.
    t.
  Qed.

  Theorem bind_right_id A T (r: relation A A T) :
    and_then r (@pure A T) <---> r.
  Proof.
    t.
  Qed.

  Theorem bind_right_id_unit A (r: relation A A unit) :
    and_then r (fun _ => pure tt) <---> r.
  Proof.
    t.
  Qed.

  Theorem bind_assoc
          A B C D
          T1 T2 T3
          (r1: relation A B T1)
          (r2: T1 -> relation B C T2)
          (r3: T2 -> relation C D T3) :
    and_then (and_then r1 r2) r3 <--->
             and_then r1 (fun v => and_then (r2 v) r3).
  Proof.
    t.
  Qed.

  Theorem to_any A B T (r: relation A B T) :
    r ---> any.
  Proof.
    t.
  Qed.

  Theorem identity_to_any A :
    pure tt ---> any (A:=A).
  Proof.
    t.
  Qed.

  Theorem any_idem A B C T1 T2 :
    any (B:=B) (T:=T1);; any --->
        any (A:=A) (B:=C) (T:=T2).
  Proof.
    t.
  Qed.

  Theorem seq_star_to_bind_star : forall A (r: relation A A unit),
      seq_star r <---> bind_star (fun _ => r) tt.
  Proof.
    t.
    - induction H; t.
    - induction H; t.
  Qed.

  Lemma bind_star_fun_ext A T (r r': T -> relation A A T) (init: T) :
    (forall x, r x <---> r' x) ->
    bind_star r init <---> bind_star r' init.
  Proof.
    t.
    - induction H0; eauto.
      specialize (H o1); t.
    - induction H0; eauto.
      specialize (H o1); t.
  Qed.

  Theorem bind_star_unit A (r: unit -> relation A A unit) u :
      bind_star r u <---> seq_star (r tt).
  Proof.
    intros.
    destruct u.
    rewrite seq_star_to_bind_star.
    apply bind_star_fun_ext; intros.
    destruct x; reflexivity.
  Qed.

  Global Instance rimpl_equiv_proper A B T (r: relation A B T) :
    Proper (requiv ==> Basics.flip Basics.impl) (rimpl r).
  Proof.
    t.
  Qed.

  Global Instance rimpl_equiv_applied_proper A B T :
    Proper (requiv ==> requiv ==> iff) (rimpl (A:=A) (B:=B) (T:=T)).
  Proof.
    t.
    split; t.
  Qed.

  Definition rimpl_refl A B T (r: relation A B T) : r ---> r := ltac:(reflexivity).
  Definition requiv_refl A B T (r: relation A B T) : r <---> r := ltac:(reflexivity).

  Hint Resolve rimpl_refl requiv_refl.

  Theorem bind_dist_r A B C T1 T2 (r1 r2: relation A B T1) (r3: T1 -> relation B C T2) :
    and_then (r1 + r2) r3 <---> (and_then r1 r3) + (and_then r2 r3).
  Proof.
    t.
  Qed.

  Theorem bind_dist_l A B C T1 T2 (r1: relation A B T1) (r2 r3: T1 -> relation B C T2) :
    and_then r1 (fun v => r2 v + r3 v) <---> and_then r1 r2 + and_then r1 r3.
  Proof.
    t.
  Qed.

  Theorem star_ind A T (r x: relation A A T) :
    identity ---> x ->
    r;; x ---> x ->
    seq_star r ---> x.
  Proof.
    t.
    induction H1; eauto.
  Qed.

  Theorem star_expand A T (r: relation A A T) :
    seq_star r <---> identity + (r;; seq_star r).
  Proof.
    apply rimpl_to_requiv.
    - apply star_ind; t.
    - t.
  Qed.

  Theorem seq_star1 A T (r: relation A A T) :
    r;; seq_star r ---> seq_star r.
  Proof.
    t.
  Qed.

  Theorem seq_star_fold A T (r r': relation A A T) :
    r' ---> r ->
    r';; seq_star r ---> seq_star r.
  Proof.
    t.
  Qed.

  Theorem seq_star_none A T (r: relation A A T) :
    identity ---> seq_star r.
  Proof.
    t.
  Qed.

  Theorem seq_star_one A T (r: relation A A T) :
    r ---> seq_star r.
  Proof.
    t.
  Qed.

  Global Instance and_then_pointwise A B C T1 T2 (r: relation A B T1) :
    Proper (pointwise_relation _ (Basics.flip rimpl) ==> Basics.flip (rimpl (B:=C) (T:=T2)))
           (and_then r).
  Proof.
    t.
    specialize (H o1); t.
  Qed.

  Theorem star_duplicate A T (r: relation A A T) :
    seq_star r <---> seq_star r;; seq_star r.
  Proof.
    t.
    induction H; t.
  Qed.

  Theorem star_one A T (r: relation A A T) :
    r ---> seq_star r.
  Proof.
    t.
  Qed.

  Lemma star_monotonic A T (r1 r2: relation A A T) :
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

  Theorem denesting A T (r1 r2: relation A A T) :
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

  Theorem bind_sliding A T1 (p: relation A A T1) (q: T1 -> relation A A unit) :
    seq_star (and_then p q);; p <--->
             v <- p; bind_star (fun v0 => q v0;; p) v.
  Proof.
    apply rimpl_to_requiv.
    - t.
      gen y.
      induction H; t.
      specialize (IHseq_star _ ltac:(eauto)); t.
    - t.
      gen x.
      induction H0; t.
      specialize (IHbind_star _ ltac:(eauto)); t.
  Qed.

  Theorem seq_sliding A T1 (p: relation A A T1) (q: relation A A unit) :
    seq_star (p;; q);; p --->
             p;; seq_star (q;; p).
  Proof.
    t.
    gen y.
    induction H; t.
    specialize (IHseq_star _ ltac:(eauto)); t.
  Qed.

  Theorem seq_unit_sliding A (p: relation A A unit) (q: relation A A unit) :
    p;; seq_star (q;; p) --->
     seq_star (p;; q);; p.
  Proof.
    t.
    gen x.
    induction H0; t.
    specialize (IHseq_star _ ltac:(eauto)); t.
  Qed.

  Theorem bind_unit A B C T (p: relation A B unit) (q: unit -> relation B C T) :
    and_then p q <---> p;; q tt.
  Proof.
    t.
  Qed.

  Inductive seq_star_r A `(r: relation A A T) : relation A A T :=
  | seq_star_r_refl : forall x o,
      seq_star_r r x x o
  | seq_star_r_one_more : forall x y z o1 o2,
      seq_star_r r x y o1 ->
      r y z o2 ->
      seq_star_r r x z o1.

  Hint Constructors seq_star_r.

  Theorem seq_star_lr A `(r: relation A A T) :
    seq_star r <---> seq_star_r r;; identity.
  Proof.
    t.
    - induction H; propositional; eauto.
      clear H0.
      induction H1; propositional; eauto.
    - induction H; propositional; eauto.
      clear H.
      induction IHseq_star_r; propositional; eauto.
      Grab Existential Variables.
      all: auto.
  Qed.

  Theorem simulation_seq A B
          (p: relation A B unit)
          (q: relation B B unit)
          (r: relation A A unit) :
    p;; q ---> r;; p ->
    p;; seq_star q ---> seq_star r;; p.
  Proof.
    setoid_rewrite seq_star_lr.
    t.
    induction H1; propositional.
    - eauto 10.
    - repeat match goal with
             | [ u: unit |- _ ] => destruct u
             end.
      unfold rimpl in H; simpl in *.
      specialize (H y0 z tt).
      match type of H with
      | ?P -> ?Q =>
        let HP := fresh in
        assert P as HP;
          [ | specialize (H HP) ]
      end; eauto; propositional.
      eauto 10.

      Grab Existential Variables.
      all: auto.
  Qed.

  Theorem simulation_seq_value A B T
          (p: relation A B unit)
          (q: relation B B T)
          (r: relation A A T) :
    p;; q ---> v <- r; (p;; pure v) ->
    p;; seq_star q ---> v <- seq_star r; (p;; pure v).
  Proof.
    setoid_rewrite seq_star_lr.
    t.
    induction H1; propositional.
    - eauto 15.
    - repeat match goal with
             | [ u: unit |- _ ] => destruct u
             end.
      unfold rimpl in H; simpl in *.
      specialize (H y0 z o2).
      match type of H with
      | ?P -> ?Q =>
        let HP := fresh in
        assert P as HP;
          [ | specialize (H HP) ]
      end; eauto; propositional.
      eauto 15.

      Grab Existential Variables.
      all: auto.
  Qed.

  (* some basic properties of tests *)
  Hint Unfold test : t.

  Theorem test_to_id A (P: predicate A) :
    test P ---> identity.
  Proof.
    t.
  Qed.

  Definition pred_and A (P1 P2: predicate A) : predicate A :=
    fun x => P1 x /\ P2 x.

  Hint Unfold pred_and : t.

  Theorem test_and A (P1 P2: predicate A) :
    test P1;; test P2 <---> test (pred_and P1 P2).
  Proof.
    t.
  Qed.

  Theorem test_idem A (P: predicate A) :
    test P;; test P <---> test P.
  Proof.
    t.
  Qed.

  Theorem test_identity A :
    identity (A:=A) <---> test (fun _ => True).
  Proof.
    t.
  Qed.

  Lemma unit_identity A :
    identity (A:=A) <---> pure tt.
  Proof.
    t.
  Qed.

End OutputRelations.

Module RelationNotations.
  Declare Scope relation_scope.
  Delimit Scope relation_scope with rel.
  Open Scope relation_scope.
  Notation "r1 ---> r2" := (rimpl r1 r2)
                             (at level 60, no associativity,
                              format "'[hv' r1  '/' ---> '/'  r2 ']'")
                           : relation_scope.
  Notation "r1 <---> r2" := (requiv r1 r2)
                              (at level 60, no associativity,
                               format "'[hv' r1  '/' <---> '/'  r2 ']'")
                            : relation_scope.
  Infix "+" := rel_or : relation_scope.

  Notation "p1 ;; p2" := (and_then p1 (fun _ => p2))
                           (at level 54, right associativity)
  : relation_scope.
  (* TODO: experiment more with printing boxes *)
  Notation "x <- p1 ; p2" := (and_then p1 (fun x => p2))
                              (at level 54, right associativity,
                               format "'[' x  <-  '[v    ' p1 ']' ; ']'  '/' p2")
                             : relation_scope.
End RelationNotations.
