Require Import Setoid.
Require Import Morphisms.
Require Classical_Prop.

Require Import Tactical.Propositional.
Require Import Tactical.Misc.
From Classes Require Import Classes.

Set Implicit Arguments.
Generalizable All Variables.
(* for compatibility with coq master *)
Set Warnings "-undeclared-scope".

Section OutputRelations.

  (* an output relation: a heterogeneous relation from [A] to [B] that also
  emits some value of type [T] *)
  Inductive Return (B T: Type) : Type :=
  | Val (b: B) (t: T)
  | Err.

  Arguments Val {_ _}.
  Arguments Err {_ _}.

  Definition relation A B T := A -> Return B T -> Prop.

  (** Several operations on relations *)
  Definition and_then {A B C} {T1 T2}
             (r1: relation A B T1)
             (r2: T1 -> relation B C T2) :
    relation A C T2 :=
    fun x mz =>
      match mz with
      | Val z o2 => exists o1 y, r1 x (Val y o1) /\ (r2 o1) y (Val z o2)
      | Err => r1 x Err \/ exists o1 y, r1 x (Val y o1) /\ (r2 o1) y Err
      end.

  Notation "p1 ;; p2" := (and_then p1 (fun _ => p2))
                           (at level 55, p2 at next level, right associativity).
  Notation "x <- p1 ; p2" := (and_then p1 (fun x => p2))
                               (at level 54, right associativity).

  Definition pure A T (o0:T) : relation A A T :=
    fun x y => Val x o0 = y.

  Definition identity {A} {T} : relation A A T :=
    fun x y => exists t, Val x t = y.

  Definition any {A B} {T} : relation A B T :=
    fun x y => True.

  Definition none {A B} {T} : relation A B T :=
    fun x y => False.

  Definition reads {A} {T} (f: A -> T) : relation A A T :=
    fun x y => Val x (f x) = y.

  Definition puts {A} (f: A -> A) : relation A A unit :=
    fun x y => y = Val (f x) tt.

  Definition error {A B T} : relation A B T :=
    fun _ r => r = Err.

  Definition readSome {A T} (f: A -> option T) : relation A A T :=
    fun s r => match f s with
            | Some v => r = Val s v
            | None => r = Err
            end.

  Definition readNone {A T} (f: A -> option T) : relation A A unit :=
    fun s r => match f s with
            | Some _ => r = Err
            | None => r = Val s tt
            end.

  Inductive such_that {A T} (f: A -> T -> Prop) : relation A A T :=
  | such_that_holds : forall s v, f s v -> such_that f s (Val s v).

  Definition predicate A := A -> Prop.
  (* TODO: should failure of a test be error? *)
  Definition test {A} (P: predicate A) : relation A A unit :=
    fun x y => P x /\ Val x tt = y.

  Definition rel_or A B T (r1 r2: relation A B T) : relation A B T :=
    fun x y => r1 x y \/ r2 x y.
  (*
  Definition rel_or A B T (r1 r2: relation A B T) : relation A B T :=
    fun x y =>
      match y with
      | Val b o => (r1 x (Val b o) /\ ~ (r2 x Err)) \/
                     (r2 x (Val b o) /\ ~ (r1 x Err))
      | Err => r1 x Err \/ r2 x Err
      end.
   *)

  Infix "+" := rel_or.

  Inductive seq_star A `(r: relation A A T) : relation A A T :=
  | seq_star_refl : forall x o,
      seq_star r x (Val x o)
  | seq_star_one_more_valid : forall x y z o1,
      r x (Val y o1) ->
      seq_star r y z ->
      seq_star r x z
  | seq_star_one_more_err : forall x,
      r x Err ->
      seq_star r x Err
  .

  (* at-least-once iteration *)
  Inductive seq_plus A `(r: relation A A T) : relation A A T :=
  | seq_plus_once : forall x y,
      r x y ->
      seq_plus r x y
  | seq_plus_one_more_valid : forall x y z o1,
      r x (Val y o1) ->
      seq_plus r y z ->
      seq_plus r x z.

  Inductive bind_star A `(r: T -> relation A A T) : T -> relation A A T :=
  | bind_star_pure : forall (o:T) x,
      bind_star r o x (Val x o)
  | bind_star_one_more_valid : forall (o1:T) x y z o2,
      r o1 x (Val y o2) ->
      bind_star r o2 y z ->
      bind_star r o1 x z
  | bind_star_one_more_err : forall (o1:T) x,
      r o1 x Err ->
      bind_star r o1 x Err
  .

  Inductive bind_star_r A `(r: T -> relation A A T) : T -> relation A A T :=
  | bind_star_r_pure : forall (o:T) x,
      bind_star_r r o x (Val x o)
                  (*
  | bind_star_r_err_refl : forall (o1:T) x,
      r o1 x Err ->
      bind_star_r r o1 x Err
                   *)
  | bind_star_r_one_more_valid : forall (o1:T) x y z o2,
      bind_star_r r o1 x (Val y o2) ->
      r o2 y z ->
      bind_star_r r o1 x z
  | bind_star_r_one_more_err : forall (o1 o2:T) x y,
      bind_star_r r o1 x (Val y o2) ->
      r o2 y Err ->
      bind_star_r r o1 x Err
  .

  (** Notions of equivalence and implication *)

  Definition rimpl {A B} {T} (r1 r2: relation A B T) :=
    forall x y, r1 x y -> r2 x Err \/ r2 x y.

  Lemma rimpl_alt {A B} {T} (r1 r2: relation A B T) :
    (forall a ret, ~ r2 a Err -> r1 a ret -> r2 a ret) ->
    rimpl r1 r2.
  Proof.
    intros Halt x ret Hr1.
    destruct (Classical_Prop.classic (r2 x Err)); auto.
  Qed.

  Global Instance rimpl_preorder T : PreOrder (rimpl (A:=A) (B:=B) (T:=T)).
  split.
  - intros x y.  firstorder.
  - intros x y z H1 H2 ? ? ?.
    destruct (H1 x0 y0); intuition.
    destruct (H2 x0 Err); intuition.
  Qed.

  Definition requiv {A B} {T} (r1 r2: relation A B T) :=
    rimpl r1 r2 /\ rimpl r2 r1.

  Global Instance requiv_equivalence : Equivalence (requiv (A:=A) (B:=B) (T:=T)).
  Proof.
    split.
    - intros ?; split; reflexivity.
    - intros ?? (?&?); split; eauto.
    - intros ??? (?&?) (?&?); split.
      * etransitivity; eauto.
      * etransitivity; eauto.
  Qed.

  Infix "--->" := rimpl (at level 60, no associativity).
  Infix "<--->" := requiv (at level 60, no associativity).

  Global Instance rimpl_requiv_sub : subrelation (requiv (A:=A) (B:=B) (T:=T)) rimpl :=
    ltac:(firstorder).

  Global Instance rimpl_proper_basics_flip A B T (r: relation A B T) :
    Proper
      (Basics.flip rimpl ==> Basics.flip Basics.impl) (rimpl r).
  Proof.
    unfold Basics.flip, Basics.impl.
    intros ?? ??. etransitivity; eauto.
  Qed.

  Lemma rimpl_elim A B T (r1 r2: relation A B T) a b:
    r1 a b ->
    r1 ---> r2 ->
    r2 a Err \/ r2 a b.
  Proof. firstorder. Qed.

  Lemma requiv_no_err_elim A B T (r1 r2: relation A B T) a b:
    r1 a b ->
    r1 <---> r2 ->
    ~ (r1 a Err) ->
    r2 a b.
  Proof.
    intros Hr1 (Hlr&Hrl) Hno_err. eapply Hlr in Hr1.
    destruct Hr1 as [Herr|?]; eauto.
    apply Hrl in Herr. intuition.
  Qed.

  Lemma requiv_no_err_elim' A B T (r1 r2: relation A B T) a b:
    r1 a b ->
    r1 <---> r2 ->
    ~ (r2 a Err) ->
    r2 a b.
  Proof.
    intros Hr1 (Hlr&Hrl) Hno_err. eapply Hlr in Hr1.
    destruct Hr1 as [Herr|?]; eauto. intuition.
  Qed.

  Lemma requiv_err_elim A B T (r1 r2: relation A B T) a:
    r1 a Err ->
    r1 <---> r2 ->
    r2 a Err.
  Proof.
    intros Hr1 (Hlr&Hrl). eapply Hlr in Hr1; intuition.
  Qed.

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

  (* we define an ordering over relations ---> in a natural way for relations,
  but the definition is equivalent to starting with equivalence [<--->] and
  defining [r1 <= r2 := r1 + r2 <---> r2] *)
  Theorem rimpl_or A B T (r1 r2: relation A B T) :
    r1 ---> r2 ->
    r1 + r2 <---> r2.
  Proof.
    firstorder.
  Qed.

  Theorem rel_or_to_rimpl A B T (r1 r2: relation A B T) :
    r1 + r2 <---> r2 ->
    r1 ---> r2.
  Proof.
    firstorder.
  Qed.

  (** Various equivalence and implication proofs *)
  Hint Unfold Proper respectful pointwise_relation : t.
  Hint Unfold Basics.flip Basics.impl : t.
  Hint Unfold and_then rel_or pure any identity reads : t.

  Ltac add_hypothesis' pf :=
    let P := type of pf in
    lazymatch P with
    | ?P' \/ ?Q' =>
      lazymatch goal with
      | [ H: P' \/ Q' |- _ ] => fail "already known"
      | [ H: Q' \/ P' |- _ ] => fail "already known"
      | [ H: P' |- _ ] => fail "already known"
      | [ H: Q' |- _ ] => fail "already known"
      | _ => pose proof pf
      end
    | ?P' =>
      lazymatch goal with
      | [ H: P' |- _ ] => fail "already known"
      | _ => pose proof pf
      end
    end.

  Ltac t :=
    autounfold with t;
    repeat match goal with
           | |- _ <---> _ => split
           | |- _ ---> _ => unfold "--->"
                                   (*
           | [ H: ?r <---> _ |- _ ] => add_hypothesis (proj1 H)
           | [ H: _ <---> ?r |- _ ] => add_hypothesis (proj2 H)
           | [ H: ?r ---> _ |- _] =>
             match type of r with
             | relation ?A ?B ?T =>
               match goal with
               | [ x: A, y: Return B T |- _ ] => add_hypothesis' (H x y); add_hypothesis' (H x Err)
               | [ x: A, y: B, o: T |- _ ] => add_hypothesis' (H x (Val y o));
                                              add_hypothesis' (H x Err)
               end
             end
                                    *)
           | [ H: ?r <---> _,
                  H': ?r ?x ?y |- _ ] =>
             add_hypothesis (proj1 H x y H')
           | [ H: _ <---> ?r,
                  H': ?r ?x ?y |- _ ] =>
             add_hypothesis (proj2 H x y H')
           | [ H: ?r ---> _,
                  H': ?r ?x ?y |- _ ] =>
             add_hypothesis (H x y H')
           | [ u: unit |- _ ] => destruct u
           | [ |- exists (_:unit), _ ] => exists tt
           | _ => progress propositional
           | _ => solve [ eauto 10 ]
           | [ H: _ \/ _  |- _ ] => destruct H
           | [ H : none _ _ |- _] => destruct H
           | [ H : Val _ _ = Val _ _ |- _] => inversion H; subst; clear H
           | [ H : Val _ _  = Err |- _] => inversion H
           | [ H : Err = Val _ _ |- _] => inversion H
        end.

  Ltac destruct_return :=
    match goal with
    | [ y : Return _ _  |- _ ] => destruct y
    end.


  (* first some respectful/congruence rules *)
  Global Instance or_respects_equiv :
    Proper (requiv ==> requiv ==> requiv) (rel_or (A:=A) (B:=B) (T:=T)).
  Proof. t. Qed.

  Global Instance or_respects_impl :
    Proper (rimpl ==> rimpl ==> rimpl) (rel_or (A:=A) (B:=B) (T:=T)).
  Proof. t. Qed.

  Theorem and_then_monotonic A B C T1 T2
          (r1 r1': relation A B T1) (r2 r2': T1 -> relation B C T2) :
    r1 ---> r1' ->
    (forall x, r2 x ---> r2' x) ->
    and_then r1 r2 ---> and_then r1' r2'.
  Proof.
    t. destruct_return.
    - destruct H1 as (o1&y&?&?). edestruct (H0 o1); t.
    - destruct H1 as [|(o1&y&?&?)]. t.
      edestruct (H0 o1); t.
  Qed.

  Global Instance and_then_respectful :
    Proper (rimpl ==> pointwise_relation _ rimpl ==> rimpl) (and_then (A:=A) (B:=B) (C:=C) (T1:=T1) (T2:=T2)).
  Proof.
    unfold Proper, "==>"; intros.
    apply and_then_monotonic; auto.
  Qed.

  Lemma and_then_err_cancel A B C T1 T2 a
        (r1: relation A B T1)
        (r2 r2': T1 -> relation B C T2) :
    and_then r1 r2 a Err ->
    (forall x b, r2 x b Err -> r2' x b Err) ->
    and_then r1 r2' a Err.
  Proof.
    intros Hand_then1 Himpl.
    destruct Hand_then1; t.
  Qed.

  Theorem and_then_equiv_cong A B C T1 T2
          (r1 r1': relation A B T1)
          (r2 r2': T1 -> relation B C T2) :
    r1 <---> r1' ->
    (forall x, r2 x <---> r2' x) ->
    and_then r1 r2 <---> and_then r1' r2'.
  Proof.
    intros. split; apply and_then_monotonic; eauto.
  Qed.

  Theorem and_then_cong_l A B C T1 T2
          (r1 r1': relation A B T1)
          (r2: T1 -> relation B C T2) :
    r1 <---> r1' ->
    and_then r1 r2 <---> and_then r1' r2.
  Proof.
    intros. split; apply and_then_monotonic; eauto; intros; reflexivity.
  Qed.

  Theorem and_then_cong_r A B C T1 T2
          (r1: relation A B T1)
          (r2 r2': T1 -> relation B C T2) :
    (forall x, r2 x <---> r2' x) ->
    and_then r1 r2 <---> and_then r1 r2'.
  Proof.
    intros. split; apply and_then_monotonic; eauto; intros; reflexivity.
  Qed.

  Theorem bind_identity1 A B T1 T2 (r: relation A B T2) :
    (_ <- identity (T:=T1); r) ---> r.
  Proof.
    t. destruct_return; t; intuition congruence.
  Qed.

  Theorem bind_identity A B T1 T2 (r: relation A B T2) (_:Default T1) :
    (_ <- identity (T:=T1); r) <---> r.
  Proof.
    unshelve (t; destruct_return; t; intuition congruence); eauto.
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
    t. (induction H0; intuition eauto); t.
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
    induction H0; (eauto; specialize (H o1); intuition eauto); t.
  Qed.

  Global Instance bind_star_equiv_respectful :
    Proper (pointwise_relation _ requiv ==> eq ==> requiv) (bind_star (A:=A) (T:=T)).
  Proof.
    t.
    - induction H0; eauto;
      specialize (H o1);
      (apply requiv_to_rimpls in H; propositional; intuition eauto); t.
    - induction H0; eauto;
      specialize (H o1);
      (apply requiv_to_rimpls in H; propositional; intuition eauto); t.
  Qed.

  Theorem and_then_monotonic_r A B C T1 T2
          (r1 r2: relation A B T1) (rx: T1 -> relation B C T2) :
    r1 ---> r2 ->
    and_then r1 rx ---> and_then r2 rx.
  Proof.
    intros.
    rewrite H; reflexivity.
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
    t. destruct_return; t.
  Qed.

  Theorem bind_left_id A B T1 T2 (v:T1) (r: T1 -> relation A B T2) :
    and_then (pure v) r <---> r v.
  Proof.
    t; destruct_return; t; intuition congruence.
  Qed.

  Theorem bind_right_id A B T (r: relation A B T) :
    and_then r (@pure B T) <---> r.
  Proof.
    t; destruct_return; t; intuition congruence.
  Qed.

  (* pure tt is also the right identity for relations at output type T *)
  Theorem bind_right_id_unit A B (r: relation A B unit) :
    and_then r (fun _ => pure tt) <---> r.
  Proof.
    t; destruct_return; t; intuition congruence.
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
    repeat (t; destruct_return; t).
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

  Theorem from_none A B T (r: relation A B T):
    none ---> r.
  Proof.
    t.
  Qed.

  Theorem none_idem A B C T1 T2:
    none (B:=B) (T:=T1);; none --->
        none (A:=A) (B:=C) (T:=T2).
  Proof.
    t. destruct_return; t.
  Qed.

  Theorem none_absorb_l A B C T1 T2 p:
    x <- none (B:=B) (T:=T1); p x --->
        none (A:=A) (B:=C) (T:=T2).
  Proof.
    t. destruct_return; t.
  Qed.

  Theorem none_absorb_l_equiv A B C T1 T2 p:
    x <- none (B:=B) (T:=T1); p x <--->
        none (A:=A) (B:=C) (T:=T2).
  Proof.
    t. destruct_return; t.
  Qed.

  (* This is not true anymore, because p can error *)
  (*
  Theorem none_absorb_r A B C T1 T2 (p: relation A B T1):
    p;; none ---> none (A:=A) (B:=C) (T:=T2).
  Proof.
    t. destruct_return; t.
  Qed.
   *)

  (*
  Theorem none_absorb_r_equiv A B C T1 T2 (p: relation A B T1):
    p;; none <---> none (A:=A) (B:=C) (T:=T2).
  Proof.
    t. destruct_return; t.
  Qed.
   *)

  Theorem none_plus_r A B T1 (p: relation A B T1):
    (p + none) <---> p.
  Proof.
    t.
  Qed.

  Theorem none_plus_l A B T1 (p: relation A B T1):
    (none + p) <---> p.
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
    - induction H0; eauto;
      edestruct (H o1); intuition; t.
    - induction H0; eauto;
      edestruct (H o1); intuition; t.
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

  Theorem bind_star_expand A T (r: T -> relation A A T) (v:T) :
    pure v + and_then (r v) (bind_star r) <---> bind_star r v.
  Proof.
    t; destruct_return; t;
    induction H; eauto;
    t; destruct_return; t.
  Qed.

  Global Instance rimpl_equiv_proper A B T (r: relation A B T) :
    Proper (requiv ==> Basics.flip Basics.impl) (rimpl r).
  Proof.
    intros ?? (?&?) ?. etransitivity; eauto.
  Qed.

  Global Instance rimpl_equiv_applied_proper A B T :
    Proper (requiv ==> requiv ==> iff) (rimpl (A:=A) (B:=B) (T:=T)).
  Proof.
    intros ?? (?&?) ?? (?&?).
    split; intros; repeat (etransitivity; eauto).
  Qed.

  Definition rimpl_refl A B T (r: relation A B T) : r ---> r := ltac:(reflexivity).
  Definition requiv_refl A B T (r: relation A B T) : r <---> r := ltac:(reflexivity).

  Hint Resolve rimpl_refl requiv_refl.

  Theorem bind_dist_r A B C T1 T2 (r1 r2: relation A B T1) (r3: T1 -> relation B C T2) :
    and_then (r1 + r2) r3 <---> (and_then r1 r3) + (and_then r2 r3).
  Proof.
    t; destruct_return; t.
  Qed.

  Theorem bind_dist_l A B C T1 T2 (r1: relation A B T1) (r2 r3: T1 -> relation B C T2) :
    and_then r1 (fun v => r2 v + r3 v) <---> and_then r1 r2 + and_then r1 r3.
  Proof.
    t; destruct_return; t.
  Qed.

  Theorem star_ind A T (r x: relation A A T) :
    identity ---> x ->
    r;; x ---> x ->
    seq_star r ---> x.
  Proof.
    intros H1 H2 a y.
    induction 1.
    - eapply H1. econstructor; eauto.
    - t.
      * left. edestruct (H2 x0 Err); eauto.
        simpl; intuition eauto.
      * eapply H2. destruct z.
        ** econstructor; eauto.
        ** right. intuition eauto.
    - eapply H2; left; eauto.
  Qed.

  Theorem star_expand A T (r: relation A A T) :
    seq_star r <---> identity + (r;; seq_star r).
  Proof.
    apply rimpl_to_requiv.
    - apply star_ind; t; destruct_return; t.
    - t; destruct_return; t.
  Qed.

  Theorem seq_star1 A T (r: relation A A T) :
    r;; seq_star r ---> seq_star r.
  Proof.
    t; destruct_return; t.
  Qed.

  Theorem seq_star_fold A T (r r': relation A A T) :
    r' ---> r ->
    r';; seq_star r ---> seq_star r.
  Proof.
    t; destruct_return; t.
  Qed.

  Theorem seq_star_none A T (r: relation A A T) :
    identity ---> seq_star r.
  Proof.
    t.
  Qed.

  Theorem seq_star_one A T (r: relation A A T) :
    r ---> seq_star r.
  Proof.
    t; destruct_return; t.
  Qed.

  Hint Constructors seq_plus.

  Theorem plus_one `(r: relation A A T) :
    r ---> seq_plus r.
  Proof.
    t.
  Qed.

  Theorem plus_expand A T (r: relation A A T) :
    seq_plus r <---> r + (r;; seq_plus r).
  Proof.
    t; destruct_return; t; induction H; eauto; t.
  Qed.

  (*
  Inductive seq_plus_r `(r: relation A A T) : relation A A T :=
  | seq_plus_r_once : forall x y o,
      r x y o ->
      seq_plus_r r x y o
  | seq_plus_r_one_more : forall x y z o1 o2,
      seq_plus_r r x y o1 ->
      r y z o2 ->
      seq_plus_r r x z o2.

  Hint Constructors seq_plus_r.

  Theorem seq_plus_lr `(r: relation A A T) :
    seq_plus r <---> seq_plus_r r.
  Proof.
    t.
    - induction H; eauto.
      clear H0.
      induction IHseq_plus; eauto.
    - induction H; eauto.
      clear H.
      induction IHseq_plus_r; eauto.
  Qed.

  Theorem plus_expand_r A T (r: relation A A T) :
    seq_plus r <---> r + (seq_plus r;; r).
  Proof.
    rewrite seq_plus_lr.
    t.
    induction H; eauto.
  Qed.
   *)

  Global Instance and_then_pointwise A B C T1 T2 (r: relation A B T1) :
    Proper (pointwise_relation _ (Basics.flip rimpl) ==> Basics.flip (rimpl (B:=C) (T:=T2)))
           (and_then r).
  Proof.
    t. destruct_return; t;
    specialize (H o1); t.
  Qed.

  Theorem star_duplicate A T (r: relation A A T) :
    seq_star r <---> seq_star r;; seq_star r.
  Proof.
    t.
    - induction H.
      * unshelve (eauto); eauto.
      * unshelve (destruct_return; t); eauto.
      * do 2 left. eapply seq_star_one_more_err; eauto.
    - destruct_return; t.
      * remember (Val y o1) as z eqn:Heq. revert y o1 H0 Heq. revert H.
        induction 1; intros.
        ** inversion Heq; subst. intuition.
        ** subst. edestruct IHseq_star; eauto.
        ** congruence.
      * remember (Val y o1) as z eqn:Heq. revert y o1 H0 Heq. revert H.
        induction 1; intros.
        ** inversion Heq; subst. intuition.
        ** subst. edestruct IHseq_star; eauto.
        ** congruence.
  Qed.

  Theorem star_one A T (r: relation A A T) :
    r ---> seq_star r.
  Proof.
    t. destruct_return; t.
  Qed.

  Lemma star_monotonic A T (r1 r2: relation A A T) :
    r1 ---> r2 ->
    seq_star r1 ---> seq_star r2.
  Proof.
    intros.
    rewrite H; reflexivity.
  Qed.

  Lemma star_congruent A T (r1 r2: relation A A T) :
    r1 <---> r2 ->
    seq_star r1 <---> seq_star r2.
  Proof.
    intros.
    rewrite H; reflexivity.
  Qed.

  Lemma bind_star_congruent A T (r1 r2: T -> relation A A T) (v:T) :
    (forall v, r1 v <---> r2 v) ->
    bind_star r1 v <---> bind_star r2 v.
  Proof.
    intros.
    apply bind_star_equiv_respectful; auto.
  Qed.

  Theorem star_expand_r A (r: relation A A unit) :
    seq_star r <---> identity + (seq_star r;; r).
  Proof.
    apply rimpl_to_requiv.
    - unshelve (apply star_ind; t;
        destruct_return; t;
      inversion H0; subst; t;
      congruence); exact tt.
    - apply rel_or_elim.
      * t.
      * rewrite star_duplicate at 2.
        apply and_then_monotonic; eauto.
        intros []. apply star_one.
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

  Theorem bind_unit' B C T (q: unit -> relation B C T) v:
    q v <---> q tt.
  Proof.
    t.
  Qed.

  Theorem bind_unit A B C T (p: relation A B unit) (q: unit -> relation B C T) :
    and_then p q <---> p;; q tt.
  Proof.
    setoid_rewrite <-bind_unit'; reflexivity.
  Qed.

  Theorem denesting A T (r1 r2: relation A A T) (_:Default T):
    seq_star (r1 + r2) <--->
             seq_star r1;; (seq_star (r2;; seq_star r1)).
  Proof.
    apply rimpl_to_requiv.
    - unshelve (apply star_ind; t; destruct_return; t; intuition t); eauto.
    - setoid_rewrite star_duplicate at 4; cong.
      cong.

      apply star_ind; try solve [ t ].
      setoid_rewrite star_duplicate at 3; cong.

      setoid_rewrite star_duplicate at 2; cong.
      * setoid_rewrite <-star_one. apply rel_or_intror.
      * cong.
  Qed.

  Theorem bind_sliding A T1 (p: relation A A T1) (q: T1 -> relation A A unit) :
    seq_star (and_then p q);; p <--->
             v <- p; bind_star (fun v0 => q v0;; p) v.
  Proof.
    apply rimpl_to_requiv.
    - t. destruct_return.
      * destruct H as ([]&y&Hstar&Hy).
        remember (Val y tt) as ret eqn:Heq. gen y Heq.
        induction Hstar; subst; t.
        ** specialize (IHHstar _ ltac:(eauto) ltac:(eauto)); t.
           left. right.
           do 2 eexists; split; eauto.
           eapply bind_star_one_more_err. eauto.
      * t.
        ** set (ret := @Err A unit). replace Err with ret in H at 1; eauto.
           remember ret as ret' eqn:Heq. unfold ret in Heq.
           induction H.
           *** congruence.
           *** t; left; right; do 2 eexists; split; eauto; t.
           *** t.
        ** remember (Val y tt) as ret eqn:Heq. gen y Heq.
        induction H; subst; t.
        *** specialize (IHseq_star _ ltac:(eauto) ltac:(eauto)); t.
           **** left. right.
           do 2 eexists; split; eauto.
           eapply bind_star_one_more_err. eauto.
           **** left. right.
           do 2 eexists; split; eauto.
           eapply bind_star_one_more_err. eauto.
    - t. destruct_return.
      * t.
        gen x.
        unshelve (induction H0; t); try exact tt.
        specialize (IHbind_star _ ltac:(eauto)); t.
      * unshelve t; try exact tt.
        **
        gen x.
        unshelve (induction H0; t); try exact tt.
        unshelve (specialize (IHbind_star _ ltac:(eauto)); t); try exact tt.
  Qed.

  Theorem seq_sliding A T1 (p: relation A A T1) (q: relation A A unit) :
    seq_star (p;; q);; p --->
             p;; seq_star (q;; p).
  Proof.
    - t. destruct_return.
      * destruct H as ([]&y&Hstar&Hy).
        remember (Val y tt) as ret eqn:Heq. gen y Heq.
        induction Hstar; subst; t.
        specialize (IHHstar _ ltac:(eauto) ltac:(eauto)); t.
        left. right.
        do 2 eexists; split; eauto.
        eapply seq_star_one_more_err. eauto.
      * t.
        ** set (ret := @Err A unit). replace Err with ret in H at 1; eauto.
           remember ret as ret' eqn:Heq. unfold ret in Heq.
           induction H.
           *** congruence.
           *** t; left; right; do 2 eexists; split; eauto; t.
           *** t.
        ** remember (Val y tt) as ret eqn:Heq. gen y Heq.
           induction H; subst; t.
           specialize (IHseq_star _ ltac:(eauto) ltac:(eauto)); t.
           *** left. right.
           do 2 eexists; split; eauto.
           eapply seq_star_one_more_err. eauto.
           *** left. right.
           do 2 eexists; split; eauto.
           eapply seq_star_one_more_err. eauto.
  Qed.


  Theorem seq_unit_sliding A (p: relation A A unit) (q: relation A A unit) :
    p;; seq_star (q;; p) --->
     seq_star (p;; q);; p.
  Proof.
    setoid_rewrite seq_star_to_bind_star at 1.
    setoid_rewrite bind_sliding.
    eapply bind_unit.
  Qed.

  Theorem seq_unit_sliding_equiv A (p: relation A A unit) (q: relation A A unit) :
     seq_star (p;; q);; p <--->
              p;; seq_star (q;; p).
  Proof.
    apply rimpl_to_requiv; auto using seq_sliding, seq_unit_sliding.
  Qed.

  Inductive seq_star_r A `(r: relation A A T) : relation A A T :=
  | seq_star_r_refl : forall x o,
      seq_star_r r x (Val x o)
  (* This might seem redundant because of _one_more_err, but it is not if T is uninhabited *)
  | seq_star_r_err_refl : forall x,
      r x Err ->
      seq_star_r r x Err
  | seq_star_r_one_more_valid : forall x y z o1 o2,
      seq_star_r r x (Val y o1) ->
      r y (Val z o2) ->
      seq_star_r r x (Val z o2)
  | seq_star_r_one_more_err : forall x y o1,
      seq_star_r r x (Val y o1) ->
      r y Err ->
      seq_star_r r x Err.

  Hint Constructors seq_star_r.

  Lemma seq_star_r_one_more_valid_left {A T} (r: relation A A T) x y z o1 o2:
    r x (Val y o1) ->
    seq_star_r r y (Val z o2) ->
    exists o3, seq_star_r r x (Val z o3).
  Proof.
    intros Hr Hseq. remember (Val z o2) as ret eqn: Heq. revert x z o1 o2 Hr Heq.
    induction Hseq; intros.
    - unshelve t; eauto.
    - unshelve t; eauto.
    - t. edestruct IHHseq; eauto.
    - t.
  Qed.

  Lemma seq_star_trans A `(r: relation A A T) (x y: A) (o: T) z:
    seq_star r x (Val y o) ->
    seq_star r y z ->
    seq_star r x z.
  Proof.
    intros Hstar.
    remember (Val y o) as ret eqn:Heq. revert y o Heq.
    induction Hstar; t.
  Qed.

  Lemma seq_star_rl_valid A `(r: relation A A T) x b o1 o2:
    seq_star_r r x (Val b o1) ->
    seq_star r x (Val b o2).
  Proof.
    intros Hstar.
    remember (Val b o1) as ret eqn:Heq.
    revert b o1 Heq. induction Hstar; t.
    specialize (IHHstar y o1 ltac:(eauto)); t.
    clear Hstar.
    remember (Val y o2) as ret eqn:Heq.
    revert o2 Heq.
    induction IHHstar; t.
  Qed.

  Hint Resolve seq_star_r_one_more_valid_left.

  Theorem seq_star_lr A `(r: relation A A T) :
    seq_star r <---> seq_star_r r;; identity.
  Proof.
    t.
    - induction H.
      * unshelve t; eauto.
      * t.
        ** unshelve (induction H1; propositional; eauto; t; destruct_return; t); eauto.
        ** destruct_return; t.
           *** edestruct (@seq_star_r_one_more_valid_left A _ r); eauto; t.
           *** remember Err as ret eqn:Heq.
               gen Heq. unshelve (induction H1; intros; t); eauto.
               left. left.
               edestruct (@seq_star_r_one_more_valid_left A _ r); eauto; t.
      * left. left. econstructor. unshelve t; eauto.
    - destruct_return; t.
      * right. eapply seq_star_rl_valid; eauto.
      * left.
        inversion H; subst.
        ** eapply seq_star_one_more_err; eauto.
        ** unshelve (eapply seq_star_trans; [| eapply seq_star_one_more_err; eauto]); eauto.
           eapply seq_star_rl_valid; eauto.
  Qed.

  Hint Constructors bind_star_r.

  Lemma bind_star_r_one_more_valid_left {A T} (r: T -> relation A A T) x y z o1 o2 o3:
    r o1 x (Val y o2) ->
    bind_star_r r o2 y (Val z o3) ->
    bind_star_r r o1 x (Val z o3).
  Proof.
    intros Hr Hseq. remember (Val z o2) as ret eqn: Heq. revert x o1 Hr Heq.
    induction Hseq; intros; unshelve t; eauto.
  Qed.

  Lemma bind_star_trans A `(r: T -> relation A A T) (x y: A) (o1 o2: T) z:
    bind_star r o1 x (Val y o2) ->
    bind_star r o2 y z ->
    bind_star r o1 x z.
  Proof.
    intros Hstar.
    remember (Val y o2) as ret eqn:Heq. revert y o2 Heq.
    induction Hstar; t.
  Qed.

  Lemma bind_star_rl_valid A `(r: T -> relation A A T) x b o1 o2:
    bind_star_r r o1 x (Val b o2) ->
    bind_star r o1 x (Val b o2).
  Proof.
    intros Hstar.
    remember (Val b o2) as ret eqn:Heq.
    revert b o2 Heq. induction Hstar; t.
    specialize (IHHstar y o2 ltac:(eauto)); t.
    clear Hstar.
    remember (Val y o2) as ret eqn:Heq.
    revert o2 Heq H.
    induction IHHstar; t.
  Qed.

  Lemma bind_star_lr_valid A `(r: T -> relation A A T) x b o1 o2:
    bind_star r o1 x (Val b o2) ->
    bind_star_r r o1 x (Val b o2).
  Proof.
    intros Hstar.
    remember (Val b o2) as ret eqn:Heq.
    revert b o2 Heq. induction Hstar; t.
    specialize (IHHstar _ _ ltac:(eauto)); t.
    clear Hstar.
    remember (Val y o2) as ret eqn:Heq.
    subst.
    induction IHHstar; t.
  Qed.

  Hint Resolve bind_star_r_one_more_valid_left.

  Theorem bind_star_lr A `(r: T -> relation A A T) (v:T) :
    bind_star r v <---> bind_star_r r v.
  Proof.
    t.
    - induction H.
      * unshelve t; eauto.
      * t.
        ** unshelve (induction H1; propositional; eauto; t; destruct_return; t); eauto.
        ** destruct_return; t; unshelve (induction H1; intros; t); eauto.
      * t.
    - destruct_return; t.
      * right. eapply bind_star_rl_valid; eauto.
      * left.
        inversion H; subst;
        unshelve (eapply bind_star_trans; [| eapply bind_star_one_more_err; eauto]);
        eauto using bind_star_rl_valid.
  Qed.

  Theorem bind_star_expand_r_valid `(r: T -> relation A A T) (v:T) x b o :
    (rel_or (pure v) (and_then (bind_star r v) r) x (Val b o)) <-> bind_star r v x (Val b o).
  Proof.
    split.
    - intros. apply bind_star_rl_valid.
      destruct H; t.
      * inversion H; subst. econstructor.
      * inversion H; subst. t.
        eapply bind_star_r_one_more_valid.
        { eapply bind_star_lr_valid; eauto. }
        { eauto. }
    - intros [?|?|?]%bind_star_lr_valid.
      * left; econstructor.
      * right. destruct_return.
        ** do 2 eexists; split.
           *** eapply bind_star_rl_valid; eauto.
           *** eauto.
        ** right. do 2 eexists; split.
           *** eapply bind_star_rl_valid; eauto.
           *** eauto.
      * right.
        ** right. do 2 eexists; split.
           *** eapply bind_star_rl_valid; eauto.
           *** eauto.
  Qed.

  Theorem bind_star_expand_r `(r: T -> relation A A T) (v:T) :
    pure v + and_then (bind_star r v) r <---> bind_star r v.
  Proof.
    rewrite bind_star_lr.
    t; destruct_return; t;
    induction H; eauto;
    t; destruct_return; t.
  Qed.

  Theorem seq_star_ind_l A B T1 (q x: relation A B T1) T2 (p: relation A A T2) :
    q + and_then p (fun _ => x) ---> x ->
    and_then (seq_star p) (fun _ => q) ---> x.
  Proof.
    t; destruct_return; t.
    * remember (Val y o1) as ret eqn:Heq.
      revert y b o1 Heq H1. induction H0; intros; t.
      edestruct IHseq_star; t.
      edestruct (H x0 Err); t.
    * remember Err as ret eqn:Heq.
      revert Heq. induction H0; t.
    * remember (Val y o1) as ret eqn:Heq.
      revert y o1 Heq H1. induction H0; intros; t.
      edestruct IHseq_star; t.
  Qed.

  Theorem pure_no_err A T (a: A) (v: T): pure v a Err -> False.
  Proof. inversion 1. Qed.

  Theorem bind_with_no_err A B C T S (p: relation A B T) (r: T -> relation B C S) a:
    (forall b t, r t b Err -> False) ->
    and_then p r a Err ->
    p a Err.
  Proof.
    intros Hno_err. inversion 1; auto.
    exfalso; t.
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
    t; destruct_return; t.
  Qed.

  Theorem test_idem A (P: predicate A) :
    test P;; test P <---> test P.
  Proof.
    t; destruct_return; t.
  Qed.

  Theorem test_identity A :
    identity (A:=A) <---> test (fun _ => True).
  Proof.
    t; destruct_return; t.
  Qed.

  Lemma unit_identity A :
    identity (A:=A) <---> pure tt.
  Proof.
    t; destruct_return; t.
  Qed.

End OutputRelations.

Module RelationNotations.
  (* Declare Scope relation_scope. *)
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
  (at level 100, p2 at level 200, only parsing, right associativity)
  : relation_scope.
  (* TODO: experiment more with printing boxes *)
  Notation "x <- p1 ; p2" := (and_then p1 (fun x => p2))
                              (at level 20, p1 at level 100, p2 at level 200, right associativity,
                               format "'[' x  <-  '[v    ' p1 ']' ; ']'  '/' p2")
                             : relation_scope.
  Ltac destruct_return :=
    match goal with
    | [ y : Return _ _  |- _ ] => destruct y
    end.

End RelationNotations.
