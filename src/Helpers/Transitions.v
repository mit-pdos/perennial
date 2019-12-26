From Coq Require Import RelationClasses.
From Coq Require Import Setoid.
From Coq Require Import ZArith.

From stdpp Require Import base.

Set Implicit Arguments.
Generalizable All Variables.

Class GenPred T Σ (pred: Σ -> T -> Prop) := genNext : Z -> forall (s:Σ), option {x:T | pred s x}.
Arguments GenPred : clear implicits.
Notation GenType T Σ := (GenPred T Σ (fun _ _ => True)).

Instance fallback_genPred T Σ p : GenPred T Σ p | 99 := fun _ _ => None.
Instance bool_GenType Σ : GenType bool Σ := fun z _ => Some (exist _ (z mod 2 =? 0)%Z I).

Section transition.
  Context {Σ:Type}.

  Inductive transition : Type -> Type :=
  | runF {T} (f: Σ -> Σ * T) : transition T
  | suchThat {T} (pred: Σ -> T -> Prop) {gen:GenPred T Σ pred} : transition T
  | bind {T T'} (x: transition T') (rx: T' -> transition T) : transition T
  .

  Arguments suchThat {T} pred {gen}.

  Definition ret {T} (v:T): transition T :=
    runF (fun s => (s, v)).

  Definition fmap {T1 T2} (f: T1 -> T2) (r: transition T1): transition T2 :=
    bind r (fun x => ret (f x)).

  Definition r_mbind : MBind transition :=
    fun {A B} rx r => bind r rx.
  Definition r_mret : MRet transition := @ret.
  Definition r_fmap : FMap transition := @fmap.

  Definition reads {T} (f: Σ -> T): transition T :=
    runF (fun s => (s, f s)).

  Definition modify (f: Σ -> Σ): transition unit :=
    runF (fun s => (f s, tt)).

  Definition any T {gen:GenType T Σ}: transition T :=
    suchThat (fun _ _ => True).

  Arguments any T {gen}.

  Definition undefined {T}: transition T :=
    suchThat (fun _ _ => False).

  Definition plus {T} (r1 r2: transition T): transition T :=
    bind (any bool) (fun b => if b then r1 else r2).

  Definition ifThenElse P `{!Decision P} {T} (tr1 tr2: transition T): transition T :=
    if (decide P) then tr1 else tr2.

  Arguments ifThenElse P {_} {T}.

  Definition check P `{!Decision P}: transition unit :=
    ifThenElse P (ret tt) (undefined).

  Definition checkNot P `{!Decision P}: transition unit :=
    ifThenElse P (undefined) (ret tt).

  Definition when P `{!Decision P} (r: transition unit): transition unit :=
    ifThenElse P r (ret tt).

  Definition unless P `{!Decision P} (r: transition unit): transition unit :=
    ifThenElse P (ret tt) (r).

  Definition unwrap {T} (mx: option T): transition T :=
    match mx with
    | Some x => ret x
    | None => undefined
    end.

  Theorem ifThenElse_if P `{!Decision P} {T} (r1 r2: transition T) :
    P ->
    ifThenElse P r1 r2 = r1.
  Proof.
    intros H.
    unfold ifThenElse.
    destruct (decide P); auto || contradiction.
  Qed.

  Theorem ifThenElse_else P `{!Decision P} {T} (r1 r2: transition T) :
    ~P ->
    ifThenElse P r1 r2 = r2.
  Proof.
    intros H.
    unfold ifThenElse.
    destruct (decide P); auto || contradiction.
  Qed.

  Definition next_hint (hints: list Z): Z * list Z :=
    match hints with
    | z::hints' => (z, hints')
    | nil => (0%Z, nil)
    end.

  Fixpoint interpret (hints: list Z) {T} (tr: transition T): Σ -> option (list Z * Σ * T) :=
    match tr with
    | runF f => fun s => let (s', v) := f s in
                     Some (hints, s', v)
    | bind r1 rx => fun s => match interpret hints r1 s with
                         | Some (hints', s', v) =>
                           interpret hints' (rx v) s'
                         | None => None
                         end
    | suchThat pred => let (hint, hints') := next_hint hints in
                          fun s => match genNext hint s with
                                | Some (exist _ x _) => Some (hints', s, x)
                                | None => None
                                end
    end.

End transition.

Arguments transition Σ T : clear implicits.
Arguments suchThat {Σ T} pred {gen}.
Arguments any {Σ} T {gen}.
Arguments check {Σ} P {_}.
Arguments when {Σ} P {_}.

Module relation.
  Section state.
    Context (Σ:Type).
    Definition t T := Σ -> Σ -> T -> Prop.

    Inductive runF {T} (f:Σ -> Σ * T): t T :=
    | runF_runs : forall s s' v,
        f s = (s', v) ->
        runF f s s' v.

    Theorem runF_runs_to {T} (f: Σ -> Σ * T) s :
      runF f s (fst (f s)) (snd (f s)).
    Proof.
      econstructor.
      destruct (f s); auto.
    Qed.

    Inductive suchThat {T} (pred: Σ -> T -> Prop): t T :=
    | suchThat_runs : forall s x,
        pred s x ->
        suchThat pred s s x
    .

    Inductive bind {T1 T2} (r: t T1) (rx: T1 -> t T2): t T2 :=
    | bind_runs : forall s1 s2 x s3 x',
        r s1 s2 x ->
        (rx x) s2 s3 x' ->
        bind r rx s1 s3 x'
    .

    Definition ret {T} (v:T): t T :=
      runF (fun s => (s, v)).

    Theorem inv_runF {T} (f:Σ -> Σ*T) :
      forall s1 s2 v', runF f s1 s2 v' ->
                  s2 = fst (f s1) /\ v' = snd (f s1).
    Proof.
      intros.
      inversion H; subst.
      destruct (f s1); inversion H0; subst; auto.
    Qed.

    Theorem inv_ret {T} (v:T) :
      forall s1 s2 v', ret v s1 s2 v' ->
                  s2 = s1 /\ v' = v.
    Proof.
      intros.
      apply inv_runF in H; intuition subst.
    Qed.

    Theorem inv_suchThat {T} (pred:Σ -> T -> Prop) :
      forall s1 s2 v', suchThat pred s1 s2 v' ->
                  s2 = s1 /\ pred s1 v'.
    Proof.
      intros.
      inversion H; subst; eauto.
    Qed.

    Definition fmap {T1 T2} (f: T1 -> T2) (r: t T1): t T2 :=
      bind r (fun x => ret (f x)).

    Fixpoint denote {T} (tr: transition Σ T): t T :=
      match tr with
      | Transitions.runF f => runF f
      | Transitions.suchThat pred => suchThat pred
      | Transitions.bind r rx => bind (denote r) (fun x => denote (rx x))
      end.

    Theorem suchThat_gen_run {T} (pred: Σ -> T -> Prop) {gen: GenPred T Σ pred} (hint:Z) :
      forall s v H,
      gen hint s = Some (exist _ v H) ->
      suchThat pred s s v.
    Proof.
      intros.
      simpl.
      constructor; eauto.
    Qed.

    Theorem suchThat_gen0 {T} (pred: Σ -> T -> Prop) {gen: GenPred T Σ pred} :
      forall s v H,
      gen 0%Z s = Some (exist _ v H) ->
      suchThat pred s s v.
    Proof.
      intros.
      eapply suchThat_gen_run; eauto.
    Qed.

    Instance requiv {T}: Equiv (t T) :=
      fun r1 r2 => forall s1 s2 v, r1 s1 s2 v <-> r2 s1 s2 v.

    Ltac inv H :=
      lazymatch type of H with
      | ret _ _ _ _ => apply inv_ret in H; destruct H; subst
      | _ => inversion H; subst; clear H
      end.

    Theorem interpret_sound {T} (tr: transition Σ T):
      forall hints s s' hints' v,
        interpret hints tr s = Some (hints', s', v) ->
        denote tr s s' v.
    Proof.
      induction tr; simpl; intros.
      - destruct_with_eqn (f s).
        inv H.
        eauto using runF_runs.
      - destruct_with_eqn (next_hint hints).
        destruct (genNext z s); [ | congruence ].
        destruct s0.
        inv H.
        eauto using suchThat_runs.
      - destruct_with_eqn (interpret hints tr s); [ | congruence ].
        destruct p as [[hints'' s''] v'].
        eapply IHtr in Heqo.
        eapply H in H0.
        econstructor; eauto.
    Qed.

    Global Instance equiv_Equiv T : Equivalence (@requiv T).
    Proof.
      constructor.
      - firstorder.
      - firstorder.
      - intros r1 r2 r3.
        unfold requiv; intros Heq1 Heq2 **.
        rewrite Heq1.
        apply Heq2.
    Qed.

    Theorem bind_id {T1 T2} (f: T1 -> t T2) x :
      bind (ret x) f ≡ f x.
    Proof.
      intros s1 s2 v.
      split; intros.
      - inv H. inv H0.
        auto.
      - econstructor; eauto.
        econstructor; eauto.
    Qed.

    Theorem bind_id' {T} (r: t T) :
      bind r (fun x => ret x) ≡ r.
    Proof.
      intros s1 s2 v.
      split; intros.
      - inv H. inv H1.
        auto.
      - econstructor; eauto.
        econstructor; eauto.
    Qed.

    Theorem bind_bind {T1 T2 T3} (r1:  t T1) (r2: T1 -> t T2) (r3: T2 -> t T3) :
      forall s1 s2 v, bind (bind r1 r2) r3 s1 s2 v -> bind r1 (fun x => bind (r2 x) r3) s1 s2 v.
    Proof.
      intros s1 s2 v H.
      inv H.
      inv H0.
      eauto using bind_runs.
    Qed.

    Theorem bind_assoc {T1 T2 T3} (r1:  t T1) (r2: T1 -> t T2) (r3: T2 -> t T3) :
      bind (bind r1 r2) r3 ≡ bind r1 (fun x => bind (r2 x) r3).
    Proof.
      intros s1 s2 v.
      split; intros.
      - eauto using bind_bind.
      - inv H.
        inv H1.
        eauto using bind_runs.
    Qed.

    Theorem fmap_ret T1 T2 (f: T1 -> T2) x :
      fmap f (ret x) ≡ ret (f x).
    Proof.
      intros s1 s2 v.
      split; intros.
      - inv H.
        inv H0.
        inv H1.
        econstructor; eauto.
      - inv H.
        econstructor; eauto.
        { econstructor; eauto. }
        { econstructor; eauto. }
    Qed.

    Global Instance bind_respects_equiv {T1 T2} :
      Proper (requiv ==> pointwise_relation _ requiv ==> requiv) (@bind T1 T2).
    Proof.
      unfold Proper, respectful, pointwise_relation.
      intros r1 r1' Heq1 r2 r2' Heq2.
      intros s1 s2 v.
      split; intros.
      - inv H.
        econstructor; eauto.
        { eapply Heq1; eauto. }
        { eapply Heq2; eauto. }
      - inv H.
        econstructor; eauto.
        { eapply Heq1; eauto. }
        { eapply Heq2; eauto. }
    Qed.

    Theorem bind_runF T1 T2 (f: Σ -> Σ * T1) (r: T1 -> t T2) :
      forall s1 s2 v,
        r (f s1).2 (f s1).1 s2 v ->
        bind (runF f) r s1 s2 v.
    Proof.
      intros.
      destruct_with_eqn (f s1); simpl in H.
      eapply bind_runs; eauto.
      econstructor; eauto.
    Qed.

    Theorem inv_bind_runF T1 T2 (f: Σ -> Σ * T1) (r: T1 -> t T2) :
      forall s1 s2 v,
        bind (runF f) r s1 s2 v ->
        r (f s1).2 (f s1).1 s2 v.
    Proof.
      intros.
      inv H.
      inv H0.
      replace (f s1); auto.
    Qed.

    Theorem bind_suchThat T1 T2 (pred: Σ -> T1 -> Prop) (r: T1 -> t T2) :
      forall s1 s2 v x,
        pred s1 x -> r x s1 s2 v ->
        bind (suchThat pred) r s1 s2 v.
    Proof.
      intros.
      econstructor; eauto using suchThat_runs.
    Qed.

    Theorem inv_bind_suchThat T1 T2 (pred: Σ -> T1 -> Prop) (r: T1 -> t T2) :
      forall s1 s2 v,
        bind (suchThat pred) r s1 s2 v ->
        exists x, pred s1 x /\ r x s1 s2 v.
    Proof.
      intros.
      inv H.
      inv H0.
      eauto.
    Qed.

    Theorem bind_runF_runF T1 T2 (f: Σ -> Σ * T1) (rx: T1 -> Σ -> Σ * T2) :
      bind (runF f) (fun x => runF (rx x)) ≡
           runF (fun s => let '(s', x) := f s in
                       rx x s').
    Proof.
      intros s1 s2 v.
      split; intros.
      - inv H.
        inv H0.
        inv H1.
        econstructor.
        replace (f s1).
        auto.
      - inv H.
        destruct_with_eqn (f s1).
        inv Heqp.
        eauto using bind_runs, runF_runs.
    Qed.

  End state.
End relation.

Arguments ifThenElse {Σ} P {_} {T} tr1 tr2.
Arguments ifThenElse_if {Σ} P {_} {T} r1 r2.
Arguments ifThenElse_else {Σ} P {_} {T} r1 r2.

Ltac monad_simpl :=
  unfold check, when;
  repeat match goal with
         | |- relation.bind (relation.bind _ _) _ ?s1 ?s2 ?v =>
           apply relation.bind_assoc
         | |- relation.bind (relation.runF _) _ ?s1 ?s2 ?v =>
           apply relation.bind_runF
         | |- relation.runF _ ?s1 ?s2 ?v =>
           solve [ econstructor; eauto ]
         | [ H: ?mx = Some ?x |- context[unwrap ?mx] ] =>
           rewrite H; cbn [unwrap fst snd]
         | [ |- context[relation.denote (ifThenElse ?P _ _)] ] =>
           rewrite -> (ifThenElse_if P) by eauto; cbn [relation.denote ret undefined]
         | [ |- context[relation.denote (ifThenElse ?P _ _)] ] =>
           rewrite -> (ifThenElse_else P) by eauto; cbn [relation.denote ret undefined]
         end.

Ltac monad_inv :=
  repeat match goal with
         | [ H: (_, _) = (_, _) |- _ ] =>
           inversion H; subst; clear H
         | [ H: relation.bind (relation.runF _) _ ?s1 ?s2 ?v |- _ ] =>
           apply relation.inv_bind_runF in H
         | [ H: relation.runF _ ?s1 ?s2 ?v |- _ ] =>
           apply relation.inv_runF in H; simpl in H; destruct H; subst
         | [ H: relation.suchThat (fun _ _ => False) ?s1 ?s2 ?v |- _ ] =>
           inversion H; contradiction
         | [ H: relation.suchThat _ ?s1 ?s2 ?v |- _ ] =>
           apply relation.inv_suchThat in H; destruct H; subst
         | [ H: relation.bind (relation.bind _ _) _ ?s1 ?s2 ?v |- _ ] =>
           apply relation.bind_bind in H
         | [ H: relation.bind (relation.suchThat ?pred) _ ?s1 ?s2 ?v |- _ ] =>
           let pred := (eval hnf in pred) in
           lazymatch pred with
           | fun _ x => _ =>
             let x := fresh x in
             let H' := fresh in
             apply relation.inv_bind_suchThat in H;
             destruct H as [x [H' H]]
           end
         | [ H: ?mx = Some ?x, H': context[unwrap ?mx] |- _ ] =>
           rewrite H in H'; cbn [fst snd unwrap] in H'
         | [ H: context[relation.denote (check ?P)] |- _ ] =>
           unfold check in H
         | [ H: context[relation.denote (when ?P _)] |- _ ] =>
           unfold when in H
         | [ H: context[relation.denote (ifThenElse ?P _ _)] |- _ ] =>
           rewrite -> (ifThenElse_if P) in H by eauto; cbn [relation.denote ret undefined] in H
         | [ H: context[relation.denote (ifThenElse ?P _ _)] |- _ ] =>
           rewrite -> (ifThenElse_else P) in H by eauto; cbn [relation.denote ret undefined] in H
         end.
