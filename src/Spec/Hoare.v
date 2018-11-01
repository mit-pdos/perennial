Require Import Spec.Proc Spec.ProcTheorems.
Require Import Tactical.Propositional.
Require Import Helpers.RelationAlgebra.

Import RelationNotations.

(** Defining specifications, which are just convenient ways to express program
behavior. *)

Record SpecProps T R State :=
  { pre: Prop;
    post: State -> T -> Prop;
    recovered: State -> R -> Prop; }.

Definition Specification A T R State := A -> State -> SpecProps T R State.

Definition spec_exec A T R State (spec: Specification A T R State) :
  relation State State T :=
  fun s s' r => forall a,
    (spec a s).(pre) -> (spec a s).(post) s' r.

Definition spec_rexec A T R State (spec: Specification A T R State) :
  relation State State R :=
  fun s s' r => forall a,
    (spec a s).(pre) -> (spec a s).(recovered) s' r.

Definition spec_impl A A'
           `(spec1: Specification A' T R State)
           `(spec2: Specification A T R State) :=
  forall a s, (spec2 a s).(pre) ->
         exists a', (spec1 a' s).(pre) /\
               (forall s' v, (spec1 a' s).(post) s' v ->
                        (spec2 a s).(post) s' v) /\
               (forall s' rv, (spec1 a' s).(recovered) s' rv ->
                         (spec2 a s).(recovered) s' rv).

Definition op_spec `(sem: Dynamics Op State) `(op : Op T) : Specification unit T unit State :=
  fun (_:unit) state =>
    {|
      pre := True;
      post :=
        fun state' v => sem.(step) op state state' v;
      recovered :=
        fun state' r =>
          r = tt /\ (state' = state \/ exists v, sem.(step) op state state' v);
    |}.


Section Hoare.
  Context `(sem: Dynamics Op State).
  Notation proc := (proc Op).
  Notation exec := sem.(exec).
  Notation rexec := sem.(rexec).

  Definition proc_ok A T R
             (p: proc T) (rec: proc R)
             (spec: Specification A T R State) :=
    exec p ---> spec_exec spec /\
    rexec p rec ---> spec_rexec spec.

  Theorem proc_ok_expand A T R
          (p: proc T) (rec: proc R)
          (spec: Specification A T R State) :
    proc_ok p rec spec <->
    forall a s,
      (spec a s).(pre) ->
      (forall s' v, exec p s s' v ->
               (spec a s).(post) s' v) /\
      (forall s' rv, rexec p rec s s' rv ->
                (spec a s).(recovered) s' rv).
  Proof.
    unfold proc_ok, rimpl, spec_exec, spec_rexec; split; intros.
    - intuition eauto 10.
    - split; intros.
      specialize (H a x); intuition eauto.
      specialize (H a x); intuition eauto.
  Qed.

  Theorem spec_impl_relations A A'
          `(spec1: Specification A' T R State)
          `(spec2: Specification A T R State)
          p rec :
    spec_impl spec1 spec2 ->
    proc_ok p rec spec1 ->
    proc_ok p rec spec2.
  Proof.
    unfold spec_impl; intros.
    pose proof (proj1 (proc_ok_expand _ _ _) H0); clear H0.
    apply proc_ok_expand; intros.
    specialize (H a s); propositional.
    specialize (H1 a' s); propositional.
    eauto 10.
  Qed.

  Theorem proc_ok_exec_equiv A T `(spec: Specification A T R State)
          (p p': proc T) `(rec: proc R):
      exec_equiv sem p p' ->
      proc_ok p' rec spec ->
      proc_ok p rec spec.
  Proof. unfold proc_ok. intros ->; auto. Qed.

  Theorem proc_ok_rx A T A' T' R `(spec: Specification A T R State)
                           `(p: proc T) `(rec: proc R)
                           `(rx: T -> proc T')
                           `(spec': Specification A' T' R State):
      proc_ok p rec spec ->
      (forall a' state, pre (spec' a' state) ->
               exists a, pre (spec a state) /\
                    (forall r,
                        proc_ok (rx r) rec
                          (fun (_:unit) state' =>
                             {| pre := post (spec a state) state' r;
                                post :=
                                  fun (state'' : State) r =>
                                    post (spec' a' state) state'' r;
                                recovered :=
                                  fun (state'' : State) r =>
                                    recovered (spec' a' state) state'' r |})
                    ) /\
                    (forall (r: R) (state': State), recovered (spec a state) state' r ->
                             recovered (spec' a' state) state' r)) ->
      proc_ok (Bind p rx) rec spec'.
  Proof.
    unfold proc_ok at 3. intros (Hp_ok&Hp_rec) Hrx.
    split.
    - simpl; setoid_rewrite Hp_ok.
      intros state state' t' (t&(state_mid&Hspec_mid&Hexec_mid)) a' Hpre'.
      specialize (Hrx _ _ Hpre') as (a&Hpre&Hok&Hrec).
      specialize (Hok t). rewrite proc_ok_expand in Hok.
      destruct (Hok tt state_mid) as (Hrx_ok&Hrx_rec); simpl; eauto.
    - rewrite rexec_unfold. rewrite rexec_unfold in Hp_rec.
      simpl. rewrite exec_crash_idem, bind_dist_r.
      apply rel_or_elim.
      + rewrite Hp_rec; auto.
        intros state state' r Hspec_rexec a' Hpre'.
        specialize (Hrx _ _ Hpre') as (a&Hpre&?&Hrec); eauto.
      + rewrite bind_assoc, Hp_ok.
        intros state state' t' (t&(state_mid&Hspec_mid&Hcrash_mid)) a' Hpre'.
      specialize (Hrx _ _ Hpre') as (a&Hpre&Hok&Hrec).
      specialize (Hok t). rewrite proc_ok_expand in Hok.
      destruct (Hok tt state_mid) as (Hrx_ok&Hrx_rec); simpl; eauto.
  Qed.

  (** ** Reasoning about the [Ret] return operation.

  The simplest procedure we can construct in our model is
  the return operation, [Ret].  Writing a specification for
  [Ret] should be intuitively straightforward, but turns out
  to be slightly complicated by the possibility of crashes.
  The [rec_noop] definition below captures this notion: a
  [Ret v] procedure has no precondition, and has a simple
  postcondition (the state does not change and the return
  value is [v]), but in case of a crash, the state is wiped
  according to some [wipe] relation.

  [rec_noop] is a proposition that states that [Ret v] actually
  meets this specification.  Proving [rec_noop] will be a
  proof obligation, and boils down to showing that the recovery
  procedure [rec] corresponds to the wipe relation [wipe].
   *)

  Definition rec_noop `(rec: proc R) (wipe: State -> State -> Prop) :=
    forall T (v:T),
      proc_ok
        (Ret v) rec
        (fun (_:unit) state =>
           {| pre := True;
              post := fun state' r => r = v /\
                                      state' = state;
              recovered := fun state' _ => wipe state state'; |}).

  Definition proc_loopspec A `(rec': proc unit) `(rec: proc unit)
             `(spec: Specification A unit unit State):=
    (pure tt + rexec rec' rec);; exec rec' ---> spec_exec spec.

  (** A more general theorem about specifications for [Ret], which
    we will use as part of our proof automation, says
    that [Ret v] meets a specification [spec] if the [rec_noop]
    theorem holds (i.e., the recovery procedure is correctly
    described by a wipe relation [wipe]), and the specification
    [spec] matches the [wipe] relation:
   *)

  Theorem ret_spec A T R (wipe: State -> State -> Prop) `(spec: Specification A T R State)
          (v:T) (rec: proc R):
    rec_noop rec wipe ->
    (forall a state, pre (spec a state) ->
                     post (spec a state) state v /\
                     forall state', wipe state state' ->
                                    forall (r : R), recovered (spec a state) state' r) ->
    proc_ok (Ret v) rec spec .
  Proof.
    unfold proc_ok; intros Hnoop Himpl; split.
    - intros state state' t Hexec a Hpre.
      inversion Hexec; subst. specialize (Himpl _ _ Hpre). intuition.
    - destruct (Hnoop _ v) as (?&->).
      unfold spec_rexec.
      intros s s' r Hl a Hpre. specialize (Hl tt).
      eapply Himpl; eauto.
      eapply Hl; simpl; eauto.
  Qed.

  (** Define what it means for a spec to be idempotent: *)
  Definition idempotent A T `(spec: Specification A T unit State) :=
    forall a state,
      pre (spec a state) ->
      forall v state', recovered (spec a state) state' v ->
              (** idempotency: recovered condition implies precondition to
                 re-run on every crash *)
              exists a', pre (spec a' state') /\
                    (** postcondition transitivity: establishing the
                       postcondition from a recovered state is sufficient to
                       establish it with respect to the original initial
                       state (note all with the same ghost state) *)
                    forall rv state'', post (spec a' state') state'' rv ->
                                  post (spec a state) state'' rv.


  (* Idempotents theorem: *)
  Theorem idempotent_loopspec A `(rec: proc unit) `(rec': proc unit)
        `(spec: Specification A unit unit State)
        (Hspec: proc_ok rec' rec spec):
        idempotent spec ->
        proc_loopspec rec' rec spec.
  Proof.
    unfold proc_loopspec; intros.
    destruct Hspec as (Hse&Hsr).
    rewrite Hsr.
    rewrite bind_dist_r.
    apply rel_or_elim.
    - rewrite bind_left_id; eauto.
    - setoid_rewrite Hse.
      intros s s'' tt Hrs a Hpre.
      inversion Hrs as ([]&s'&Hrs'&?).
      specialize (Hrs' a Hpre). unfold idempotent in H.
      edestruct H as (a'&Hpre'&Hpost); eauto.
  Qed.

  Theorem compose_recovery A A' A'' `(spec: Specification A'' T unit State)
                               `(rspec: Specification A' unit unit State)
                               `(spec': Specification A T unit State)
                               `(p: proc T) `(rec: proc unit) `(rec': proc unit)
        (Hspec: proc_ok p rec spec)
        (Hrspec: proc_loopspec rec' rec rspec)
        (Hspec_spec':
           forall (a:A) state, pre (spec' a state) ->
                      exists (a'':A''),
                        pre (spec a'' state) /\
                        (forall v state', post (spec a'' state) v state' ->
                                 post (spec' a state) v state') /\
                        (forall v state', recovered (spec a'' state) state' v ->
                                 exists a', pre (rspec a' state') /\
                                       forall v' state'',
                                         post (rspec a' state') state'' v' ->
                                         recovered (spec' a state) state'' v')):
        proc_ok p (Bind rec (fun _ => rec')) spec'.
  Proof.
    unfold proc_ok; intros; split.
    - destruct Hspec as (->&?).
      intros s s' t Hspec a Hpre.
      edestruct Hspec_spec' as (a''&?&Hp&?); eauto.
    - unfold rexec; simpl. unfold exec_recover; simpl.
      unfold proc_loopspec in Hrspec.
      unfold rexec in Hrspec. unfold exec_recover in Hrspec.
      destruct Hspec as (?&Hrec).
      unfold rexec in Hrec. unfold exec_recover in Hrec.
      setoid_rewrite bind_dist_r.
      setoid_rewrite bind_dist_r.
      setoid_rewrite bind_left_id.

      (* Base case *)
      assert (_ <- exec_crash sem p;
              _ <- sem.(crash_step);
              _ <- exec rec;
              exec rec'
                   --->
                   spec_rexec spec').
      { setoid_rewrite <-seq_star_none in Hrec.
        setoid_rewrite bind_identity in Hrec; [| exact tt].
        setoid_rewrite <-rel_or_introl in Hrspec.
        rewrite bind_left_id in Hrspec.
        setoid_rewrite Hrspec.
        setoid_rewrite <-bind_assoc.
        setoid_rewrite <-bind_assoc.
        setoid_rewrite bind_assoc at 2.
        rewrite Hrec.
        intros s1 s3 [] Hl a Hpre.
        destruct Hl as ([]&s2&Hrexec_spec&?Hexec_rspec).
        edestruct Hspec_spec' as (?&?&?&Hrec'); eauto.
        edestruct Hrec'.
        { eapply Hrexec_spec; eauto. }
        destruct H2 as (?&?). eapply H3. eapply Hexec_rspec. eauto.
      }
  Abort.

  Theorem op_spec_correct T (op: Op T) rec (* (wipe: State -> State -> Prop) *):
    rec_noop rec eq ->
    proc_ok (Prim op) rec (op_spec sem op).
  Proof.
    unfold proc_ok; intros Hnoop; split.
    - intros state state' t Hexec a Hpre; eauto.
    - unfold rexec, spec_rexec.
      simpl. rewrite bind_dist_r. apply rel_or_elim.
      * destruct (Hnoop _ tt) as (?&->).
        intros s s' [] Hl a Hpre. specialize (Hl tt).
        split; eauto. intuition.
      * rewrite bind_assoc.
        destruct (Hnoop _ tt) as (?&Hr).
        setoid_rewrite Hr.
        unfold spec_rexec.
        intros s s' [] Hl a Hpre.
        inversion Hl as (?&?&?&Hrest). specialize (Hrest tt I). split; eauto.
        right.  eexists; eauto. simpl in Hrest. subst. eauto.
  Qed.


  (** In some situations, the precondition of a specification
    may define variables or facts that you want to [intros].
    Here we define several helper theorems and an Ltac tactic, [spec_intros],
    that does so.  This is done by changing the specification's precondition
    from an arbitrary Prop (i.e., [pre]) into a statement that there's
    some state [state0] such that [state = state0], and [intros]ing the
    arbitrary Prop in question as a hypothesis about [state0].
  *)

  Theorem spec_intros A T R `(spec: Specification A T R State)
          `(p: proc T) `(rec: proc R):
      (forall a state0,
          pre (spec a state0) ->
          proc_ok p rec
            (fun (_:unit) state =>
               {| pre := state = state0;
                  post :=
                    fun state' r => post (spec a state) state' r;
                  recovered :=
                    fun state' r => recovered (spec a state) state' r;
               |})) ->
      proc_ok p rec spec.
  Proof.
    unfold proc_ok at 2; intros H.
    split; intros s s' r Hexec a Hpre; eapply H; simpl; eauto using tt.
  Qed.


End Hoare.

Ltac spec_intros := intros; eapply spec_intros; intros.
