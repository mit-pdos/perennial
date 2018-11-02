Require Import Spec.Proc Spec.ProcTheorems.
Require Import Tactical.Propositional.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationRewriting.

Import RelationNotations.

(** Defining specifications, which are just convenient ways to express program
behavior. *)

Record SpecProps T R State :=
  { pre: Prop;
    post: State -> T -> Prop;
    alternate: State -> R -> Prop; }.

Definition Specification T R State := State -> SpecProps T R State.

Definition spec_exec T R State (spec: Specification T R State) :
  relation State State T :=
  fun s s' r => (spec s).(pre) -> (spec s).(post) s' r.

Definition spec_aexec T R State (spec: Specification T R State) :
  relation State State R :=
  fun s s' r => (spec s).(pre) -> (spec s).(alternate) s' r.

Definition spec_impl
           `(spec1: Specification T R State)
           `(spec2: Specification T R State) :=
  forall s, (spec2 s).(pre) -> (spec1 s).(pre) /\
            (forall s' v, (spec1 s).(post) s' v ->
                          (spec2 s).(post) s' v) /\
            (forall s' rv, (spec1 s).(alternate) s' rv ->
                           (spec2 s).(alternate) s' rv).

Definition op_spec `(sem: Dynamics Op State) `(op : Op T) : Specification T unit State :=
  fun state =>
    {|
      pre := True;
      post :=
        fun state' v => sem.(step) op state state' v;
      alternate :=
        fun state' r =>
          r = tt /\ (state' = state \/ exists v, sem.(step) op state state' v);
    |}.


Section Hoare.
  Context `(sem: Dynamics Op State).
  Notation proc := (proc Op).
  Notation exec := sem.(exec).
  Notation exec_crash := sem.(exec_crash).
  Notation crash_step := sem.(crash_step).
  Notation rexec := sem.(rexec).

  Definition proc_rspec T R
             (p: proc T) (rec: proc R)
             (spec: Specification T R State) :=
    exec p ---> spec_exec spec /\
    rexec p rec ---> spec_aexec spec.

  Definition proc_cspec T
             (p: proc T)
             (spec: Specification T unit State) :=
    exec p ---> spec_exec spec /\
    exec_crash p ---> spec_aexec spec.

  Theorem proc_rspec_expand T R
          (p: proc T) (rec: proc R)
          (spec: Specification T R State) :
    proc_rspec p rec spec <->
    forall s,
      (spec s).(pre) ->
      (forall s' v, exec p s s' v ->
               (spec s).(post) s' v) /\
      (forall s' rv, rexec p rec s s' rv ->
                (spec s).(alternate) s' rv).
  Proof.
    unfold proc_rspec, rimpl, spec_exec, spec_aexec; split; intros.
    - intuition eauto 10.
    - split; intros x y ?.
      specialize (H x); intuition eauto.
      specialize (H x); intuition eauto.
  Qed.

  Theorem proc_cspec_expand T (p: proc T)
          (spec: Specification T unit State) :
    proc_cspec p spec <->
    forall s,
      (spec s).(pre) ->
      (forall s' v, exec p s s' v ->
               (spec s).(post) s' v) /\
      (forall s' rv, exec_crash p s s' rv ->
                (spec s).(alternate) s' rv).
  Proof.
    unfold proc_cspec, rimpl, spec_exec, spec_aexec; split; intros.
    - intuition eauto 10.
    - split; intros x y ?.
      specialize (H x); intuition eauto.
      specialize (H x); intuition eauto.
  Qed.

  Theorem proc_rspec_impl
          `(spec1: Specification T R State)
          `(spec2: Specification T R State)
          p rec :
    spec_impl spec1 spec2 ->
    proc_rspec p rec spec1 ->
    proc_rspec p rec spec2.
  Proof.
    unfold spec_impl; intros.
    pose proof (proj1 (proc_rspec_expand _ _ _) H0); clear H0.
    apply proc_rspec_expand; intros.
    specialize (H s); propositional.
    specialize (H1 s); propositional.
    eauto 10.
  Qed.

  Theorem proc_cspec_impl
          `(spec1: Specification T unit State)
          `(spec2: Specification T unit State)
          p :
    spec_impl spec1 spec2 ->
    proc_cspec p spec1 ->
    proc_cspec p spec2.
  Proof.
    unfold spec_impl; intros.
    pose proof (proj1 (proc_cspec_expand _ _) H0); clear H0.
    apply proc_cspec_expand; intros.
    firstorder.
  Qed.

  Theorem proc_rspec_exec_equiv T `(spec: Specification T R State)
          (p p': proc T) `(rec: proc R):
      exec_equiv sem p p' ->
      proc_rspec p' rec spec ->
      proc_rspec p rec spec.
  Proof. unfold proc_rspec. intros ->; auto. Qed.

  Theorem proc_cspec_exec_equiv T `(spec: Specification T unit State)
          (p p': proc T):
      exec_equiv sem p p' ->
      proc_cspec p' spec ->
      proc_cspec p spec.
  Proof. unfold proc_cspec. intros ->; auto. Qed.

  Theorem proc_rspec_rx T T' R `(spec: Specification T R State)
                           `(p: proc T) `(rec: proc R)
                           `(rx: T -> proc T')
                           `(spec': Specification T' R State):
      proc_rspec p rec spec ->
      (forall state, pre (spec' state) -> pre (spec state) /\
                    (forall r,
                        proc_rspec (rx r) rec
                          (fun state' =>
                             {| pre := post (spec state) state' r;
                                post :=
                                  fun (state'' : State) r =>
                                    post (spec' state) state'' r;
                                alternate :=
                                  fun (state'' : State) r =>
                                    alternate (spec' state) state'' r |})
                    ) /\
                    (forall (r: R) (state': State), alternate (spec state) state' r ->
                             alternate (spec' state) state' r)) ->
      proc_rspec (Bind p rx) rec spec'.
  Proof.
    unfold proc_rspec at 3. intros (Hp_ok&Hp_rec) Hrx.
    split.
    - simpl; rew Hp_ok.
      intros state state' t' (t&(state_mid&Hspec_mid&Hexec_mid)) Hpre'.
      specialize (Hrx _ Hpre') as (Hpre&Hok&Hrec).
      specialize (Hok t). rewrite proc_rspec_expand in Hok.
      destruct (Hok state_mid) as (Hrx_ok&Hrx_rec); simpl; eauto.
    - rewrite rexec_unfold. rewrite rexec_unfold in Hp_rec.
      simpl. rewrite exec_crash_idem, bind_dist_r.
      apply rel_or_elim.
      + rewrite Hp_rec; auto.
        intros state state' r Hspec_aexec Hpre'.
        specialize (Hrx _ Hpre') as (Hpre&?&Hrec); eauto.
      + rewrite bind_assoc, Hp_ok.
        intros state state' t' (t&(state_mid&Hspec_mid&Hcrash_mid)) Hpre'.
      specialize (Hrx _ Hpre') as (Hpre&Hok&Hrec).
      specialize (Hok t). rewrite proc_rspec_expand in Hok.
      destruct (Hok state_mid) as (Hrx_ok&Hrx_rec); simpl; eauto.
  Qed.

  Theorem proc_cspec_rx T T' `(spec: Specification T unit State)
                           `(p: proc T)
                           `(rx: T -> proc T')
                           `(spec': Specification T' unit State):
      proc_cspec p spec ->
      (forall state, pre (spec' state) -> pre (spec state) /\
                    (forall r,
                        proc_cspec (rx r)
                          (fun state' =>
                             {| pre := post (spec state) state' r;
                                post :=
                                  fun (state'' : State) r =>
                                    post (spec' state) state'' r;
                                alternate :=
                                  fun (state'' : State) r =>
                                    alternate (spec' state) state'' r |})
                    ) /\
                    (forall (r:  unit) (state': State), alternate (spec state) state' r ->
                             alternate (spec' state) state' r)) ->
      proc_cspec (Bind p rx) spec'.
  Proof.
    unfold proc_cspec at 3. intros (Hp_ok&Hp_rec) Hrx.
    split.
    - simpl; rew Hp_ok.
      intros state state' t' (t&(state_mid&Hspec_mid&Hexec_mid)) Hpre'.
      specialize (Hrx _ Hpre') as (Hpre&Hok&Hrec).
      specialize (Hok t). rewrite proc_cspec_expand in Hok.
      destruct (Hok state_mid) as (Hrx_ok&Hrx_rec); simpl; eauto.
    - simpl. rewrite exec_crash_idem.
      apply rel_or_elim.
      + rewrite Hp_rec; auto.
        intros state state' r Hspec_aexec Hpre'.
        specialize (Hrx _ Hpre') as (Hpre&?&Hrec); eauto.
      + rewrite Hp_ok.
        intros state state' t' (t&(state_mid&Hspec_mid&Hcrash_mid)) Hpre'.
        specialize (Hrx _ Hpre') as (Hpre&Hok&Hrec).
        specialize (Hok t). rewrite proc_cspec_expand in Hok.
        destruct (Hok state_mid) as (Hrx_ok&Hrx_rec); simpl; eauto.
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
      proc_rspec
        (Ret v) rec
        (fun state =>
           {| pre := True;
              post := fun state' r => r = v /\
                                      state' = state;
              alternate := fun state' _ => wipe state state'; |}).


  (** A more general theorem about recovery specifications for [Ret], which
    we will use as part of our proof automation, says
    that [Ret v] meets a specification [spec] if the [rec_noop]
    theorem holds (i.e., the recovery procedure is correctly
    described by a wipe relation [wipe]), and the specification
    [spec] matches the [wipe] relation:
   *)

  Theorem ret_rspec T R (wipe: State -> State -> Prop) `(spec: Specification T R State)
          (v:T) (rec: proc R):
    rec_noop rec wipe ->
    (forall state, pre (spec state) ->
                     post (spec state) state v /\
                     forall state', wipe state state' ->
                                    forall (r : R), alternate (spec state) state' r) ->
    proc_rspec (Ret v) rec spec .
  Proof.
    unfold proc_rspec; intros Hnoop Himpl; split.
    - intros state state' t Hexec Hpre.
      inversion Hexec; subst. specialize (Himpl _ Hpre). intuition.
    - destruct (Hnoop _ v) as (?&->).
      unfold spec_aexec. firstorder.
  Qed.

  Theorem ret_cspec T `(spec: Specification T unit State)
          (v:T):
    (forall state, pre (spec state) ->
                     post (spec state) state v /\
                     alternate (spec state) state tt) ->
    proc_cspec (Ret v) spec .
  Proof.
    unfold proc_cspec; intros Himpl; split;
    intros state state' t Hexec Hpre;
    inversion Hexec; subst; specialize (Himpl _ Hpre); intuition.
  Qed.

  (** Define what it means for a spec to be idempotent: *)
  Definition idempotent A T R `(spec: A -> Specification T R State) :=
    forall a state, pre (spec a state) ->
      forall v state', alternate (spec a state) state' v -> 
              (** idempotency: alternate condition implies precondition to
                 re-run on every crash *)
              exists a', pre (spec a' state') /\
                    (** postcondition transitivity: establishing the
                       postcondition from a alternate state is sufficient to
                       establish it with respect to the original initial
                       state (note all with the same ghost state) *)
                    forall rv state'', post (spec a' state') state'' rv ->
                                  post (spec a state) state'' rv.

  Definition idempotent_crash_step A T R `(spec: A -> Specification T R State) :=
    forall a state,
      pre (spec a state) ->
      forall v state' state'', alternate (spec a state) state' v ->
                               crash_step state' state'' tt ->
               exists a', pre (spec a' state'') /\
                    forall rv state''', post (spec a' state'') state''' rv ->
                                  post (spec a state) state''' rv.

  (** In some situations, the precondition of a specification
    may define variables or facts that you want to [intros].
    Here we define several helper theorems and an Ltac tactic, [spec_intros],
    that does so.  This is done by changing the specification's precondition
    from an arbitrary Prop (i.e., [pre]) into a statement that there's
    some state [state0] such that [state = state0], and [intros]ing the
    arbitrary Prop in question as a hypothesis about [state0].
  *)

  Theorem rspec_intros T R `(spec: Specification T R State)
          `(p: proc T) `(rec: proc R):
      (forall state0,
          pre (spec state0) ->
          proc_rspec p rec
            (fun state =>
               {| pre := state = state0;
                  post :=
                    fun state' r => post (spec state) state' r;
                  alternate :=
                    fun state' r => alternate (spec state) state' r;
               |})) ->
      proc_rspec p rec spec.
  Proof.
    unfold proc_rspec at 2; intros H.
    split; intros s s' r Hexec Hpre; eapply H; simpl; eauto.
  Qed.

  Theorem cspec_intros T `(spec: Specification T unit State)
          `(p: proc T):
      (forall state0,
          pre (spec state0) ->
          proc_cspec p
            (fun state =>
               {| pre := state = state0;
                  post :=
                    fun state' r => post (spec state) state' r;
                  alternate :=
                    fun state' r => alternate (spec state) state' r;
               |})) ->
      proc_cspec p spec.
  Proof.
    unfold proc_cspec at 2; intros H.
    split; intros s s' r Hexec Hpre; eapply H; simpl; eauto using tt.
  Qed.

  (*
  Theorem op_spec_correct T (op: Op T) rec (* (wipe: State -> State -> Prop) *):
    rec_noop rec eq ->
    proc_rspec (Prim op) rec (op_spec sem op).
  Proof.
    unfold proc_rspec; intros Hnoop; split.
    - intros state state' t Hexec a Hpre; eauto.
    - unfold rexec, spec_aexec.
      simpl. rewrite bind_dist_r. apply rel_or_elim.
      * destruct (Hnoop _ tt) as (?&->).
        intros s s' [] Hl a Hpre. specialize (Hl tt).
        split; eauto. intuition.
      * rewrite bind_assoc.
        destruct (Hnoop _ tt) as (?&Hr).
        setoid_rewrite Hr.
        unfold spec_aexec.
        intros s s' [] Hl a Hpre.
        inversion Hl as (?&?&?&Hrest). specialize (Hrest tt I). split; eauto.
        right.  eexists; eauto. simpl in Hrest. subst. eauto.
  Qed.
   *)

  Theorem op_spec_correct T (op: Op T):
    proc_cspec (Prim op) (op_spec sem op).
  Proof.
    unfold proc_cspec; split.
    - intros state state' t Hexec Hpre; eauto.
    - simpl. apply rel_or_elim.
      * intros s s' [] Hl Hpre. simpl. split; auto.
        firstorder.
      * intros s s' [] Hl Hpre.
        inversion Hl as (?&?&?&Hrest). inversion Hrest; subst.
        firstorder.
  Qed.

  (*
  Theorem proc_cspec_to_rspec A A' T R (cspec: Specification A T unit State)
          `(rec_cspec: Specification A' R unit State)
          `(rspec: Specification A' T R State)
          `(p: proc T) `(rec: proc R):
    proc_cspec p cspec ->
    proc_cspec rec rec_cspec ->
    idempotent_crash_step rec_cspec ->
    (forall a s, (rspec a s).(pre) ->
         exists a', (cspec a' s).(pre) /\
               (forall s' v, (cspec a' s).(post) s' v ->
                        (rspec a s).(post) s' v)) ->
    (* alternate of cspec followed by crash implies pre of rec but bad ghost state *)
    (forall a' state state' state'' v, exists a, alternate (cspec a state) state' v ->
                               crash_step state' state'' tt ->
                 pre (rec_cspec a' state'')) ->
    (* recovery post implies alternate of rspec but is ghost state handled correctly? *)
    (forall a s sc, (rspec a s).(pre) ->
                    exists a', (forall sfin rv, (rec_cspec a' sc).(post) sfin rv ->
                                                (rspec a s).(alternate) sfin rv)) ->
    proc_rspec p rec rspec.
  Proof.
    intros (Hpe&Hpc) (Hre&Hrc).
    unfold idempotent_crash_step. intros Hidemp.
    intros Himpl1 Hc_crash_r Hr_alt.
    split.
    - rew Hpe; auto.
      intros s1 s2 t Hl a' Hpre.
      edestruct Himpl1 as (?&?&?); eauto.
    - unfold rexec. rewrite Hpc.
      unfold exec_recover.
      setoid_rewrite Hrc.

      (* Base case *)
      assert (_ <- spec_aexec cspec;
              _ <- crash_step;
              exec rec
                   --->
                   spec_aexec rspec).
      {  intros s s' r Hl a' Hpre.
         destruct Hl as ([]&smid1&Haexec&Hcrash).
         destruct Hcrash as ([]&smid2&Hcrash&Hexec).
         edestruct Hr_alt as (a''&Hfin); eauto. eapply Hfin.
         eapply Hre; eauto.
           edestruct Himpl1 as (?&?&?); eauto.
         edestruct Hc_crash_r; eauto.
         eapply H1; eauto.
         eapply Haexec.
         (* Bad quantifiers on the ghost state. *)
         admit.
      }
   Abort.
   *)


End Hoare.

Ltac spec_intros := intros; first [ eapply rspec_intros | eapply cspec_intros ] ; intros.
