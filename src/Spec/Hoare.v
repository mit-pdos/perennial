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

End Hoare.
