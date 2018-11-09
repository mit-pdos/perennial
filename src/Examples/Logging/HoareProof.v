Require Import POCS.
Require Import Spec.HoareTactics.

Require Import Examples.Logging.Impl.
Require Import Examples.Logging.LogLayout.
Require Import Examples.Logging.LogicalLog.

Local Notation proc_rspec := (Hoare.proc_rspec D.ODLayer.(sem)).
Local Arguments Hoare.proc_rspec {Op State} sem {T R}.

Definition logical_abstraction (d: D.State) ps ls :=
  PhyDecode d ps /\
  LogDecode ps ls /\
  ls.(ls_committed) = false.

Local Hint Resolve recovery_ok.
Local Hint Resolve log_apply_spec_idempotent_crash_step_notxn'.
Local Hint Resolve log_apply_spec_idempotent_crash_step'.

Definition general_rspec ls0 T (p_cspec: Specification T unit D.State) :=
  proc_cspec_to_rspec
    (sem:=D.ODLayer.(sem))
    (p_cspec:=p_cspec)
    (rec_cspec:=fun (a: Recghost (fun ls =>
                                  if ls.(ls_committed) then
                                    massign ls.(ls_log) ls.(ls_disk) =
                                    massign ls0.(ls_log) ls0.(ls_disk)
                                  else ls.(ls_disk) = ls0.(ls_disk) \/
                                       ls.(ls_disk) = massign ls0.(ls_log) ls0.(ls_disk))) =>
                  let 'recghost ps ls _ := a in
                  log_apply_spec ps ls ls.(ls_disk) ls.(ls_committed)).


Definition mk_rspec ls0 T (p_cspec: Specification T unit D.State) :=
  proc_cspec_to_rspec
    (sem:=D.ODLayer.(sem))
    (p_cspec:=p_cspec)
    (rec_cspec:=fun (a: Recghost (fun ls => ls.(ls_disk) = ls0.(ls_disk))) =>
                  let 'recghost ps ls _ := a in
                  log_apply_spec ps ls ls.(ls_disk) false).

Local Hint Resolve log_read_ok.

Definition log_read_rec_ok ps ls a :
  proc_rspec
    (log_read a)
    (recovery)
    (fun state =>
       {| pre := logical_abstraction state ps ls;
          post state' r :=
            state' = state /\
            index ls.(ls_disk) a ?|= eq r;
          alternate state' r :=
            exists ps',
              logical_abstraction
                state' ps'
                {| ls_committed := false;
                   ls_log := nil;
                   ls_disk := ls.(ls_disk); |}
       |}).
Proof.
  eapply mk_rspec; eauto; simpl in *; propositional;
    repeat match goal with
           | [ x: Recghost _ |- _ ] => destruct x
           end;
    eauto.
  - inv_clear H1.
    eexists (recghost _ _ _); simpl; intuition eauto.
  - simpl in H0; propositional.
    unfold logical_abstraction.
    descend; intuition eauto.
    rewrite <- pf.
    eassumption.

    Grab Existential Variables.
    simpl; auto.
Qed.

Local Hint Resolve log_write_ok.

Definition log_write_rec_ok ps ls a v :
  proc_rspec
    (log_write a v)
    (recovery)
    (fun state =>
       {| pre := logical_abstraction state ps ls;
          post state' r :=
            exists ps',
              match r with
              | TxnD.WriteOK =>
                logical_abstraction
                  state' ps'
                  {| ls_committed := false;
                     ls_log := ls.(ls_log) ++ (a,v)::nil;
                     ls_disk := ls.(ls_disk); |}
              | TxnD.WriteErr =>
                logical_abstraction
                  state' ps'
                  {| ls_committed := false;
                     ls_log := ls.(ls_log);
                     ls_disk := ls.(ls_disk); |}
              end;
          alternate state' r :=
            exists ps',
              logical_abstraction state' ps'
                                  {| ls_committed := false;
                                     ls_log := nil;
                                     ls_disk := ls.(ls_disk) |};
       |}).
Proof.
  eapply mk_rspec; eauto; simpl in *; propositional;
    repeat match goal with
           | [ x: Recghost _ |- _ ] => destruct x
           end;
    eauto.
  - unfold logical_abstraction in *; intuition eauto.
    destruct v0; propositional; descend; intuition eauto.
    destruct ls; simpl in *; congruence.
  - inv_clear H1.
    eexists (recghost _ _ _); simpl; intuition eauto.
  - simpl in H0; propositional.
    unfold logical_abstraction.
    descend; intuition eauto.
    rewrite <- pf; eassumption.

    Grab Existential Variables.
    simpl; auto.
Qed.

Local Hint Resolve log_commit_ok.

Definition commit_ok ps ls :
  proc_rspec
    (commit)
    (recovery)
    (fun state =>
       {| pre := logical_abstraction state ps ls;
          post state' r :=
            exists ps',
              logical_abstraction
                state' ps'
                {| ls_committed := false;
                   ls_log := nil;
                   ls_disk := massign ls.(ls_log) ls.(ls_disk) |};
          alternate state' r :=
            exists ps',
              logical_abstraction
                state' ps'
                {| ls_committed := false;
                   ls_log := nil;
                   ls_disk := ls.(ls_disk) |} \/
              logical_abstraction
                state' ps'
                {| ls_committed := false;
                   ls_log := nil;
                   ls_disk := massign ls.(ls_log) ls.(ls_disk) |};
       |}).
Proof.
  eapply general_rspec; eauto; simpl; propositional.
  - destruct a; eauto.
  - unfold logical_abstraction in *; intuition eauto.
    propositional.
    descend; intuition eauto.
    destruct ls'; simpl in *; congruence.
  - inv_clear H1.
    split_cases;
      lazymatch goal with
      | [ H: PhyDecode state'' ?ps,
             H': LogDecode ?ps ?ls |- _ ] =>
        unshelve eexists (recghost ps ls _); simpl; eauto
      end.
  - destruct a; simpl in *; propositional.
    exists ps'.
    destruct_with_eqn (ls0.(ls_committed));
      unfold logical_abstraction in *; simpl; propositional.
    + right; split_cases; finish.
    + split_cases.
      left; split_cases; finish.
      right; split_cases; finish.
Qed.

Local Hint Resolve log_size_ok.

Definition log_size_rec_ok ps ls :
  proc_rspec
    (log_size)
    (recovery)
    (fun state =>
       {| pre := logical_abstraction state ps ls;
          post state' r :=
            r = length ls.(ls_disk) /\
            state' = state;
          alternate state' r :=
            exists ps',
              logical_abstraction
                state' ps'
                {| ls_committed := false;
                   ls_log := nil;
                   ls_disk := ls.(ls_disk) |};
       |}).
Proof.
  eapply mk_rspec; eauto; simpl in *; propositional;
    repeat match goal with
           | [ x: Recghost _ |- _ ] => destruct x
           end;
    eauto.
  - inv_clear H1.
    eexists (recghost _ _ _); simpl; intuition eauto.
  - simpl in H0; propositional.
    unfold logical_abstraction.
    descend; intuition eauto.
    rewrite <- pf; eassumption.

    Grab Existential Variables.
    simpl; auto.
Qed.

Definition abstraction (txnd: TxnD.State) (d: D.State) (u: unit) : Prop :=
  exists ps ls,
    logical_abstraction d ps ls /\
    txnd = (ls.(ls_disk), massign ls.(ls_log) ls.(ls_disk)).
