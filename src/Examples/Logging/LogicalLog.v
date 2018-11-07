Require Import POCS.
Require Import Spec.HoareTactics.

Require Import Examples.Logging.Impl.
Require Import Examples.Logging.LogLayout.

Import EqualDecNotation.

Record LogicalState :=
  { ls_committed : bool;
    ls_log : list (addr * block);
    ls_disk : disk; }.

Inductive LogDecode : PhysicalState -> LogicalState -> Prop :=
| log_decode hdr (desc: Descriptor) (log_values: LogValues) log
             commit data_region data :
    forall (Hloglen: length log = hdr.(log_length))
      (Hlogcontents:
         forall i, i < hdr.(log_length) ->
              index log i = Some (sel desc i, sel log_values i))
      (Hcommitted: hdr.(committed) = commit)
      (Hdisk: data_region = data),
      LogDecode {| p_hdr := hdr;
                   p_desc := desc;
                   p_log_values := log_values;
                   p_data_region := data_region; |}
                {| ls_committed := commit;
                   ls_log := log;
                   ls_disk := data; |}.

Local Notation proc_cspec := (Hoare.proc_cspec D.ODLayer.(sem)).

Local Hint Resolve data_read_ok.

Ltac match_abs ::=
  match goal with
  | [ H: PhyDecode ?d _ |- PhyDecode ?d _ ] => exact H
  | [ H: PhyDecode ?d ?ps |- context[PhyDecode ?d _] ] =>
    match goal with
    | |- exists _, _ => solve [ destruct ps; descend; eauto ]
    end
  | [ H: LogDecode ?d _ |- LogDecode ?d _ ] => exact H
  | [ H: PhyDecode ?d ?ps |- exists ps, PhyDecode ?d ps /\ _ ] =>
    exists ps; split; [ exact H | ]
  | [ H: LogDecode ?d ?ps |- context[LogDecode ?d _] ] =>
    match goal with
    | |- exists _, _ => solve [ destruct ps; descend; eauto ]
    end
  end.

Lemma logd_disk ps ls :
  LogDecode ps ls ->
  ps.(p_data_region) = ls.(ls_disk).
Proof.
  inversion 1; auto.
Qed.

Hint Resolve logd_disk.

Lemma logd_loglen ps ls :
  LogDecode ps ls ->
  ps.(p_hdr).(log_length) = length ls.(ls_log).
Proof.
  inversion 1; auto.
Qed.

Lemma logd_committed ps ls :
  LogDecode ps ls ->
  ps.(p_hdr).(committed) = ls.(ls_committed).
Proof.
  inversion 1; auto.
Qed.

Hint Resolve logd_committed.

Lemma logd_log_contents ps ls :
  LogDecode ps ls ->
  forall i, i < ps.(p_hdr).(log_length) ->
       index ls.(ls_log) i =
       Some (sel ps.(p_desc) i, sel ps.(p_log_values) i).
Proof.
  inversion 1; auto.
Qed.

Lemma logd_log_bounds ps ls :
  LogDecode ps ls ->
  length ls.(ls_log) <= LOG_LENGTH.
Proof.
  inversion 1; simpl.
  pose proof hdr.(log_length_ok).
  congruence.
Qed.

Theorem log_read_ok ps ls a :
  proc_cspec
    (log_read a)
    (fun state =>
       {| pre := PhyDecode state ps /\
                 LogDecode ps ls;
          post state' r :=
            state' = state /\
            index ls.(ls_disk) a ?|= eq r;
          alternate state' _ :=
            state' = state; |}).
Proof.
  unfold log_read.
  spec_impl; split_cases; simplify; finish.
  rewrite (logd_disk ltac:(eassumption)) in *; auto.
Qed.

Local Hint Resolve log_write_ok.

Lemma length_descriptor (desc:Descriptor) :
  length desc = LOG_LENGTH.
Proof.
  destruct desc; auto.
Qed.

Hint Rewrite length_descriptor : length.

Lemma log_decode_app:
  forall (ps : PhysicalState) (ls : LogicalState)
    (a : addr) (v : block) (s : D.ODLayer.(State)),
    PhyDecode s ps ->
    LogDecode ps ls ->
    forall pf : ps.(p_hdr).(log_length) < LOG_LENGTH,
      LogDecode
        {|
          p_hdr := hdr_inc ps.(p_hdr) pf;
          p_desc := desc_assign ps.(p_desc) ps.(p_hdr).(log_length) a;
          p_log_values := log_assign ps.(p_log_values) ps.(p_hdr).(log_length) v;
          p_data_region := ps.(p_data_region) |}
        {| ls_committed := ls.(ls_committed);
           ls_log := ls.(ls_log) ++ (a, v) :: nil;
           ls_disk := ls.(ls_disk) |}.
Proof.
  intros ps ls a v s Hphy Hlog pf.
  pose proof (logd_log_bounds Hlog).
  constructor; simpl; eauto.
  - rewrite app_length; simpl.
    rewrite (logd_loglen ltac:(eassumption)); auto.
  - intros.
    pose proof (logd_log_contents Hlog (i:=i)).
    rewrite (logd_loglen ltac:(eassumption)) in *.
    destruct (i == length ls.(ls_log)); subst; array.
    + rewrite Nat.sub_diag; simpl; auto.
    + apply H1; omega.
Qed.

Hint Resolve log_decode_app.

Fixpoint zip A B (l1: list A) (l2: list B) : list (A*B) :=
  match l1, l2 with
  | x::xs, y::ys => (x, y) :: zip xs ys
  | _, _ => nil
  end.

Theorem zip_index A B {defA: Default A} {defB: Default B} (l1: list A) (l2: list B) :
  forall i, i < length l1 ->
       i < length l2 ->
       index (zip l1 l2) i = Some (sel l1 i, sel l2 i).
Proof.
  generalize dependent l2.
  induction l1; simpl; intros.
  omega.
  destruct l2; simpl in *; try omega.
  destruct i; simpl.
  reflexivity.
  rewrite IHl1 by omega.
  reflexivity.
Qed.

Theorem zip_length1 A B (l1: list A) (l2: list B) :
  length l1 <= length l2 ->
  length (zip l1 l2) = length l1.
Proof.
  generalize dependent l2.
  induction l1; simpl; intros; auto.
  destruct l2; simpl in *; try omega.
  rewrite IHl1 by omega; auto.
Qed.

Lemma log_decode_some_log:
  forall (ps : PhysicalState) (ls : LogicalState) (s : D.ODLayer.(State)),
    PhyDecode s ps ->
    LogDecode ps ls ->
    forall (hdr : LogHdr) (desc : Descriptor) (log_values : LogValues),
      hdr.(committed) = ps.(p_hdr).(committed) ->
      exists log : list (addr * block),
        LogDecode
          {|
            p_hdr := hdr;
            p_desc := desc;
            p_log_values := log_values;
            p_data_region := ps.(p_data_region) |}
          {|
            ls_committed := ls.(ls_committed);
            ls_log := log;
            ls_disk := ls.(ls_disk) |}.
Proof.
  intros ps ls s Hphy Hlog hdr desc log_values Hcommit.
  exists (firstn hdr.(log_length) (zip desc log_values)).
  constructor; eauto.
  - rewrite firstn_length.
    rewrite zip_length1; autorewrite with length; auto.
    rewrite Nat.min_l; auto.
    apply hdr.(log_length_ok).
  - intros.
    rewrite index_firstn by auto.
    pose proof hdr.(log_length_ok).
    erewrite zip_index; eauto; autorewrite with length; try omega.
Qed.

Hint Resolve log_decode_some_log.

Theorem log_write_ok ps ls a v :
  proc_cspec
    (log_write a v)
    (fun state =>
       {| pre := PhyDecode state ps /\
                 LogDecode ps ls;
          post state' r :=
            match r with
            | TxnD.WriteOK =>
              exists ps', PhyDecode state' ps' /\
                     LogDecode ps'
                               {| ls_committed := ls.(ls_committed);
                                  ls_log := ls.(ls_log) ++ (a,v)::nil;
                                  ls_disk := ls.(ls_disk); |}
            | TxnD.WriteErr =>
              exists ps', PhyDecode state' ps' /\
                     LogDecode ps' ls
            end;
          alternate state' _ :=
            exists ps',
              PhyDecode state' ps' /\
              exists log,
                (LogDecode ps' {| ls_committed := ls.(ls_committed);
                                  ls_log := log;
                                  ls_disk := ls.(ls_disk); |});
       |}).
Proof.
  spec_impl; split_cases; simplify; finish.
  destruct v0; simplify; finish.
Qed.

(* log contains data region addresses, and this applies them to a data region
logical disk *)
Fixpoint logical_log_apply (l: list (addr * block)) (data: disk)  : disk :=
  match l with
  | nil => data
  | (a, b) :: l' => logical_log_apply l' (assign data (2+LOG_LENGTH+a) b)
  end.
