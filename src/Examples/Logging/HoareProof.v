Require Import POCS.
Require Import Spec.HoareTactics.

Require Import Examples.Logging.Impl.

From SimpleClasses Require Import Classes.

Opaque plus.
Opaque lt.

Import EqualDecNotation.

Record LogicalState :=
  { ls_disk : disk;
    ls_log : list (addr * block);
  }.

Inductive DiskDecode (d: disk) (ls: LogicalState) : Prop :=
| disk_decode
    (Hsize: 2 + LOG_LENGTH + length ls.(ls_disk) = length d)
    (Hdisk: forall i, i <= length ls.(ls_disk) -> index ls.(ls_disk) i = index d (i + 258)).

Inductive LogDecode (d: disk) (ls: LogicalState) : Prop :=
| log_decode bhdr bdesc hdr desc 
    (Hbhdr: index d O = Some bhdr)
    (Hbdesc: index d 1 = Some bdesc)
    (Hhdr_dec : LogHdr_fmt.(decode) bhdr = hdr)
    (Hdesc_dec : Descriptor_fmt.(decode) bdesc = desc)
    (Hlog_length: length ls.(ls_log) <= LOG_LENGTH)
    (Hlog: forall i, i < hdr.(log_length) ->
                     exists a b,
                       index ls.(ls_log) i = Some (a, b) /\
                       index desc.(addresses) i = Some a /\
                       index d (2 + i) = Some b):
    LogDecode d ls.

Record LogValues :=
  { values :> list block;
    values_ok: length values = LOG_LENGTH }.

Coercion addresses : Descriptor >-> list.

Record PhysicalState :=
  { p_hdr: LogHdr;
    p_desc: Descriptor;
    p_log_values: LogValues;
    p_data_region: disk; }.

Inductive PhyDecode (d: disk) : PhysicalState -> Prop :=
| phy_decode hdr desc (log_values:LogValues) data
             (Hhdr: index d 0 = Some (LogHdr_fmt.(encode) hdr))
             (Hdesc: index d 1 = Some (Descriptor_fmt.(encode) desc))
             (Hlog_values: forall i,
                 i < LOG_LENGTH ->
                 index d (2+i) = index log_values i)
             (Hdata: forall i,
                 index d (2+LOG_LENGTH+i) = index data i) :
    PhyDecode d {| p_hdr := hdr;
                   p_desc := desc;
                   p_log_values := log_values;
                   p_data_region := data; |}
.

Lemma log_length_nonzero : LOG_LENGTH > 0.
  unfold LOG_LENGTH.
  omega.
Qed.

(* coercion magic makes this theorem seem odd - the proof comes from inside
log_values *)
Lemma length_log (log_values:LogValues) :
  length log_values = LOG_LENGTH.
Proof.
  destruct log_values; auto.
Qed.

Hint Rewrite length_log : length.

Theorem PhyDecode_disk_bound d ps :
  PhyDecode d ps ->
  length d >= 2 + LOG_LENGTH.
Proof.
  pose proof log_length_nonzero.
  inversion 1; subst.
  specialize (Hlog_values (LOG_LENGTH-1) ltac:(omega)).
  rewrite (index_inbounds log_values (LOG_LENGTH-1)) in Hlog_values;
    autorewrite with length;
    try omega.
  apply index_some_bound in Hlog_values.
  omega.
Qed.

Theorem PhyDecode_data_len d ps :
  PhyDecode d ps ->
  length ps.(p_data_region) = length d - 2 - LOG_LENGTH.
Proof.
  inversion 1; subst; simpl.
  apply length_bounds.
  - apply index_none_bound.
    rewrite <- Hdata; array.
  - assert (length d <= 2 + LOG_LENGTH + length data); try omega.
    apply index_none_bound.
    rewrite Hdata; array.
Qed.

Theorem PhyDecode_disk_len d ps :
  PhyDecode d ps ->
  length d = 2 + LOG_LENGTH + length ps.(p_data_region).
Proof.
  intros.
  pose proof (PhyDecode_disk_bound H).
  pose proof (PhyDecode_data_len H).
  omega.
Qed.

Inductive CommitStatus d b : Prop :=
| commit_status bhdr 
    (Hbhdr: index d O = Some bhdr)
    (Hstatus : (LogHdr_fmt.(decode) bhdr).(committed) = b):
    CommitStatus d b.

Fixpoint logical_log_apply (l: list (addr * block)) (d: disk)  : disk :=
  match l with
  | nil => d
  | (a, b) :: l' => logical_log_apply l' (assign d (2+LOG_LENGTH+a) b)
  end.

Definition ls_snoc ls a v : LogicalState :=
  {| ls_disk := ls_disk ls;
     ls_log := ls_log ls ++ ((a, v) :: nil) |}.

Definition ls_clear ls : LogicalState :=
  {| ls_disk := ls_disk ls;
     ls_log := nil |}.

Definition log_write_cspec ls (a: addr) (v: block) : Specification TxnD.WriteStatus unit D.State :=
  fun state =>
    {|
      pre := LogDecode state ls /\ DiskDecode state ls /\ CommitStatus state false;
      post := fun state' status =>
                match status with
                | TxnD.WriteErr => state' = state
                | TxnD.WriteOK =>
                  LogDecode state' (ls_snoc ls a v)
                  /\ DiskDecode state' (ls_snoc ls a v)
                  /\ CommitStatus state' false
                end;
      alternate := fun state' _ => DiskDecode state' ls /\ CommitStatus state' false
    |}.
                  
Definition log_size_cspec ls : Specification nat unit D.State :=
  fun state =>
    {|
      pre := LogDecode state ls /\ DiskDecode state ls /\ CommitStatus state false;
      post := fun state' sz => state = state' /\ sz = length ls.(ls_disk);
      alternate := fun state' _ => state = state'
    |}.
    
Definition log_read_cspec ls (a: addr) : Specification block unit D.State :=
  fun state =>
    {|
      pre := LogDecode state ls /\ DiskDecode state ls /\ CommitStatus state false;
      post := fun state' v => state = state' /\
                              match index ls.(ls_disk) a with
                              | Some v' => v = v'
                              | None => True
                              end;
      alternate := fun state' _ => state = state'
    |}.

Definition log_recover_spec ls : Specification block unit D.State :=
  fun state =>
    {|
      pre := LogDecode state ls /\ DiskDecode state ls /\ CommitStatus state false;
      post := fun state' v => LogDecode state' (ls_clear ls) /\
                       DiskDecode state' (ls_clear ls) /\
                       CommitStatus state' false;
      alternate := fun state' _ => state = state'
    |}.

Ltac simplify :=
  repeat match goal with
         | _ => progress propositional
         | |- _ /\ _ => split; [ solve [ auto ] | ]
         | |- _ /\ _ => split; [ | solve [ auto ] ]
         | _ => progress cbn [pre post alternate] in *
         end.

Ltac finish :=
  repeat match goal with
         | _ => eauto
         | _ => congruence
         end.

Lemma and_wlog (P Q:Prop) :
  P ->
  (P -> Q) ->
  P /\ Q.
Proof.
  firstorder.
Qed.

Ltac split_wlog :=
  repeat match goal with
         | |- _ /\ _ => apply and_wlog
         | [ H: _ \/ _ |- _ ] => destruct H
         | _ => progress propositional
         | _ => solve [ auto ]
         end.

Ltac split_cases :=
  repeat match goal with
         | |- _ /\ _ => split
         | [ H: _ \/ _ |- _ ] => destruct H
         | _ => progress propositional
         | _ => solve [ auto ]
         end.

(* specs for one-disk primitives (restatement of semantics as specs) *)
Ltac prim :=
  eapply proc_cspec_impl; [ unfold spec_impl | eapply op_spec_sound ];
  simpl in *;
  propositional;
  (intuition eauto);
  propositional.

Theorem read_ok a :
  proc_cspec D.ODLayer
             (read a)
             (fun state =>
                {| pre := True;
                   post state' r :=
                     index state a ?|= eq r /\
                     state' = state;
                   alternate state' _ :=
                     state' = state; |}).
Proof.
  unfold read.
  prim;
    repeat match goal with
           | [ H: D.op_step _ _ _ _ |- _ ] => invert H; clear H
           end;
    propositional;
    auto.
  destruct (index s' a); simpl; eauto.
Qed.

Theorem write_ok a v :
  proc_cspec D.ODLayer
             (write a v)
             (fun state =>
                {| pre := True;
                   post state' r :=
                     r = tt /\
                     state' = assign state a v;
                   alternate state' _ :=
                     state' = state \/
                     state' = assign state a v; |}).
Proof.
  unfold write.
  prim;
    repeat match goal with
           | [ H: D.op_step _ _ _ _ |- _ ] => invert H; clear H
           end;
    propositional;
    auto.
Qed.

Theorem size_ok :
  proc_cspec D.ODLayer
             (size)
             (fun state =>
                {| pre := True;
                   post state' r :=
                     r = length state /\
                     state' = state;
                   alternate state' _ :=
                     state' = state; |}).
Proof.
  unfold size.
  prim;
    repeat match goal with
           | [ H: D.op_step _ _ _ _ |- _ ] => invert H; clear H
           end;
    propositional;
    auto.
Qed.

Hint Resolve read_ok write_ok size_ok.

Ltac step :=
  unshelve step_proc; simplify; finish.

Opaque index.

Theorem gethdr ps :
  proc_cspec D.ODLayer
             gethdr
             (fun state =>
                {| pre := PhyDecode state ps;
                   post state' r :=
                     r = ps.(p_hdr) /\
                     state' = state;
                   alternate state' _ :=
                     state' = state; |}).
Proof.
  unfold gethdr.
  step.
  step.
  inversion H; subst; simpl in *.
  replace (index state 0) in *; simpl in *; subst.
  rewrite LogHdr_fmt.(encode_decode); auto.
Qed.

Lemma phy_writedesc:
  forall (ps : PhysicalState) (desc : Descriptor) (s : D.State),
    PhyDecode s ps ->
    PhyDecode (assign s 1 (Descriptor_fmt.(encode) desc))
              {|
                p_hdr := ps.(p_hdr);
                p_desc := desc;
                p_log_values := ps.(p_log_values);
                p_data_region := ps.(p_data_region) |}.
Proof.
  intros ps desc s H.
  pose proof (PhyDecode_disk_len H).
  inv_clear H; constructor; intros; array.
Qed.

Hint Resolve phy_writedesc.


Lemma phy_writehdr:
  forall (ps : PhysicalState) (hdr : LogHdr) (s : D.ODLayer.(State)),
    PhyDecode s ps ->
    PhyDecode (assign s 0 (LogHdr_fmt.(encode) hdr))
              {| p_hdr := hdr;
                 p_desc := ps.(p_desc);
                 p_log_values := ps.(p_log_values);
                 p_data_region := ps.(p_data_region) |}.
Proof.
  intros ps hdr s H.
  pose proof (PhyDecode_disk_len H).
  inv_clear H; constructor; intros; array.
Qed.

Hint Resolve phy_writehdr.

Ltac spec_impl :=
  eapply proc_cspec_impl; [ unfold spec_impl | solve [ eauto] ];
  simplify.

Notation proc_cspec := (Hoare.proc_cspec D.ODLayer.(sem)).
Arguments Hoare.proc_cspec {Op State} sem {T}.

Theorem writehdr_ok ps hdr :
  proc_cspec
    (writehdr hdr)
    (fun state =>
       {| pre := PhyDecode state ps;
          post state' r :=
            PhyDecode state' {| p_hdr := hdr;
                            p_desc := ps.(p_desc);
                            p_log_values := ps.(p_log_values);
                            p_data_region := ps.(p_data_region); |};
          alternate state' _ :=
            PhyDecode state' ps \/
            PhyDecode state' {| p_hdr := hdr;
                            p_desc := ps.(p_desc);
                            p_log_values := ps.(p_log_values);
                            p_data_region := ps.(p_data_region); |}
       |}).
Proof.
  unfold writehdr.
  spec_impl; split_wlog.
Qed.

Hint Resolve writehdr_ok.

Theorem writedesc_ok ps desc :
  proc_cspec
    (writedesc desc)
    (fun state =>
       {| pre := PhyDecode state ps;
          post state' r :=
            r = tt /\
            PhyDecode state' {| p_hdr := ps.(p_hdr);
                            p_desc := desc;
                            p_log_values := ps.(p_log_values);
                            p_data_region := ps.(p_data_region); |};
          alternate state' _ :=
            PhyDecode state' ps \/
            PhyDecode state' {| p_hdr := ps.(p_hdr);
                            p_desc := desc;
                            p_log_values := ps.(p_log_values);
                            p_data_region := ps.(p_data_region); |}
       |}).
Proof.
  unfold writedesc.
  spec_impl; split_wlog.
Qed.

Hint Resolve writedesc_ok.

Definition log_assign (log_values:LogValues) i b : LogValues :=
  {| values := assign log_values i b;
     values_ok := ltac:(autorewrite with length; auto); |}.

Hint Resolve addresses_length.

Definition desc_assign (desc:Descriptor) i a : Descriptor :=
  {| addresses := assign desc i a;
     addresses_length := ltac:(autorewrite with length; auto); |}.

Lemma phy_set_log_value:
  forall (ps : PhysicalState) (i : nat) (a : addr) (v : block),
    i < LOG_LENGTH ->
    forall s : D.State,
      PhyDecode s
                {|
                  p_hdr := ps.(p_hdr);
                  p_desc := add_addr ps.(p_desc) i a;
                  p_log_values := ps.(p_log_values);
                  p_data_region := ps.(p_data_region) |} ->
      PhyDecode (assign s (2 + i) v)
                {|
                  p_hdr := ps.(p_hdr);
                  p_desc := desc_assign ps.(p_desc) i a;
                  p_log_values := log_assign ps.(p_log_values) i v;
                  p_data_region := ps.(p_data_region) |}.
Proof.
  intros ps i a v Hbound s H.
  pose proof (PhyDecode_disk_len H); simpl in *.
  inv_clear H; constructor; intros;
    cbn [log_assign values]; array.
  destruct (i == i0); subst; array.
Qed.

Hint Resolve phy_set_log_value.

Theorem set_desc_ok ps desc i a v :
  proc_cspec
    (set_desc desc i a v)
    (fun state =>
       {| pre := PhyDecode state ps /\
                 ps.(p_desc) = desc /\
                 i < LOG_LENGTH;
          post state r :=
            r = tt /\
            PhyDecode state {| p_hdr := ps.(p_hdr);
                           p_desc := desc_assign desc i a;
                           p_log_values :=
                             log_assign ps.(p_log_values) i v;
                           p_data_region := ps.(p_data_region) |};
          alternate state' _ :=
            exists desc' log_values',
              PhyDecode state' {| p_hdr := ps.(p_hdr);
                              p_desc := desc';
                              p_log_values := log_values';
                              p_data_region := ps.(p_data_region); |};
       |}).
Proof.
  unfold set_desc.
  step; split_cases; simplify; finish.
  - spec_impl; split_wlog; simplify; finish.
  - destruct ps; eauto.
Qed.

Theorem phy_log_size_ok ps :
  proc_cspec
    (log_size)
    (fun state =>
       {| pre := PhyDecode state ps;
          post state' r :=
            state' = state /\
            r = length ps.(p_data_region);
          alternate state' _ :=
            state' = state; |}).
Proof.
  unfold log_size.
  step.
  step.
  pose proof (PhyDecode_data_len H).
  omega.
Qed.

Hint Resolve phy_log_size_ok.

Lemma sel_log_value d ps i :
  PhyDecode d ps ->
  i < LOG_LENGTH ->
  sel d (2 + i) = sel ps.(p_log_values) i.
Proof.
  intros; inv_clear H; simpl.
  apply sel_index_eq.
  eauto.
Qed.

Theorem get_logwrite_ok ps desc i :
  proc_cspec
    (get_logwrite desc i)
    (fun state =>
       {| pre := PhyDecode state ps /\
                 i < LOG_LENGTH /\
                 ps.(p_desc) = desc;
          post state' r :=
            state' = state /\
            r = (sel ps.(p_desc) i, sel ps.(p_log_values) i);
          alternate state' _ :=
            state' = state; |}).
Proof.
  unfold get_logwrite.
  step.
  step.
  pose proof (PhyDecode_disk_len H).
  f_equal.
  (* BUG: rewrite does not try to instantiate def using the typeclass *)
  rewrite (@index_inbounds block _) in H1 by omega.
  simpl in *; propositional.
  auto using sel_log_value.
Qed.
