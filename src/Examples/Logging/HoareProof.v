Require Import POCS.

Require Import Examples.Logging.Impl.

Require Import Spec.HoareTactics.

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

Record PhysicalState :=
  { p_hdr: LogHdr;
    p_desc: Descriptor;
    p_log_values: list block;
    p_log_values_len: length p_log_values = LOG_LENGTH;
    p_data_region: disk; }.

Inductive PhyDecode (d: disk) : PhysicalState -> Prop :=
| phy_decode hdr desc log_values pf data
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
                   p_log_values_len := pf;
                   p_data_region := data; |}
.

Lemma length_bound A (d: list A) i :
  index d i = None ->
  length d <= i.
Proof.
  intros.
  destruct (lt_dec i (length d)); try omega.
  exfalso; apply index_not_none in H; auto.
Qed.

Theorem PhyDecode_data_len d ps :
  PhyDecode d ps ->
  length ps.(p_data_region) = length d - 2 - LOG_LENGTH.
Proof.
  inversion 1; subst; simpl.
  apply Nat.le_antisymm.
  - apply length_bound.
    rewrite <- Hdata.
    rewrite index_oob by omega; auto.
  - assert (length d <= 2 + LOG_LENGTH + length data); try omega.
    apply length_bound.
    rewrite Hdata; auto.
    rewrite index_oob by omega; auto.
Qed.

Lemma index_inbounds_exists (d: disk) i :
  i < length d ->
  exists b, index d i = Some b.
Proof.
  intros.
  destruct_with_eqn (index d i); eauto.
  exfalso; apply index_not_none in Heqo; auto.
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
         end.

Ltac finish :=
  repeat match goal with
         | _ => auto
         | _ => congruence
         end.

(* specs for one-disk primitives (restatement of semantics as specs) *)
Ltac prim :=
  eapply proc_cspec_impl; [ unfold spec_impl | eapply op_spec_sound ];
    simpl;
    propositional;
    (intuition auto);
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
  inversion H; subst; cbn [p_hdr] in *.
  replace (index state 0) in *; cbn [maybe_holds] in *; subst.
  rewrite LogHdr_fmt.(encode_decode); auto.
Qed.

Theorem writedesc ps desc :
  proc_cspec D.ODLayer
             (writedesc desc)
             (fun state =>
                {| pre := PhyDecode state ps;
                   post state' r :=
                     PhyDecode state' {| p_hdr := ps.(p_hdr);
                                     p_desc := desc;
                                     p_log_values := ps.(p_log_values);
                                     p_log_values_len := ps.(p_log_values_len);
                                     p_data_region := ps.(p_data_region); |};
                   alternate state' _ :=
                     PhyDecode state' ps \/
                     PhyDecode state' {| p_hdr := ps.(p_hdr);
                                     p_desc := desc;
                                     p_log_values := ps.(p_log_values);
                                     p_log_values_len := ps.(p_log_values_len);
                                     p_data_region := ps.(p_data_region); |}
                |}).
Proof.
  unfold writedesc.
  eapply proc_cspec_impl; [ unfold spec_impl | solve [eauto] ];
    simpl;
    propositional;
    (intuition auto);
    propositional.
  assert (length s >= 2 + LOG_LENGTH) by admit.
  - admit.
  - admit.
  - admit.
Abort.
