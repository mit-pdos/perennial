Require Import POCS.
Require Import Spec.HoareTactics.

Require Import Examples.Logging.Impl.

From Classes Require Import Classes.

Opaque plus.
Opaque lt.

Import EqualDecNotation.

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

(* TODO: Hint Rewrite length_descriptor breaks a proof here *)

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

Ltac match_abs :=
  match goal with
  | [ H: PhyDecode ?d _ |- PhyDecode ?d _ ] => exact H
  | [ H: PhyDecode ?d ?ps |- context[PhyDecode ?d _] ] =>
    match goal with
    | |- exists _, _ => solve [ destruct ps; descend; eauto ]
    end
  end.

Ltac simplify :=
  repeat match goal with
         | _ => match_abs
         | _ => progress propositional
         | |- _ /\ _ => split; [ solve [ auto ] | ]
         | |- _ /\ _ => split; [ | solve [ auto ] ]
         | _ => destruct_tuple
         | [ u: unit |- _ ] => destruct u
         | [ H: (_, _) = (_, _) |- _ ] => inv_clear H
         | _ => progress cbn [pre post alternate] in *
         end.

Ltac finish :=
  repeat match goal with
         | _ => match_abs
         | _ => solve [ eauto ]
         | _ => congruence
         | _ => omega
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
         | _ => match_abs
         | |- _ /\ _ => apply and_wlog
         | [ H: _ \/ _ |- _ ] => destruct H
         | _ => progress propositional
         | _ => solve [ auto ]
         end.

Ltac split_cases :=
  repeat match goal with
         | _ => match_abs
         | |- _ /\ _ => split
         | [ H: _ \/ _ |- _ ] => destruct H
         | _ => progress propositional
         | _ => solve [ eauto ]
         end.

(* specs for one-disk primitives (restatement of semantics as specs) *)
Ltac prim :=
  eapply proc_cspec_impl; [ unfold spec_impl | eapply op_spec_sound ];
  simpl in *;
  propositional;
  (intuition eauto);
  propositional.

Local Notation proc_cspec := (Hoare.proc_cspec D.ODLayer.(sem)).
Arguments Hoare.proc_cspec {Op State} sem {T}.

Theorem read_ok a :
  proc_cspec
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
  proc_cspec
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
  proc_cspec
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

Local Hint Resolve read_ok write_ok size_ok.

Ltac step :=
  step_proc; simplify; finish.

Opaque index.
Opaque D.ODLayer.

Theorem gethdr_ok ps :
  proc_cspec
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

Local Hint Resolve gethdr_ok.

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

Local Hint Resolve phy_writedesc.


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

Local Hint Resolve phy_writehdr.

Ltac spec_impl :=
  eapply proc_cspec_impl; [ unfold spec_impl | solve [ eauto] ];
  simplify.

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

Local Hint Resolve writehdr_ok.

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

Local Hint Resolve writedesc_ok.

Definition log_assign (log_values:LogValues) i b : LogValues :=
  {| values := assign log_values i b;
     values_ok := ltac:(autorewrite with length; auto); |}.

Local Hint Resolve addresses_length.

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

Local Hint Resolve phy_set_log_value.

Theorem getdesc_ok ps :
  proc_cspec
    (getdesc)
    (fun state =>
       {| pre := PhyDecode state ps;
          post state' r :=
            r = ps.(p_desc) /\
            state' = state;
          alternate state' _ :=
            state' = state; |}).
Proof.
  unfold getdesc.
  step.
  step.
  inv_clear H; simpl in *.
  replace (index state 1) in *; simpl in *; propositional.
  rewrite Descriptor_fmt.(encode_decode); auto.
Qed.

Local Hint Resolve getdesc_ok.

Theorem set_desc_ok ps desc i a v :
  proc_cspec
    (set_desc desc i a v)
    (fun state =>
       {| pre := PhyDecode state ps /\
                 ps.(p_desc) = desc /\
                 i < LOG_LENGTH;
          post state' r :=
            r = tt /\
            PhyDecode state' {| p_hdr := ps.(p_hdr);
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
  spec_impl; split_wlog; simplify; finish.
Qed.

Local Hint Resolve set_desc_ok.

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

Local Hint Resolve phy_log_size_ok.

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
  (* BUG: rewrite does not try to instantiate def using the typeclass without
  the (def:=_) *)
  rewrite (index_inbounds (def:=_)) in H1 by omega.
  simpl in *; propositional.
  auto using sel_log_value.
Qed.

Local Hint Resolve get_logwrite_ok.

Lemma phy_index_data:
  forall (ps : PhysicalState) (a : nat) (s : D.ODLayer.(State)),
    PhyDecode s ps ->
    forall v : block,
      index s (2 + LOG_LENGTH + a) ?|= eq v ->
      index ps.(p_data_region) a ?|= eq v.
Proof.
  intros ps a s H v H0.
  pose proof (PhyDecode_disk_len H).
  inv_clear H; simpl in *.

  destruct (index_dec data a);
    propositional;
    autorewrite with array in *;
    auto.

  rewrite (index_inbounds (def:=_)) in * by omega; simpl.
  simpl in *; propositional.
  apply sel_index_eq; auto.
Qed.

Local Hint Resolve phy_index_data.

Theorem data_read_ok ps a :
  proc_cspec
    (data_read a)
    (fun state =>
       {| pre := PhyDecode state ps;
          post state' r :=
            state' = state /\
            index ps.(p_data_region) a ?|= eq r;
          alternate state' _ :=
            state' = state; |}).
Proof.
  unfold data_read.
  spec_impl; finish.
Qed.

Local Hint Resolve data_read_ok.

Lemma phy_data_write:
  forall (ps : PhysicalState) (a : nat) (v : block) (s : D.ODLayer.(State)),
    PhyDecode s ps ->
    PhyDecode (assign s (2 + LOG_LENGTH + a) v)
              {|
                p_hdr := ps.(p_hdr);
                p_desc := ps.(p_desc);
                p_log_values := ps.(p_log_values);
                p_data_region := assign ps.(p_data_region) a v |}.
Proof.
  intros ps a v s H.
  pose proof (PhyDecode_disk_len H).
  inv_clear H; constructor; intros; simpl in *; array.
  destruct (a == i); subst; array.
  destruct (index_dec data i); propositional; array.
Qed.

Local Hint Resolve phy_data_write.

Theorem data_write_ok ps a v :
  proc_cspec
    (data_write a v)
    (fun state =>
       {| pre := PhyDecode state ps;
          post state r :=
            r = tt /\
            PhyDecode state {| p_hdr := ps.(p_hdr);
                           p_desc := ps.(p_desc);
                           p_log_values := ps.(p_log_values);
                           p_data_region :=
                             assign ps.(p_data_region) a v; |};
          alternate state' _ :=
            exists data,
              (data = ps.(p_data_region) \/
               data = assign ps.(p_data_region) a v) /\
              PhyDecode state' {| p_hdr := ps.(p_hdr);
                              p_desc := ps.(p_desc);
                              p_log_values := ps.(p_log_values);
                              p_data_region := data |};
       |}).
Proof.
  unfold data_write.
  spec_impl; split_wlog; simplify; finish.
Qed.

Local Hint Resolve data_write_ok.

Theorem log_write_ok ps a v :
  proc_cspec
    (log_write a v)
    (fun state =>
       {| pre := PhyDecode state ps;
          post state' r :=
            match r with
            | TxnD.WriteOK =>
              let hdr := ps.(p_hdr) in
              exists pf,
                PhyDecode state'
                          {| p_hdr := hdr_inc hdr pf;
                             p_desc :=
                               desc_assign ps.(p_desc) hdr.(log_length) a;
                             p_log_values :=
                               log_assign ps.(p_log_values) hdr.(log_length) v;
                             p_data_region := ps.(p_data_region); |}
            | TxnD.WriteErr =>
              state' = state /\
              ps.(p_hdr).(log_length) = LOG_LENGTH
            end;
          alternate state' _ :=
            (* if we crash the log will still be uncommited, so just promise
            that the data is unaffected *)
            exists hdr desc log_values,
              PhyDecode state' {| p_hdr := hdr;
                              p_desc := desc;
                              p_log_values := log_values;
                              p_data_region := ps.(p_data_region) |} /\
              hdr.(committed) = ps.(p_hdr).(committed);
       |}).
Proof.
  unfold log_write.
  step; split_wlog; simplify; finish.
  destruct (hdr_full r).
  step; simplify; finish.
  destruct ps; eauto.
  step; split_wlog; simplify; finish.
  step; split_wlog; simplify; finish.
  step; split_wlog; simplify; finish.
  step; split_wlog; simplify; finish.
Qed.

(* this is just a physical description of [apply_at]; it precisely encodes the
data since we can't accurately abstract it that this level (we need to refer to
the old disk, which isn't tracked in these specs) *)
Theorem apply_at_ok ps desc i :
  proc_cspec
    (apply_at desc i)
    (fun state =>
       {| pre := PhyDecode state ps /\
                 desc = ps.(p_desc) /\
                 i < LOG_LENGTH;
          post state' r :=
            r = tt /\
            PhyDecode state' {| p_hdr := ps.(p_hdr);
                            p_desc := ps.(p_desc);
                            p_log_values := ps.(p_log_values);
                            p_data_region :=
                              let a := sel ps.(p_desc) i in
                              let v := sel ps.(p_log_values) i in
                              assign ps.(p_data_region) a v; |};
          alternate state' _ :=
            exists data,
              (data = ps.(p_data_region) \/
               let a := sel ps.(p_desc) i in
               let v := sel ps.(p_log_values) i in
               data = assign ps.(p_data_region) a v) /\
            PhyDecode state' {| p_hdr := ps.(p_hdr);
                            p_desc := ps.(p_desc);
                            p_log_values := ps.(p_log_values);
                            p_data_region := data; |};
       |}).
Proof.
  unfold apply_at.
  step; split_wlog; simplify; finish.
  step; split_wlog; simplify; finish.
  step; split_wlog; simplify; finish.
Qed.

Lemma log_subslice_len_ok:
  forall state : D.ODLayer.(State),
    ~ length state < 2 + LOG_LENGTH -> length (subslice state 2 LOG_LENGTH) = LOG_LENGTH.
Proof.
  intros.
  rewrite length_subslice; omega.
Qed.

Theorem phy_log_init_ok :
  proc_cspec
    (log_init)
    (fun state =>
       {| pre := True;
          post state' r :=
            match r with
            | Initialized =>
              exists ps, PhyDecode state' ps /\
                    ps.(p_hdr).(committed) = false /\
                    ps.(p_hdr).(log_length) = 0
            | InitFailed => state' = state
            end;
          alternate state' _ := True |}).
Proof.
  unfold log_init.
  step.
  destruct matches.
  step.
  unfold writehdr, writedesc.
  repeat step.
  exists {| p_hdr := empty_hdr;
       p_desc := default;
       p_log_values := {| values := subslice state 2 LOG_LENGTH;
                          values_ok := ltac:(auto using log_subslice_len_ok) |};
       p_data_region := subslice state (2+LOG_LENGTH) (length state - 2 - LOG_LENGTH); |};
    simpl.
  intuition eauto.
  constructor; intros; simpl; array.
  destruct (index_dec state (2 + LOG_LENGTH + i)); propositional; array.
Qed.
