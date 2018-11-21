From RecoveryRefinement Require Import Lib.

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
  lia.
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
  specialize (Hlog_values (LOG_LENGTH-1) ltac:(lia)).
  rewrite (index_inbounds log_values (LOG_LENGTH-1)) in Hlog_values;
    autorewrite with length;
    try lia.
  apply index_some_bound in Hlog_values.
  lia.
Qed.

Theorem PhyDecode_data_len d ps :
  PhyDecode d ps ->
  length ps.(p_data_region) = length d - 2 - LOG_LENGTH.
Proof.
  inversion 1; subst; simpl.
  apply length_bounds.
  - apply index_none_bound.
    rewrite <- Hdata; array.
  - assert (length d <= 2 + LOG_LENGTH + length data); try lia.
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
  lia.
Qed.

Ltac match_abs :=
  match goal with
  | [ H: PhyDecode ?d _ |- PhyDecode ?d _ ] => exact H
  | [ H: PhyDecode ?d ?ps |- context[PhyDecode ?d _] ] =>
    match goal with
    | |- exists _, _ => solve [ destruct ps; descend; eauto ]
    end
  end.
