From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.secure_chat.full2 Require Import shared.
From Perennial.program_proof Require Import marshal_stateless_proof.

Section consts.
Definition max_senders := 2%nat.
End consts.

Section err.
Inductive fc_err := ErrSome.
Definition fc_errno (err:option fc_err) : u64 :=
  match err with
  | None => W64 0
  | Some ErrSome => W64 1
  end.
End err.

Module MsgT.
Record t :=
  mk {
    Body: u64;
  }.

Definition encodesF (a:t) : list u8 :=
  u64_le a.(Body).
Definition encodes (x:list u8) (a:t) : Prop :=
  x = encodesF a.

Section local_defs.
Context `{!heapGS Σ}.
Definition own (a:loc) (args:t) : iProp Σ :=
  "Hbody" ∷ a ↦[MsgT :: "Body"] #args.(Body).

Lemma wp_new body :
  {{{ True }}}
    NewMsgT #body
  {{{
    args_ptr, RET #args_ptr;
    "Hargs" ∷ own args_ptr (mk body)
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  rewrite /NewMsgT.
  wp_apply wp_allocStruct; [val_ty|].
  iIntros (p) "Hargs".
  rewrite /own.
  iDestruct (struct_fields_split with "Hargs") as "H".
  iNamed "H".
  by iApply "HΦ".
Qed.

Lemma wp_eq mp m op o :
  {{{
    "Hargs1" ∷ own mp m ∗
    "Hargs2" ∷ own op o
  }}}
  MsgT__Equals #mp #op
  {{{
    (eqb:bool), RET #eqb;
    "Hargs1" ∷ own mp m ∗
    "Hargs2" ∷ own op o ∗
    "%Heq" ∷ ⌜eqb ↔ m = o⌝
  }}}.
Proof. Admitted.

Lemma wp_copy op o :
  {{{
    "Hold" ∷ own op o
  }}}
  MsgT__Copy #op
  {{{
    np, RET #np;
    "Hold" ∷ own op o ∗
    "Hnew" ∷ own np o
  }}}.
Proof. Admitted.

Lemma wp_encode args_ptr args :
  {{{
    "Hargs" ∷ own args_ptr args
  }}}
    MsgT__Encode #args_ptr
  {{{
    sl enc_args, RET (slice_val sl);
    "Hargs" ∷ own args_ptr args ∗
    "%Henc" ∷ ⌜encodes enc_args args⌝ ∗
    "Hsl" ∷ own_slice_small sl byteT 1 enc_args
  }}}.
Proof.
  iIntros (Φ) "H HΦ".
  iNamed "H".
  rewrite /MsgT__Encode.
  wp_apply wp_NewSlice.
  iIntros (sl) "Hsl".
  wp_apply wp_ref_to; [val_ty|].
  iIntros (slp) "Hslp".
  wp_loadField.
  wp_load.
  wp_apply (wp_WriteInt with "[$]").
  iIntros (sl') "Hsl".
  wp_store.
  wp_load.
  iApply "HΦ".
  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
  by iFrame.
Qed.

Lemma wp_decode sl fullB fstB sndB args q :
  {{{
    "%Henc" ∷ ⌜encodes fstB args⌝ ∗
    "%Hsplit" ∷ ⌜fullB = fstB ++ sndB⌝ ∗
    "Hsl" ∷ own_slice_small sl byteT q fullB
  }}}
    DecodeMsgT (slice_val sl)
  {{{
    args_ptr sl_rem, RET (#args_ptr, (slice_val sl_rem));
    "Hargs" ∷ own args_ptr args ∗
    "Hsl" ∷ own_slice_small sl_rem byteT q sndB
  }}}.
Proof.
  iIntros (Φ) "H HΦ".
  iNamed "H".
  rewrite /DecodeMsgT {}Hsplit.
  rewrite /encodes /encodesF in Henc.
  rewrite {}Henc.
  wp_apply (wp_ReadInt with "[$]").
  iIntros (sl_rem) "Hsl_rem".
  wp_apply wp_new.
  iIntros (p) "H".
  iNamed "H".
  wp_pures.
  iApply "HΦ".
  by iFrame.
Qed.

End local_defs.
End MsgT.

Module MsgTSlice.
Notation t := (list MsgT.t).

Definition encodesF (a:t) : list u8 :=
  u64_le (length a) ++ list_bind _ _ MsgT.encodesF a.
Definition encodes (x:list u8) (a:t) : Prop :=
  x = encodesF a.

Section local_defs.
Context `{!heapGS Σ}.
Definition own a lloc lmsg : iProp Σ :=
  "Hsl" ∷ own_slice_small a ptrT 1 lloc ∗
  "Hsep" ∷ ([∗ list] x1;x2 ∈ lloc;lmsg,
    MsgT.own x1 x2).

Lemma wp_copy op o lmsg :
  {{{
    "Hold" ∷ own op o lmsg
  }}}
  CopyMsgTSlice (slice_val op)
  {{{
    np n, RET (slice_val np);
    "Hold" ∷ own op o lmsg ∗
    "Hnew_sl" ∷ own_slice np ptrT 1 n ∗
    "Hnew_sep" ∷ ([∗ list] x1;x2 ∈ n;lmsg, MsgT.own x1 x2)
  }}}.
Proof. Admitted.

Lemma wp_prefix short ll_short lm_short long ll_long lm_long :
  {{{
    "Hshort" ∷ own short ll_short lm_short ∗
    "Hlong" ∷ own long ll_long lm_long
  }}}
  IsMsgTSlicePrefix (slice_val short) (slice_val long)
  {{{
    (eqb:bool), RET #eqb;
    "Hshort" ∷ own short ll_short lm_short ∗
    "Hlong" ∷ own long ll_long lm_long ∗
    "%Heq" ∷ ⌜eqb ↔ lm_short `prefix_of` lm_long⌝
  }}}.
Proof. Admitted.

Lemma wp_encode args_ptr args lmsg :
  {{{
    "Hargs" ∷ own args_ptr args lmsg
  }}}
    EncodeMsgTSlice (slice_val args_ptr)
  {{{
    enc lenc, RET (slice_val enc);
    "Hargs" ∷ own args_ptr args lmsg ∗
    "%Henc" ∷ ⌜encodes lenc lmsg⌝ ∗
    "Henc" ∷ own_slice_small enc byteT 1 lenc
  }}}.
Proof. Admitted.

Lemma wp_decode sl fullB fstB sndB lmsg q :
  {{{
    "%Henc" ∷ ⌜encodes fstB lmsg⌝ ∗
    "%Hsplit" ∷ ⌜fullB = fstB ++ sndB⌝ ∗
    "Hsl" ∷ own_slice_small sl byteT q fullB
  }}}
    DecodeMsgTSlice (slice_val sl)
  {{{
    args_ptr sl_rem lloc, RET ((slice_val args_ptr), (slice_val sl_rem));
    "Hargs" ∷ own args_ptr lloc lmsg ∗
    "Hsl" ∷ own_slice_small sl_rem byteT q sndB
  }}}.
Proof. Admitted.

End local_defs.
End MsgTSlice.

Module PutArg.
Record t :=
  mk {
    Sender: u64;
    Sig: list u8;
    LogB: list u8;
  }.

Definition encodesF (a:t) : list u8 :=
  u64_le a.(Sender) ++ a.(Sig) ++ a.(LogB).
Definition encodes (x:list u8) (a:t) : Prop :=
  x = encodesF a.

Section local_defs.
Context `{!heapGS Σ}.
Definition own (a:loc) (args:t) : iProp Σ :=
  ∃ q1 q2 sig logB,
  "Hsender" ∷ a ↦[PutArg :: "Sender"] #args.(Sender) ∗
  "Hsig" ∷ a ↦[PutArg :: "Sig"] (slice_val sig) ∗
  "Hsig_sl" ∷ own_slice_small sig byteT q1 args.(Sig) ∗
  "HlogB" ∷ a ↦[PutArg :: "LogB"] (slice_val logB) ∗
  "HlogB_sl" ∷ own_slice_small logB byteT q2 args.(LogB).

Lemma wp_new sender sig lsig logB llogB q1 q2 :
  {{{
    "Hsig" ∷ own_slice_small sig byteT q1 lsig ∗
    "HlogB" ∷ own_slice_small logB byteT q2 llogB
  }}}
    NewPutArg #sender (slice_val sig) (slice_val logB)
  {{{
    args_ptr, RET #args_ptr;
    "Hargs" ∷ own args_ptr (mk sender lsig llogB)
  }}}.
Proof. Admitted.

Lemma wp_encode args_ptr args :
  {{{
    "Hargs" ∷ own args_ptr args
  }}}
    PutArg__Encode #args_ptr
  {{{
    enc lenc, RET (slice_val enc);
    "Hargs" ∷ own args_ptr args ∗
    "%Henc" ∷ ⌜encodes lenc args⌝ ∗
    "Henc" ∷ own_slice_small enc byteT 1 lenc
  }}}.
Proof. Admitted.

Lemma wp_decode sl fullB q :
  {{{
    "Hsl" ∷ own_slice_small sl byteT q fullB
  }}}
    DecodePutArg (slice_val sl)
  {{{
    args_ptr args err, RET (#args_ptr, #(fc_errno err));
    match err with
    | Some ErrSome => True
    | None =>
      "%Henc" ∷ ⌜encodes fullB args⌝ ∗
      "Hargs" ∷ own args_ptr args ∗
      "%Hinb" ∷ ⌜(uint.nat args.(Sender) < max_senders)%nat⌝
    end
  }}}.
Proof. Admitted.

End local_defs.
End PutArg.
