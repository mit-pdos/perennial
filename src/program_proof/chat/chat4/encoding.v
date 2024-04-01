From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.secure_chat Require Import chat4.

Module msgT.
Record t :=
  mk {
    tag: u64;
    body: u64;
    pin: u64
  }.

Definition encodeF (l_t: t) : list u8 :=
  u64_le l_t.(tag) ++ u64_le l_t.(body) ++ u64_le l_t.(pin).

Lemma encode_inj t1 t2:
  encodeF t1 = encodeF t2 → t1 = t2.
Proof. Admitted.

Section local_defs.
Context `{!heapGS Σ}.
Definition own (p_ptr : loc) (l_t : t) : iProp Σ :=
  "HTag" ∷ p_ptr ↦[msgT :: "tag"] #l_t.(tag) ∗
  "HBody" ∷ p_ptr ↦[msgT :: "body"] #l_t.(body) ∗
  "BPin" ∷ p_ptr ↦[msgT :: "pin"] #l_t.(pin).

Lemma wp_encode (args_ptr : loc) (l_args : t):
  {{{
    own args_ptr l_args
  }}}
    encodeMsgT #args_ptr
  {{{
    (p_sl : Slice.t) l_bytes, RET (slice_val p_sl);
    own args_ptr l_args ∗
    own_slice p_sl byteT 1 l_bytes ∗
    ⌜l_bytes = encodeF l_args⌝
  }}}.
Proof. Admitted.

Lemma wp_decode p_sl (l_bytes : list u8):
  {{{
    "Hsl" ∷ own_slice_small p_sl byteT 1 l_bytes ∗
    (* 24 is byte len of msgT. *)
    "Hlen" ∷ ⌜length l_bytes = 24%nat⌝
  }}}
    decodeMsgT (slice_val p_sl)
  {{{
    (args_ptr : loc) l_args (garb : val), RET (#args_ptr, garb);
    own args_ptr l_args
  }}}.
Proof. Admitted.

End local_defs.
End msgT.

Module msgWrapT.
Record t :=
  mk {
    msg: msgT.t;
    sig: list u8;
    sn: u64
  }.

Definition encodeF (l_t : t) : (list u8) :=
  msgT.encodeF l_t.(msg) ++ l_t.(sig) ++ u64_le l_t.(sn).

Section local_defs.
Context `{!heapGS Σ}.
Definition own (p_ptr : loc) (l_t : t) : iProp Σ :=
  ∃ (p_mt_ptr : loc) (p_sig : Slice.t),
  "HMsg" ∷ p_ptr ↦[msgWrapT :: "msg"] #p_mt_ptr ∗
  "Hmsgown" ∷ msgT.own p_mt_ptr l_t.(msg) ∗
  "HSig" ∷ p_ptr ↦[msgWrapT :: "sig"] (slice_val p_sig) ∗
  "Hsl_own"  ∷ own_slice p_sig byteT 1 l_t.(sig) ∗
  "HSn" ∷ p_ptr ↦[msgWrapT :: "sn"] #l_t.(sn).

Lemma wp_encode (args_ptr : loc) (l_args : t):
  {{{
    own args_ptr l_args
  }}}
    encodeMsgWrapT #args_ptr
  {{{
    (p_sl : Slice.t) l_bytes,
    RET (slice_val p_sl);
    own args_ptr l_args ∗
    own_slice p_sl byteT 1 l_bytes ∗
    ⌜l_bytes = encodeF l_args⌝
  }}}.
Proof. Admitted.

Lemma wp_decode p_sl (l_bytes : list u8):
  {{{
    "Hsl" ∷ own_slice_small p_sl byteT 1 l_bytes ∗
    (* 96 is byte len of msgWrapT. *)
    "Hlen" ∷ ⌜length l_bytes = 96%nat⌝
  }}}
    decodeMsgWrapT (slice_val p_sl)
  {{{
    (args_ptr : loc) l_args (garb : val), RET (#args_ptr, garb);
    own args_ptr l_args
  }}}.
Proof. Admitted.

Lemma wp_new_slice:
  {{{ True }}}
    newMsgWrapTSlice #()
  {{{
    (sl : Slice.t) (l_bytes : list u8),
    RET (slice_val sl);
    own_slice sl byteT 1 l_bytes ∗
    ⌜length l_bytes = 96%nat⌝
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  unfold newMsgWrapTSlice.
  wp_apply wp_NewSlice.
  iIntros (s) "Hso".
  iApply "HΦ".
  iFrame.
  iPureIntro.
  rewrite replicate_length.
  word.
Qed.

End local_defs.
End msgWrapT.
