From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.secure_chat.kt Require Import shared.
From Perennial.program_proof Require Import marshal_stateless_proof.

Section Bytes.
Context `{!heapGS Σ}.

Lemma wp_BytesEqual sl_b0 sl_b1 (b0 b1:list u8) :
  {{{
    "Hb0" ∷ own_slice_small sl_b0 byteT 1 b0 ∗
    "Hb1" ∷ own_slice_small sl_b1 byteT 1 b1
  }}}
  BytesEqual (slice_val sl_b0) (slice_val sl_b1)
  {{{
    (eqb:bool), RET #eqb;
    "Hb0" ∷ own_slice_small sl_b0 byteT 1 b0 ∗
    "Hb1" ∷ own_slice_small sl_b1 byteT 1 b1 ∗
    "%Heqb" ∷ ⌜eqb ↔ b0 = b1⌝
  }}}.
Proof. Admitted.
End Bytes.

Module UnameKey.
Record t :=
  mk {
    Uname: u64;
    Key: list u8;
  }.

Definition encodesF (arg:t) : list u8 :=
  u64_le arg.(Uname) ++ arg.(Key).
Definition encodes (argB:list u8) (arg:t) : Prop :=
  argB = encodesF arg.

Section local_defs.
Context `{!heapGS Σ}.
Definition own ptr arg : iProp Σ :=
  ∃ sl_key,
  "Huname" ∷ ptr ↦[UnameKey :: "Uname"] #arg.(Uname) ∗
  "Hkey" ∷ own_slice_small sl_key byteT 1 arg.(Key) ∗
  "Hsl_key" ∷ ptr ↦[UnameKey :: "Key"] (slice_val sl_key).

Lemma wp_DeepCopy ptr0 arg0 :
  {{{
    "Harg0" ∷ own ptr0 arg0
  }}}
  UnameKey__DeepCopy #ptr0
  {{{
    ptr1, RET #ptr1;
    "Harg0" ∷ own ptr0 arg0 ∗
    "Harg1" ∷ own ptr1 arg0
  }}}.
Proof. Admitted.

Lemma wp_IsEqual ptr0 arg0 ptr1 arg1 :
  {{{
    "Harg0" ∷ own ptr0 arg0 ∗
    "Harg1" ∷ own ptr1 arg1
  }}}
  UnameKey__IsEqual #ptr0 #ptr1
  {{{
    (eqb:bool), RET #eqb;
    "Harg0" ∷ own ptr0 arg0 ∗
    "Harg1" ∷ own ptr1 arg1 ∗
    "%Heqb" ∷ ⌜eqb ↔ arg0.(Uname) = arg1.(Uname) ∧ arg0.(Key) = arg1.(Key)⌝
  }}}.
Proof. Admitted.

Lemma wp_Encode ptr arg :
  {{{
    "Harg" ∷ own ptr arg
  }}}
    UnameKey__Encode #ptr
  {{{
    sl_argB (argB:list u8), RET (slice_val sl_argB);
    "Harg" ∷ own ptr arg ∗
    "HargB" ∷ own_slice_small sl_argB byteT 1 argB ∗
    "%Henc" ∷ ⌜encodes argB arg⌝
  }}}.
Proof. Admitted.

Lemma wp_Decode sl_fullB fullB ptr :
  {{{
    "HfullB" ∷ own_slice_small sl_fullB byteT 1 fullB
  }}}
    UnameKey__Decode #ptr (slice_val sl_fullB)
  {{{
    sl_remB (err:u64) arg argB remB, RET ((slice_val sl_remB), #err);
    if bool_decide (err = 0) then
      "Harg" ∷ own ptr arg ∗
      "HremB" ∷ own_slice_small sl_remB byteT 1 remB ∗
      "%Hsplit" ∷ ⌜fullB = argB ++ remB⌝ ∗
      "%Henc" ∷ ⌜encodes argB arg⌝
    else True%I
  }}}.
Proof. Admitted.

End local_defs.
End UnameKey.

Module KeyLog.
Record t :=
  mk {
    Log: list UnameKey.t
  }.

Definition encodesF (arg:t) : list u8 :=
  u64_le (length arg.(Log)) ++ list_bind _ _ UnameKey.encodesF arg.(Log).
Definition encodes (argB:list u8) (arg:t) : Prop :=
  argB = encodesF arg.

Section local_defs.
Context `{!heapGS Σ}.
Definition own ptr arg : iProp Σ :=
  ∃ sl_log log,
  "Hlog" ∷ [∗ list] x0;x1 ∈ log;arg.(Log), UnameKey.own x0 x1 ∗
  "Hsl_log" ∷ own_slice_small sl_log ptrT 1 log ∗
  "Hptr_log" ∷ ptr ↦[KeyLog :: "Log"] (slice_val sl_log).

Lemma wp_New :
  {{{ True }}}
  NewKeyLog #()
  {{{
    ptr, RET #ptr;
    own ptr (mk [])
  }}}.
Proof. Admitted.

Lemma wp_DeepCopy ptr0 arg0 :
  {{{
    "Harg0" ∷ own ptr0 arg0
  }}}
  KeyLog__DeepCopy #ptr0
  {{{
    ptr1, RET #ptr1;
    "Harg0" ∷ own ptr0 arg0 ∗
    "Harg1" ∷ own ptr1 arg0
  }}}.
Proof. Admitted.

Lemma wp_IsPrefix ptr_short arg_short ptr_long arg_long :
  {{{
    "Hshort" ∷ own ptr_short arg_short ∗
    "Hlong" ∷ own ptr_long arg_long
  }}}
  KeyLog__IsPrefix #ptr_short #ptr_long
  {{{
    (eqb:bool), RET #eqb;
    "Hshort" ∷ own ptr_short arg_short ∗
    "Hlong" ∷ own ptr_long arg_long ∗
    "%Heq" ∷ ⌜eqb ↔ arg_short.(Log) `prefix_of` arg_long.(Log)⌝
  }}}.
Proof. Admitted.

(* Note: not sure exactly what properties we need in the postcond here.
  elem_of might be too weak.
  We could also use stdpp list_find with an identity P and reversed list,
  although that might be unnecessarily complicated if we never use the
  "first" property.
  list_find also doesn't have any lemmas about reversed lists.
*)
Lemma wp_Lookup ptr arg (uname:u64) :
  {{{
    "Harg" ∷ own ptr arg
  }}}
  KeyLog__Lookup #ptr #uname
  {{{
    (idx:u64) sl_found (found:list u8) (ok:bool), RET (#idx, (slice_val sl_found), #ok);
    "Harg" ∷ own ptr arg ∗
    if ok then
      "Hfound" ∷ own_slice_small sl_found byteT 1 found ∗
      "%Hfound_idx" ∷ ⌜arg.(Log) !! uint.nat idx = Some (UnameKey.mk uname found)⌝
    else True%I
  }}}.
Proof. Admitted.

Lemma wp_Len ptr arg :
  {{{
    "Harg" ∷ own ptr arg
  }}}
  KeyLog__Len #ptr
  {{{
    RET #(I64 (length arg.(Log)));
    "Harg" ∷ own ptr arg
  }}}.
Proof. Admitted.

Lemma wp_Append ptr arg ptr_new arg_new :
  {{{
    "Harg" ∷ own ptr arg ∗
    "Hnew" ∷ UnameKey.own ptr_new arg_new
  }}}
  KeyLog__Append #ptr #ptr_new
  {{{
    RET #();
    "Harg" ∷ own ptr (mk (arg.(Log) ++ [arg_new]))
  }}}.
Proof. Admitted.

Lemma wp_Encode ptr arg :
  {{{
    "Harg" ∷ own ptr arg
  }}}
    KeyLog__Encode #ptr
  {{{
    sl_argB (argB:list u8), RET (slice_val sl_argB);
    "Harg" ∷ own ptr arg ∗
    "HargB" ∷ own_slice_small sl_argB byteT 1 argB ∗
    "%Henc" ∷ ⌜encodes argB arg⌝
  }}}.
Proof. Admitted.

Lemma wp_Decode sl_fullB fullB ptr :
  {{{
    "HfullB" ∷ own_slice_small sl_fullB byteT 1 fullB
  }}}
    KeyLog__Decode #ptr (slice_val sl_fullB)
  {{{
    sl_remB (err:u64) arg argB remB, RET ((slice_val sl_remB), #err);
    if bool_decide (err = 0) then
      "Harg" ∷ own ptr arg ∗
      "HremB" ∷ own_slice_small sl_remB byteT 1 remB ∗
      "%Hsplit" ∷ ⌜fullB = argB ++ remB⌝ ∗
      "%Henc" ∷ ⌜encodes argB arg⌝
    else True%I
  }}}.
Proof. Admitted.

End local_defs.
End KeyLog.

Module SigLog.
Record t :=
  mk {
    Sig: list u8;
    Log: KeyLog.t;
  }.

Definition encodesF (arg:t) : list u8 :=
  arg.(Sig) ++ KeyLog.encodesF arg.(Log).
Definition encodes (argB:list u8) (arg:t) : Prop :=
  argB = encodesF arg.

Section local_defs.
Context `{!heapGS Σ}.
Definition own ptr arg : iProp Σ :=
  ∃ sl_sig ptr_log,
  "Hsig" ∷ own_slice_small sl_sig byteT 1 arg.(Sig) ∗
  "Hptr_sig" ∷ ptr ↦[SigLog :: "Sig"] (slice_val sl_sig) ∗
  "Hlog" ∷ KeyLog.own ptr_log arg.(Log) ∗
  "Hptr_log" ∷ ptr ↦[SigLog :: "Log"] #ptr_log.

Lemma wp_Encode ptr arg :
  {{{
    "Harg" ∷ own ptr arg
  }}}
    SigLog__Encode #ptr
  {{{
    sl_argB (argB:list u8), RET (slice_val sl_argB);
    "Harg" ∷ own ptr arg ∗
    "HargB" ∷ own_slice_small sl_argB byteT 1 argB ∗
    "%Henc" ∷ ⌜encodes argB arg⌝
  }}}.
Proof. Admitted.

Lemma wp_Decode sl_fullB fullB ptr :
  {{{
    "HfullB" ∷ own_slice_small sl_fullB byteT 1 fullB
  }}}
    SigLog__Decode #ptr (slice_val sl_fullB)
  {{{
    sl_remB (err:u64) arg argB remB, RET ((slice_val sl_remB), #err);
    if bool_decide (err = 0) then
      "Harg" ∷ own ptr arg ∗
      "HremB" ∷ own_slice_small sl_remB byteT 1 remB ∗
      "%Hsplit" ∷ ⌜fullB = argB ++ remB⌝ ∗
      "%Henc" ∷ ⌜encodes argB arg⌝
    else True%I
  }}}.
Proof. Admitted.

End local_defs.
End SigLog.
