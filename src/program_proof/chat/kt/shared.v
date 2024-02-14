From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.secure_chat.kt Require Import shared.
From Perennial.program_proof Require Import marshal_stateless_proof.

Section Bytes.
Context `{!heapGS Σ}.

Lemma wp_BytesEqual b1 b2 b1L b2L :
  {{{
    "Hb1" ∷ own_slice_small b1 byteT 1 b1L ∗
    "Hb2" ∷ own_slice_small b2 byteT 1 b2L
  }}}
  BytesEqual (slice_val b1) (slice_val b2)
  {{{
    (eqb:bool), RET #eqb;
    "Hb1" ∷ own_slice_small b1 byteT 1 b1L ∗
    "Hb2" ∷ own_slice_small b2 byteT 1 b2L ∗
    "%Heqb" ∷ ⌜eqb ↔ b1L ≡ b2L⌝
  }}}.
Proof. Admitted.
End Bytes.

Module UnameKey.
Record t :=
  mk {
    Uname: u64;
    Key: list u8;
  }.

Definition encodesF (a:t) : list u8 :=
  u64_le a.(Uname) ++ a.(Key).
Definition encodes (x:list u8) (a:t) : Prop :=
  x = encodesF a.

Section local_defs.
Context `{!heapGS Σ}.
Definition own l args : iProp Σ :=
  ∃ key,
  "Huname" ∷ l ↦[UnameKey :: "Uname"] #args.(Uname) ∗
  "Hkey" ∷ l ↦[UnameKey :: "Key"] (slice_val key) ∗
  "Hkey_sl" ∷ own_slice_small key byteT 1 args.(Key).

Lemma wp_DeepCopy l1 uk :
  {{{
    "Huk1" ∷ own l1 uk
  }}}
  UnameKey__DeepCopy #l1
  {{{
    l2, RET #l2;
    "Huk1" ∷ own l1 uk ∗
    "Huk2" ∷ own l2 uk
  }}}.
Proof. Admitted.

Lemma wp_IsEqual l1 uk1 l2 uk2 :
  {{{
    "Huk1" ∷ own l1 uk1 ∗
    "Huk2" ∷ own l2 uk2
  }}}
  UnameKey__IsEqual #l1 #l2
  {{{
    (eqb:bool), RET #eqb;
    "Huk1" ∷ own l1 uk1 ∗
    "Huk2" ∷ own l2 uk2 ∗
    "%Heqb" ∷ ⌜eqb ↔ uk1.(Uname) = uk2.(Uname) ∧ uk1.(Key) ≡ uk2.(Key)⌝
  }}}.
Proof. Admitted.

Lemma wp_encode args_ptr args :
  {{{
    "Hargs" ∷ own args_ptr args
  }}}
    UnameKey__Encode #args_ptr
  {{{
    sl enc_args, RET (slice_val sl);
    "Hargs" ∷ own args_ptr args ∗
    "%Henc" ∷ ⌜encodes enc_args args⌝ ∗
    "Hsl" ∷ own_slice_small sl byteT 1 enc_args
  }}}.
Proof. Admitted.

Lemma wp_decode sl fullB args_ptr :
  {{{
    "Hsl" ∷ own_slice_small sl byteT 1 fullB
  }}}
    UnameKey__Decode #args_ptr (slice_val sl)
  {{{
    sl_rem args (err:u64) fstB sndB, RET ((slice_val sl_rem), #err);
    if bool_decide (err = 0) then
      "%Hsplit" ∷ ⌜fullB = fstB ++ sndB⌝ ∗
      "%Henc" ∷ ⌜encodes fstB args⌝ ∗
      "Hargs" ∷ own args_ptr args ∗
      "Hrem" ∷ own_slice_small sl_rem byteT 1 sndB
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

Notation mk_new := (mk []).
Definition encodesF (a:t) : list u8 :=
  u64_le (length a.(Log)) ++ list_bind _ _ UnameKey.encodesF a.(Log).
Definition encodes (x:list u8) (a:t) : Prop :=
  x = encodesF a.

Section local_defs.
Context `{!heapGS Σ}.
Definition own l args : iProp Σ :=
  ∃ sl_args lptrs,
  "Hlog" ∷ l ↦[KeyLog :: "Log"] (slice_val sl_args) ∗
  "Hsl" ∷ own_slice_small sl_args ptrT 1 lptrs ∗
  "Hptrs" ∷ [∗ list]  x1;x2 ∈ lptrs;args.(Log), UnameKey.own x1 x2.

Lemma wp_New :
  {{{ True }}}
  NewKeyLog #()
  {{{
    args_ptr, RET #args_ptr;
    own args_ptr mk_new
  }}}.
Proof. Admitted.

Lemma wp_DeepCopy l1 log :
  {{{
    "Hlog1" ∷ own l1 log
  }}}
  KeyLog__DeepCopy #l1
  {{{
    l2, RET #l2;
    "Hlog1" ∷ own l1 log ∗
    "hlog2" ∷ own l2 log
  }}}.
Proof. Admitted.

Lemma wp_IsPrefix ptr_short short ptr_long long :
  {{{
    "Hshort" ∷ own ptr_short short ∗
    "Hlong" ∷ own ptr_long long
  }}}
  KeyLog__IsPrefix #ptr_short #ptr_long
  {{{
    (eqb:bool), RET #eqb;
    "Hshort" ∷ own ptr_short short ∗
    "Hlong" ∷ own ptr_long long ∗
    "%Heq" ∷ ⌜eqb ↔ short.(Log) `prefix_of` long.(Log)⌝
  }}}.
Proof. Admitted.

(* Note: not sure exactly what properties we need in the postcond here.
  elem_of might be too weak.
  We could also use stdpp list_find with an identity P and reversed list,
  although that might be unnecessarily complicated if we never use the
  "first" property.
  list_find also doesn't have any lemmas about reversed lists.
*)
Lemma wp_Lookup ptr args (uname:u64) :
  {{{
    "Hlog" ∷ own ptr args
  }}}
  KeyLog__Lookup #ptr #uname
  {{{
    (idx:u64) key_sl (key:list u8) (ok:bool), RET (#idx, (slice_val key_sl), #ok);
    "Hlog" ∷ own ptr args ∗
    if ok then
      "Hkey" ∷ own_slice_small key_sl byteT 1 key ∗
      "%Hkey_elem_of" ∷ ⌜args.(Log) !! int.nat idx = Some (UnameKey.mk uname key)⌝
    else True%I
  }}}.
Proof. Admitted.

Lemma wp_Len ptr args :
  {{{
    "Hlog" ∷ own ptr args
  }}}
  KeyLog__Len #ptr
  {{{
    RET #(U64 (length args.(Log)));
    "Hlog" ∷ own ptr args
  }}}.
Proof. Admitted.

Lemma wp_Append ptr args ptrUk argsUk :
  {{{
    "Hlog" ∷ own ptr args ∗
    "Huk" ∷ UnameKey.own ptrUk argsUk
  }}}
  KeyLog__Len #ptr #ptrUk
  {{{
    RET #();
    "Hlog" ∷ own ptr (mk (args.(Log) ++ [argsUk]))
  }}}.
Proof. Admitted.

Lemma wp_encode ptr args :
  {{{
    "Hlog" ∷ own ptr args
  }}}
    KeyLog__Encode #ptr
  {{{
    sl_enc enc, RET (slice_val sl_enc);
    "Hlog" ∷ own ptr args ∗
    "Henc" ∷ own_slice_small sl_enc byteT 1 enc ∗
    "%Henc" ∷ ⌜encodes enc args⌝
  }}}.
Proof. Admitted.

Lemma wp_decode sl fullB args_ptr :
  {{{
    "Hsl" ∷ own_slice_small sl byteT 1 fullB
  }}}
    KeyLog__Decode #args_ptr (slice_val sl)
  {{{
    sl_rem args (err:u64) fstB sndB, RET ((slice_val sl_rem), #err);
    if bool_decide (err = 0) then
      "Hrem" ∷ own_slice_small sl_rem byteT 1 sndB ∗
      "%Hsplit" ∷ ⌜fullB = fstB ++ sndB⌝ ∗
      "%Henc" ∷ ⌜encodes fstB args⌝ ∗
      "Hargs" ∷ own args_ptr args
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

Definition encodesF (a:t) : list u8 :=
  a.(Sig) ++ KeyLog.encodesF a.(Log).
Definition encodes (x:list u8) (a:t) : Prop :=
  x = encodesF a.

Section local_defs.
Context `{!heapGS Σ}.
Definition own ptr args : iProp Σ :=
  ∃ sl_sig ptr_log,
  "Hsig_sl" ∷ own_slice_small sl_sig byteT 1 args.(Sig) ∗
  "Hsig" ∷ ptr ↦[SigLog :: "Sig"] (slice_val sl_sig) ∗
  "Hlog_own" ∷ KeyLog.own ptr_log args.(Log) ∗
  "Hlog" ∷ ptr ↦[SigLog :: "Log"] #ptr_log.

Lemma wp_encode ptr args :
  {{{
    "Hlog" ∷ own ptr args
  }}}
    SigLog__Encode #ptr
  {{{
    sl_enc enc, RET (slice_val sl_enc);
    "Hlog" ∷ own ptr args ∗
    "Henc" ∷ own_slice_small sl_enc byteT 1 enc ∗
    "%Henc" ∷ ⌜encodes enc args⌝
  }}}.
Proof. Admitted.

Lemma wp_decode sl fullB args_ptr :
  {{{
    "Hsl" ∷ own_slice_small sl byteT 1 fullB
  }}}
    SigLog__Decode #args_ptr (slice_val sl)
  {{{
    sl_rem args (err:u64) fstB sndB, RET ((slice_val sl_rem), #err);
    if bool_decide (err = 0) then
      "Hrem" ∷ own_slice_small sl_rem byteT 1 sndB ∗
      "%Hsplit" ∷ ⌜fullB = fstB ++ sndB⌝ ∗
      "%Henc" ∷ ⌜encodes fstB args⌝ ∗
      "Hargs" ∷ own args_ptr args
    else True%I
  }}}.
Proof. Admitted.

End local_defs.
End SigLog.
