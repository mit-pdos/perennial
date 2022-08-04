From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof Require Import marshal_stateless_proof.

Module ApplyArgs.
Record C :=
{
  epoch : u64 ;
  index : u64 ;
  op : list u8 ;
}.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u64_le args.(epoch)) ++ (u64_le args.(index)) ++ args.(op).

Context `{!heapGS Σ}.

Definition own args_ptr args : iProp Σ :=
  ∃ op_sl,
  "Hargs_epoch" ∷ args_ptr ↦[pb.ApplyArgs :: "epoch"] #args.(epoch) ∗
  "Hargs_index" ∷ args_ptr ↦[pb.ApplyArgs :: "index"] #args.(index) ∗
  "Hargs_op" ∷ args_ptr ↦[pb.ApplyArgs :: "op"] (slice_val op_sl) ∗
  "Hargs_op_sl" ∷ is_slice_small op_sl byteT 1 args.(op)
  .

Lemma wp_Encode (args_ptr:loc) (args:C) :
  {{{
        own args_ptr args
  }}}
    pb.EncodeApplyArgs #args_ptr
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc args⌝ ∗
        is_slice enc_sl byteT 1 enc
  }}}.
Proof.
  iIntros (Φ) "H1 HΦ".
  iNamed "H1".
  wp_call.
  wp_loadField.
  wp_apply (wp_slice_len).
  wp_pures.
  wp_apply (wp_NewSliceWithCap).
  { apply encoding.unsigned_64_nonneg. }
  iIntros (ptr) "Henc_sl".
  wp_apply (wp_ref_to).
  { done. }
  simpl.
  iIntros (enc_ptr) "Henc".
  wp_pures.
  wp_loadField.
  wp_load.
  wp_apply (wp_WriteInt with "Henc_sl").
  iIntros (enc_sl) "Henc_sl".
  wp_store.
  replace (int.nat 0) with (0%nat) by word.
  simpl.

  wp_loadField.
  wp_load.
  wp_apply (wp_WriteInt with "Henc_sl").
  iIntros (?) "Henc_sl".
  wp_store.

  wp_loadField.
  wp_load.
  wp_apply (wp_WriteBytes with "[$Henc_sl $Hargs_op_sl]").
  iIntros (?) "[Henc_sl Hargs_op_sl]".
  wp_store.

  wp_load.
  iApply "HΦ".
  iFrame "Henc_sl".
  iPureIntro.
  done.
Qed.

End ApplyArgs.

Module SetStateArgs.
Record C :=
{
  epoch : u64 ;
}.
End SetStateArgs.

Module GetStateArgs.
Record C :=
{
  epoch : u64 ;
}.
End GetStateArgs.

Module GetStateReply.
Record C :=
{
  err : u64 ;
  state : list u8 ;
}.
End GetStateReply.

Module BecomePrimaryArgs.
Record C :=
{
  epoch : u64 ;
  replicas : list chan ;
}.
End BecomePrimaryArgs.

Section pb_marshal.

Context `{!heapGS Σ, !stagedG Σ}.

Definition has_encoding_Error (encoded:list u8) (error:u64) : Prop :=
  encoded = (u64_le error).

End pb_marshal.
