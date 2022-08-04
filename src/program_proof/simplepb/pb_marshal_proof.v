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
        is_slice enc_sl byteT 1 enc ∗
        own args_ptr args
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
  iSplitL ""; first done.
  iExists _; iFrame.
  done.
Qed.

Lemma wp_Decode enc enc_sl (args:C) :
  {{{
        ⌜has_encoding enc args⌝ ∗
        is_slice enc_sl byteT 1 enc
  }}}
    pb.DecodeApplyArgs (slice_val enc_sl)
  {{{
        args_ptr, RET #args_ptr; own args_ptr args
  }}}.
Proof.
  iIntros (Φ) "[%Henc Henc_sl] HΦ".
  wp_call.
  wp_apply (wp_ref_to).
  { done. }
  iIntros (enc_ptr) "Henc".
  wp_pures.
  wp_apply (wp_allocStruct).
  { repeat econstructor. Transparent slice.T. unfold slice.T. repeat econstructor.
    Opaque slice.T. }
  iIntros (args_ptr) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH". simpl.
  wp_pures.

  rewrite /has_encoding in Henc.
  rewrite Henc.
  wp_load.
  iDestruct (is_slice_to_small with "Henc_sl") as "Henc_sl".
  wp_apply (wp_ReadInt with "Henc_sl").
  iIntros (?) "Henc_sl".
  wp_pures.
  wp_storeField.
  wp_store.

  wp_load.
  wp_apply (wp_ReadInt with "Henc_sl").
  iIntros (?) "Henc_sl".
  wp_pures.
  wp_storeField.
  wp_store.

  wp_load.
  wp_storeField.
  iApply "HΦ".
  iExists _; iFrame.
  done.
Qed.
End ApplyArgs.

Module SetStateArgs.
Record C :=
{
  epoch : u64 ;
  state : list u8 ;
}.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u64_le args.(epoch)) ++ args.(state).

Context `{!heapGS Σ}.

Definition own args_ptr args : iProp Σ :=
  ∃ state_sl,
  "Hargs_epoch" ∷ args_ptr ↦[pb.SetStateArgs :: "Epoch"] #args.(epoch) ∗
  "Hargs_state" ∷ args_ptr ↦[pb.SetStateArgs :: "State"] (slice_val state_sl) ∗
  "Hargs_state_sl" ∷ is_slice_small state_sl byteT 1 args.(state)
  .

Lemma wp_Encode (args_ptr:loc) (args:C) :
  {{{
        own args_ptr args
  }}}
    pb.EncodeSetStateArgs #args_ptr
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc args⌝ ∗
        is_slice enc_sl byteT 1 enc ∗
        own args_ptr args
  }}} .
Proof.
  iIntros (Φ) "H1 HΦ".
  iNamed "H1".
  wp_call.
  wp_loadField.
  wp_apply (wp_slice_len).
  wp_pures.
  wp_apply (wp_NewSliceWithCap).
  { apply encoding.unsigned_64_nonneg. }
  replace (int.nat 0) with (0%nat) by word.
  simpl.
  iIntros (?) "Henc_sl".
  wp_apply (wp_ref_to).
  { done. }
  iIntros (enc_ptr) "Henc".
  wp_pures.
  wp_loadField.
  wp_load.
  wp_apply (wp_WriteInt with "Henc_sl").
  iIntros (?) "Henc_sl".
  wp_store.
  wp_loadField.
  wp_load.
  wp_apply (wp_WriteBytes with "[$Henc_sl $Hargs_state_sl]").
  iIntros (?) "[Henc_sl Hargs_state_sl]".
  wp_store.
  wp_load.
  iModIntro.
  iApply "HΦ".
  iFrame "Henc_sl".
  iSplitL ""; first done.
  iExists _; iFrame.
Qed.

Lemma wp_Decode enc enc_sl (args:C) :
  {{{
        ⌜has_encoding enc args⌝ ∗
        is_slice enc_sl byteT 1 enc
  }}}
    pb.DecodeSetStateArgs (slice_val enc_sl)
  {{{
        args_ptr, RET #args_ptr; own args_ptr args
  }}}.
Proof.
  iIntros (Φ) "[%Henc Henc_sl] HΦ".
  wp_call.
  wp_apply (wp_ref_to).
  { done. }
  iIntros (enc_ptr) "Henc".

  wp_pures.
  wp_apply (wp_allocStruct).
  { naive_solver. }
  iIntros (args_ptr) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".

  wp_pures.
  wp_load.
  iDestruct (is_slice_to_small with "Henc_sl") as "Henc_sl".
  rewrite Henc.
  wp_apply (wp_ReadInt with "Henc_sl").
  iIntros (?) "Henc_sl".
  wp_pures.
  wp_storeField.
  wp_store.

  wp_load.
  wp_storeField.
  iModIntro.
  iApply "HΦ".
  iExists _; iFrame.
Qed.

End SetStateArgs.

Module GetStateArgs.
Record C :=
{
  epoch : u64 ;
}.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u64_le args.(epoch)).

Context `{!heapGS Σ}.

Definition own args_ptr args : iProp Σ :=
  "Hargs_epoch" ∷ args_ptr ↦[pb.GetStateArgs :: "Epoch"] #args.(epoch)
  .

Lemma wp_Encode (args_ptr:loc) (args:C) :
  {{{
        own args_ptr args
  }}}
    pb.EncodeGetStateArgs #args_ptr
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc args⌝ ∗
        is_slice enc_sl byteT 1 enc
  }}}.
Proof.
  iIntros (?) "H1 HΦ".
  iNamed "H1".
  wp_call.
  wp_apply (wp_NewSliceWithCap).
  { done. }
  iIntros (?) "Henc_sl".
  wp_apply (wp_ref_to).
  { done. }
  iIntros (enc_ptr) "Henc".
  wp_pures.
  wp_loadField.
  wp_load.
  wp_apply (wp_WriteInt with "Henc_sl").
  iIntros (?) "Henc_sl".
  wp_store.
  wp_load.
  iApply "HΦ".
  iFrame.
  done.
Qed.

Lemma wp_Decode enc enc_sl (args:C) :
  {{{
        ⌜has_encoding enc args⌝ ∗
        is_slice enc_sl byteT 1 enc
  }}}
    pb.DecodeGetStateArgs (slice_val enc_sl)
  {{{
        args_ptr, RET #args_ptr; own args_ptr args
  }}}.
Proof.
  iIntros (Φ) "[%Henc Henc_sl] HΦ".
  wp_call.
  wp_apply (wp_allocStruct).
  { naive_solver. }
  iIntros (args_ptr) "Hargs".
  wp_pures.
  iDestruct (is_slice_to_small with "Henc_sl") as "Henc_sl".
  rewrite Henc.
  wp_apply (wp_ReadInt with "Henc_sl").
  iIntros (?) "Henc_sl".
  wp_pures.
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_storeField.
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iFrame.
Qed.

End GetStateArgs.

Module GetStateReply.
Record C :=
{
  err : u64 ;
  state : list u8 ;
}.

Definition has_encoding (encoded:list u8) (reply:C) : Prop :=
  encoded = (u64_le reply.(err)) ++ reply.(state).

Context `{!heapGS Σ}.

Definition own reply_ptr reply : iProp Σ :=
  ∃ state_sl,
  "Hreply_epoch" ∷ reply_ptr ↦[pb.GetStateReply :: "Err"] #reply.(err) ∗
  "Hreply_state" ∷ reply_ptr ↦[pb.GetStateReply :: "State"] (slice_val state_sl) ∗
  "Hreply_state_sl" ∷ is_slice_small state_sl byteT 1 reply.(state)
  .

Lemma wp_Encode (reply_ptr:loc) (reply:C) :
  {{{
        own reply_ptr reply
  }}}
    pb.EncodeGetStateReply #reply_ptr
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc reply⌝ ∗
        is_slice enc_sl byteT 1 enc
  }}}.
Proof.
  iIntros (?) "H1 HΦ".
  iNamed "H1".
  wp_call.
  wp_loadField.
  wp_apply (wp_slice_len).
  wp_pures.
  wp_apply (wp_NewSliceWithCap).
  { apply encoding.unsigned_64_nonneg. }
  replace (int.nat 0) with (0%nat) by word.
  simpl.
  iIntros (?) "Henc_sl".
  wp_apply (wp_ref_to).
  { done. }
  iIntros (enc_ptr) "Henc".
  wp_pures.
  wp_loadField.
  wp_load.
  wp_apply (wp_WriteInt with "Henc_sl").
  iIntros (?) "Henc_sl".
  wp_store.
  wp_loadField.
  wp_load.
  wp_apply (wp_WriteBytes with "[$Henc_sl $Hreply_state_sl]").
  iIntros (?) "[Henc_sl Hreply_state_sl]".
  wp_store.
  wp_load.
  iModIntro.
  iApply "HΦ".
  iFrame.
  done.
Qed.

Lemma wp_Decode enc enc_sl (reply:C) :
  {{{
        ⌜has_encoding enc reply⌝ ∗
        is_slice enc_sl byteT 1 enc
  }}}
    pb.DecodeGetStateReply (slice_val enc_sl)
  {{{
        reply_ptr, RET #reply_ptr; own reply_ptr reply
  }}}.
Proof.
  iIntros (Φ) "[%Henc Henc_sl] HΦ".
  wp_call.
  wp_apply (wp_ref_to).
  { done. }
  iIntros (enc_ptr) "Henc".
  wp_apply (wp_allocStruct).
  { naive_solver. }
  iIntros (args_ptr) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_pures.
  iDestruct (is_slice_to_small with "Henc_sl") as "Henc_sl".
  rewrite Henc.
  wp_load.
  wp_apply (wp_ReadInt with "Henc_sl").
  iIntros (?) "Henc_sl".
  wp_pures.
  wp_storeField.
  wp_store.

  wp_load.
  wp_storeField.

  iModIntro.
  iApply "HΦ".
  iExists _; iFrame.
Qed.

End GetStateReply.

Module BecomePrimaryArgs.
Record C :=
{
  epoch : u64 ;
  replicas : list chan ;
}.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u64_le args.(epoch)) ++ (u64_le (length args.(replicas))) ++ (flat_map u64_le args.(replicas)).

Context `{!heapGS Σ}.

Definition own args_ptr args : iProp Σ :=
  ∃ replicas_sl,
  "Hargs_epoch" ∷ args_ptr ↦[pb.BecomePrimaryArgs :: "Epoch"] #args.(epoch) ∗
  "Hargs_replicas" ∷ args_ptr ↦[pb.BecomePrimaryArgs :: "Replicas"] (slice_val replicas_sl) ∗
  "Hargs_replicas_sl" ∷ is_slice_small replicas_sl uint64T 1 args.(replicas)
  .

Lemma wp_Encode (args_ptr:loc) (args:C) :
  {{{
        own args_ptr args
  }}}
    pb.EncodeBecomePrimaryArgs #args_ptr
  {{{
        enc enc_sl, RET (slice_val enc_sl);
        ⌜has_encoding enc args⌝ ∗
        is_slice enc_sl byteT 1 enc
  }}}.
Proof.
  iIntros (?) "H1 HΦ".
  iNamed "H1".
  wp_call.
  wp_loadField.
  wp_apply (wp_slice_len).
  wp_pures.
  wp_apply (wp_NewSliceWithCap).
  { apply encoding.unsigned_64_nonneg. }
  replace (int.nat 0) with (0%nat) by word.
  simpl.
  iIntros (?) "Henc_sl".
  wp_apply (wp_ref_to).
  { done. }
  iIntros (enc_ptr) "Henc".
  wp_pures.
  wp_loadField.
  wp_load.
  wp_apply (wp_WriteInt with "Henc_sl").
  iIntros (?) "Henc_sl".
  wp_store.
  wp_loadField.
  wp_apply (wp_slice_len).
  iDestruct (is_slice_small_sz with "Hargs_replicas_sl") as %Hsz.
  wp_load.
  wp_apply (wp_WriteInt with "Henc_sl").
  iIntros (?) "Henc_sl".
  wp_store.
  replace (replicas_sl.(Slice.sz)) with (U64 (length args.(replicas))) by word.

  wp_loadField.
  (*
  wp_apply (wp_forSlice
              (λ j,
                ∃ enc_sl (replicas_so_far:list chan),
  "%Hreplicas" ∷ True ∗
  "Henc" ∷ enc_ptr ↦[slice.T byteT] (slice_val enc_sl) ∗
  "Henc_sl" ∷ is_slice enc_sl byteT 1 (([] ++ u64_le args.(epoch)) ++ u64_le (length args.(replicas)) ++ (flat_map u64_le replicas_so_far))
              )%I
              with "[] [] []"
           ). *)
Admitted.

Lemma wp_Decode enc enc_sl (args:C) :
  {{{
        ⌜has_encoding enc args⌝ ∗
        is_slice enc_sl byteT 1 enc
  }}}
    pb.DecodeBecomePrimaryArgs (slice_val enc_sl)
  {{{
        args_ptr, RET #args_ptr; own args_ptr args
  }}}.
Admitted.

End BecomePrimaryArgs.

Section pb_marshal.

Context `{!heapGS Σ, !stagedG Σ}.

Definition has_encoding_Error (encoded:list u8) (error:u64) : Prop :=
  encoded = (u64_le error).

End pb_marshal.
