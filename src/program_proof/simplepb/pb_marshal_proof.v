From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export pb.
From Perennial.program_proof Require Import marshal_stateless_proof.


Module ApplyAsBackupArgs.
Section ApplyAsBackupArgs.
Context `{!heapGS Σ}.

Record C :=
mkC {
  epoch : u64 ;
  index : u64 ;
  op : list u8 ;
}.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u64_le args.(epoch)) ++ (u64_le args.(index)) ++ args.(op).

Definition own args_ptr args : iProp Σ :=
  ∃ op_sl,
  "Hargs_epoch" ∷ args_ptr ↦[pb.ApplyAsBackupArgs :: "epoch"] #args.(epoch) ∗
  "Hargs_index" ∷ args_ptr ↦[pb.ApplyAsBackupArgs :: "index"] #args.(index) ∗
  "Hargs_op" ∷ args_ptr ↦[pb.ApplyAsBackupArgs :: "op"] (slice_val op_sl) ∗
  "Hargs_op_sl" ∷ is_slice_small op_sl byteT 1 args.(op)
  .

Definition own_ro args_ptr args : iProp Σ :=
  ∃ op_sl,
  "#Hargs_epoch" ∷ readonly (args_ptr ↦[pb.ApplyAsBackupArgs :: "epoch"] #args.(epoch)) ∗
  "#Hargs_index" ∷ readonly (args_ptr ↦[pb.ApplyAsBackupArgs :: "index"] #args.(index)) ∗
  "#Hargs_op" ∷ readonly (args_ptr ↦[pb.ApplyAsBackupArgs :: "op"] (slice_val op_sl)) ∗
  "#Hargs_op_sl" ∷ readonly (is_slice_small op_sl byteT 1 args.(op))
.

Lemma wp_Encode (args_ptr:loc) (args:C) :
  {{{
        own_ro args_ptr args
  }}}
    pb.EncodeApplyAsBackupArgs #args_ptr
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
  iMod (readonly_load with "Hargs_op_sl") as (?) "Hop_sl".
  wp_apply (wp_WriteBytes with "[$Henc_sl $Hop_sl]").
  iIntros (?) "[Henc_sl Hargs_op_sl2]".
  wp_store.

  wp_load.
  iApply "HΦ".
  iFrame "Henc_sl".
  done.
Qed.

Lemma wp_Decode enc enc_sl (args:C) :
  {{{
        ⌜has_encoding enc args⌝ ∗
        is_slice enc_sl byteT 1 enc
  }}}
    pb.DecodeApplyAsBackupArgs (slice_val enc_sl)
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
End ApplyAsBackupArgs.
End ApplyAsBackupArgs.

Module SetStateArgs.
Section SetStateArgs.
Context `{!heapGS Σ}.
Record C :=
mkC {
  epoch : u64 ;
  nextIndex: u64 ;
  state : list u8 ;
}.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u64_le args.(epoch)) ++ (u64_le args.(nextIndex)) ++ args.(state).


Definition own args_ptr args : iProp Σ :=
  ∃ state_sl,
  "Hargs_epoch" ∷ args_ptr ↦[pb.SetStateArgs :: "Epoch"] #args.(epoch) ∗
  "Hargs_next_index" ∷ args_ptr ↦[pb.SetStateArgs :: "NextIndex"] #args.(nextIndex) ∗
  "Hargs_state" ∷ args_ptr ↦[pb.SetStateArgs :: "State"] (slice_val state_sl) ∗
  "#Hargs_state_sl" ∷ readonly (is_slice_small state_sl byteT 1 args.(state))
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
  wp_apply (wp_WriteInt with "Henc_sl").
  iIntros (?) "Henc_sl".
  wp_store.

  wp_loadField.
  wp_load.
  iMod (readonly_load with "Hargs_state_sl") as (?) "Hsl".
  wp_apply (wp_WriteBytes with "[$Henc_sl $Hsl]").
  iIntros (?) "[Henc_sl _]".
  wp_store.
  wp_load.
  iModIntro.
  iApply "HΦ".
  iFrame "Henc_sl".
  iSplitL ""; first done.
  iExists _; iFrame "∗#".
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
  { repeat econstructor. Transparent slice.T. unfold slice.T. repeat econstructor.
    Opaque slice.T. } (* FIXME: don't want to unfold slice.T *)
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
  wp_apply (wp_ReadInt with "Henc_sl").
  iIntros (?) "Henc_sl".
  wp_pures.
  wp_storeField.
  wp_store.

  wp_load.
  wp_storeField.
  iApply "HΦ".
  iExists _; iFrame.
  iMod (readonly_alloc_1 with "Henc_sl") as "$".
  done.
Qed.

End SetStateArgs.
End SetStateArgs.

Module GetStateArgs.
Section GetStateArgs.
Context `{!heapGS Σ}.
Record C :=
mkC {
  epoch : u64 ;
}.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u64_le args.(epoch)).

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
        is_slice enc_sl byteT 1 enc ∗
        own args_ptr args
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
        is_slice_small enc_sl byteT 1 enc
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
End GetStateArgs.

Module GetStateReply.
Section GetStateReply.
Context `{!heapGS Σ}.
Record C :=
mkC {
  err : u64 ;
  nextIndex : u64 ;
  state : list u8 ;
}.

Definition has_encoding (encoded:list u8) (reply:C) : Prop :=
  encoded = (u64_le reply.(err)) ++ (u64_le reply.(nextIndex)) ++ reply.(state).

Definition own reply_ptr reply : iProp Σ :=
  ∃ state_sl,
  "Hreply_epoch" ∷ reply_ptr ↦[pb.GetStateReply :: "Err"] #reply.(err) ∗
  "Hreply_next_index" ∷ reply_ptr ↦[pb.GetStateReply :: "NextIndex"] #reply.(nextIndex) ∗
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
        is_slice_small enc_sl byteT 1 enc
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
  { repeat econstructor. Transparent slice.T. unfold slice.T. repeat econstructor.
    Opaque slice.T. } (* FIXME: don't want to unfold slice.T *)
  iIntros (args_ptr) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_pures.
  rewrite Henc.

  wp_load.
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

  iModIntro.
  iApply "HΦ".
  iExists _; iFrame.
Qed.

End GetStateReply.
End GetStateReply.

Module BecomePrimaryArgs.
Section BecomePrimaryArgs.
Context `{!heapGS Σ}.
Record C :=
mkC {
  epoch : u64 ;
  replicas : list chan ;
}.

Definition has_encoding (encoded:list u8) (args:C) : Prop :=
  encoded = (u64_le args.(epoch)) ++ (u64_le (length args.(replicas))) ++ (flat_map u64_le args.(replicas)).

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
        is_slice enc_sl byteT 1 enc ∗
        own args_ptr args
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
  wp_apply (wp_forSlice (V:=u64)
              (λ j,
                ∃ enc_sl (replicas_so_far:list chan),
  "%Hreplicas_prefix" ∷ ⌜replicas_so_far `prefix_of` args.(replicas)⌝ ∗
  "%Hreplicas_len" ∷ ⌜length replicas_so_far = int.nat j⌝ ∗
  "Henc" ∷ enc_ptr ↦[slice.T byteT] (slice_val enc_sl) ∗
  "Henc_sl" ∷ is_slice enc_sl byteT 1 (([] ++ u64_le args.(epoch)) ++ u64_le (length args.(replicas)) ++ (flat_map u64_le replicas_so_far))
              )%I
              with "[] [$Hargs_replicas_sl Henc Henc_sl]"
           ).
  {
    iIntros.
    clear Φ.
    iIntros (?) "!# (Hpre & %Hneq & %Hlookup) HΦ".
    iNamed "Hpre".
    wp_call.
    wp_load.
    wp_apply (wp_WriteInt with "Henc_sl").
    iIntros (?) "Henc_sl".
    wp_store.
    iApply "HΦ".
    iModIntro.
    iExists _, (replicas_so_far ++ [x]).
    iFrame.
    rewrite flat_map_app.
    iFrame.
    iPureIntro; split.
    {
      unfold prefix.
      destruct Hreplicas_prefix as [rest Hreplicas_prefix].
      exists (tail rest).
      rewrite Hreplicas_prefix.
      rewrite -app_assoc.
      rewrite Hreplicas_prefix in Hlookup.
      rewrite lookup_app_r in Hlookup; last first.
      { rewrite Hreplicas_len. done. }
      f_equal.
      rewrite Hreplicas_len in Hlookup.
      replace (int.nat i - int.nat i)%nat with (0%nat) in Hlookup by word.
      assert (length replicas_so_far < length args.(replicas)) by word.
      destruct rest.
      { done. }
      simpl.
      simpl in Hlookup.
      by inversion Hlookup.
    }
    {
      rewrite app_length //=.
      word.
    }
  }
  {
    iExists _, [].
    iFrame.
    iPureIntro; split; eauto.
    apply prefix_nil.
  }
  iIntros "[H1 Hsl]".
  iNamed "H1".
  wp_pures.
  wp_load.
  iModIntro.
  iApply "HΦ".
  iFrame "Henc_sl".
  replace (replicas_so_far) with (args.(replicas)); last first.
  { (* TODO: list_sover. *)
    rewrite -Hsz in Hreplicas_len.
    symmetry.
    apply list_prefix_eq; last word.
    done.
  }
  iFrame.
  iSplitR; first done.
  iExists _; iFrame.
Qed.

Lemma wp_Decode enc enc_sl (args:C) :
  {{{
        ⌜has_encoding enc args⌝ ∗
        is_slice_small enc_sl byteT 1 enc
  }}}
    pb.DecodeBecomePrimaryArgs (slice_val enc_sl)
  {{{
        args_ptr, RET #args_ptr; own args_ptr args
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
  rewrite Henc.
  wp_load.
  wp_apply (wp_ReadInt with "Henc_sl").
  iIntros (?) "Henc_sl".
  wp_pures.
  wp_storeField.
  wp_store.

  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (?) "Hlen".
  wp_load.

  wp_apply (wp_ReadInt with "Henc_sl").
  iIntros (?) "Henc_sl".
  wp_pures.
  wp_store.
  wp_store.
  wp_load.
  wp_apply (wp_NewSlice).
  iIntros (replicas_sl) "Hreplicas_sl".
  wp_storeField.
  wp_loadField.

  iDestruct (is_slice_to_small with "Hreplicas_sl") as "Hreplicas_sl".
  iDestruct (is_slice_small_sz with "Hreplicas_sl") as %Hreplicas_sz.
  (* FIXME: need to do a forSlice and write to the elements of that slice *)
  wp_apply (wp_forSlice (V:=u64)
              (λ j,
                ∃ (replicas_done replicas_left:list chan) enc_sl,
  "%Hreplicas_prefix" ∷ ⌜args.(replicas) = replicas_done ++ replicas_left⌝ ∗
  "%Hreplicas_len" ∷ ⌜length replicas_done = int.nat j⌝ ∗
  "Henc" ∷ enc_ptr ↦[slice.T byteT] (slice_val enc_sl) ∗
  "Henc_sl" ∷ is_slice_small enc_sl byteT 1 (flat_map u64_le replicas_left) ∗
  "HReplicas" ∷ args_ptr ↦[BecomePrimaryArgs :: "Replicas"] (slice_val replicas_sl) ∗
  "Hreplicas_sl" ∷ is_slice_small replicas_sl uint64T 1 (replicas_done ++ (replicate (length replicas_left) (U64 0)))
              )%I
              with "[] [$Hreplicas_sl Henc Henc_sl $Replicas]"
           ).
  {
    clear Φ.
    iIntros (???) "!# (Hpre & %Hineq & %Hlookup) HΦ".
    iNamed "Hpre".
    wp_call.
    wp_load.
    rewrite replicate_length in Hreplicas_sz.
    assert (int.nat i < length args.(replicas)).
    {
      admit.
    }
    destruct replicas_left as [|next_replica replicas_left'].
    { exfalso. rewrite -Hreplicas_len in H.
      rewrite app_nil_r in Hreplicas_prefix.
      rewrite Hreplicas_prefix in H.
      word.
    }

    replace (next_replica :: replicas_left') with ([next_replica] ++ replicas_left') by done.
    rewrite flat_map_app.
    wp_apply (wp_ReadInt with "Henc_sl").
    iIntros (?) "Henc_sl".
    wp_pures.
    wp_loadField.
    wp_apply (wp_SliceSet (V:=chan) with "[$Hreplicas_sl]").
    {
      iPureIntro.
      apply lookup_lt_is_Some_2.
      simpl.
      rewrite app_length.
      rewrite cons_length.
      admit.
    }
    iIntros "Hreplicas_sl".
    wp_pures.
    wp_store.
    iModIntro.
    iApply "HΦ".
    iExists _, _, _; iFrame.
    iSplitL "".
    {
      iPureIntro.
      rewrite Hreplicas_prefix.
      rewrite cons_middle.
      rewrite app_assoc.
      done.
    }
    iSplitL "".
    {
      iPureIntro.
      rewrite app_length.
      simpl.
      word.
    }
    iApply to_named.
    iExactEq "Hreplicas_sl".
    f_equal.
    apply list_eq.
    intros j.
    destruct (decide (j = int.nat i)).
    {
      rewrite e.
      rewrite list_lookup_insert; last first.
      {
        rewrite app_length.
        admit.
      }
      {
        rewrite lookup_app_l; last first.
        { rewrite -Hreplicas_len. rewrite app_length. simpl.
          unfold chan.
          word. }
        rewrite lookup_app_r; last first.
        {
          rewrite Hreplicas_len.
          word.
        }
        replace (int.nat i - length replicas_done)%nat with (0%nat) by word.
        rewrite list_lookup_singleton.
        done.
      }
    }
    {
      admit.
    }
  }
  {
    iExists _, _, _.
    iFrame "∗".
    admit.
  }

  iIntros "(H1 & _)".
  iNamed "H1".
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iExists _; iFrame.
  admit.
Admitted.

End BecomePrimaryArgs.
End BecomePrimaryArgs.

Module ApplyReply.
Section ApplyReply.
Context `{!heapGS Σ}.

Record C :=
mkC {
  err : u64 ;
  ret : list u8 ;
}.

Definition has_encoding (encoded:list u8) (reply:C) : Prop :=
  encoded = (u64_le reply.(err)) ++ reply.(ret).

Definition own args_ptr args : iProp Σ :=
  ∃ ret_sl,
  "Hreply_err" ∷ args_ptr ↦[pb.ApplyReply :: "Err"] #args.(err) ∗
  "Hreply_ret" ∷ args_ptr ↦[pb.ApplyReply :: "Reply"] (slice_val ret_sl) ∗
  "Hrepy_ret_sl" ∷ is_slice_small ret_sl byteT 1 args.(ret)
  .

Lemma wp_Encode (args_ptr:loc) (args:C) :
  {{{
        own args_ptr args
  }}}
    pb.EncodeApplyReply #args_ptr
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
  wp_apply (wp_WriteBytes with "[$]").
  iIntros (?) "[Henc_sl Hreply_ret_sl]".
  wp_store.

  wp_load.
  iApply "HΦ".
  iFrame "Henc_sl".
  iSplitL ""; first done.
  iExists _; iFrame.
  done.
Qed.

Lemma wp_Decode enc enc_sl (reply:C) :
  {{{
        ⌜has_encoding enc reply⌝ ∗
        is_slice_small enc_sl byteT 1 enc
  }}}
    pb.DecodeApplyReply (slice_val enc_sl)
  {{{
        args_ptr, RET #args_ptr; own args_ptr reply
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
End ApplyReply.
End ApplyReply.

Section pb_marshal.

Context `{!heapGS Σ, !stagedG Σ}.

Definition has_encoding_Error (encoded:list u8) (error:u64) : Prop :=
  encoded = (u64_le error).

End pb_marshal.
