From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.goose_lang Require Import ffi.grove_ffi.
From Perennial.program_proof Require Import marshal_proof.

(*
  Defines Coq request and reply types for shard server Get RPC. Also defines
  has_encoding for Get Request/Reply and provides WPs for {de|en}codeGetRe{ply|quest}()
 *)

Section memkv_marshal_get_proof.

Context `{!heapG Σ}.

Record GetRequestC := mkGetRequestC {
  GR_CID : u64;
  GR_Seq : u64;
  GR_Key : u64
}.

Record GetReplyC := mkGetReplyC {
  GR_Err : u64;
  GR_Value : list u8
}.

Definition own_GetRequest args_ptr args : iProp Σ :=
  "HCID" ∷ args_ptr ↦[GetRequest.S :: "CID"] #args.(GR_CID) ∗
  "HSeq" ∷ args_ptr ↦[GetRequest.S :: "Seq"] #args.(GR_Seq) ∗
  "HKey" ∷ args_ptr ↦[GetRequest.S :: "Key"] #args.(GR_Key)
.

Definition own_GetReply reply_ptr rep : iProp Σ :=
  ∃ val_sl,
  "HErr" ∷ reply_ptr ↦[GetReply.S :: "Err"] #rep.(GR_Err) ∗
  "HValue" ∷ reply_ptr ↦[GetReply.S :: "Value"] (slice_val val_sl) ∗
  "HValue_sl" ∷ ∃ (q:Qp), (typed_slice.is_slice_small val_sl byteT q rep.(GR_Value))
.

Definition has_encoding_GetRequest (data:list u8) (args:GetRequestC) :=
  has_encoding data [ EncUInt64 args.(GR_CID) ; EncUInt64 args.(GR_Seq) ; EncUInt64 args.(GR_Key) ].

Definition has_encoding_GetReply (data:list u8) (rep:GetReplyC) :=
  has_encoding data [ EncUInt64 rep.(GR_Err) ; EncUInt64 (length rep.(GR_Value)) ; EncBytes rep.(GR_Value) ].

Lemma wp_encodeGetRequest args_ptr args :
  {{{
       own_GetRequest args_ptr args
  }}}
    encodeGetRequest #args_ptr
  {{{
       (reqData:list u8) req_sl, RET (slice_val req_sl); ⌜has_encoding_GetRequest reqData args⌝ ∗
                                               typed_slice.is_slice req_sl byteT 1%Qp reqData ∗
                                               own_GetRequest args_ptr args
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_lam.
  wp_apply (wp_new_enc).
  iIntros (?) "Henc".
  wp_pures.

  wp_loadField.
  wp_apply (wp_Enc__PutInt with "[$Henc]").
  { done. }
  iIntros "Henc".
  wp_pures.

  wp_loadField.
  wp_apply (wp_Enc__PutInt with "[$Henc]").
  { done. }
  iIntros "Henc".
  wp_pures.

  wp_loadField.
  wp_apply (wp_Enc__PutInt with "[$Henc]").
  { done. }
  iIntros "Henc".
  wp_pures.

  wp_apply (wp_Enc__Finish with "[$Henc]").
  iIntros (??) "(%Henc & Hlen & Hsl)".
  iApply "HΦ".
  iFrame.
  done.
Qed.

Lemma wp_decodeGetRequest req_sl reqData args :
  {{{
       ⌜has_encoding_GetRequest reqData args⌝ ∗
       typed_slice.is_slice req_sl byteT 1%Qp reqData
  }}}
    decodeGetRequest (slice_val req_sl)
  {{{
       (args_ptr:loc), RET #args_ptr; own_GetRequest args_ptr args
  }}}.
Proof.
Admitted.

Lemma has_encoding_GetRequest_inj (reqRaw:list u8) req req' :
  has_encoding_GetRequest reqRaw req →
  has_encoding_GetRequest reqRaw req' →
  req = req'.
Proof.
  intros.
  unfold has_encoding_GetRequest in *.
Admitted.

Lemma wp_decodeGetReply rep rep_sl repData :
  {{{
       typed_slice.is_slice rep_sl byteT 1%Qp repData ∗
       ⌜has_encoding_GetReply repData rep ⌝
  }}}
    decodeGetReply (slice_val rep_sl)
  {{{
       (rep_ptr:loc) , RET #rep_ptr;
       own_GetReply rep_ptr rep
  }}}.
Proof.
  iIntros (Φ) "[Hsl %Henc] HΦ".
  wp_lam.
  wp_apply (wp_allocStruct).
  { unfold GetReply.S. simpl.
    unfold ErrorType. admit. }
  iIntros (rep_ptr) "Hrep".
  iDestruct (struct_fields_split with "Hrep") as "HH".
  iNamed "HH".
  wp_pures.
  iDestruct (typed_slice.is_slice_small_acc with "Hsl") as "[Hsl Hsl_close]".
  wp_apply (wp_new_dec with "[$Hsl]").
  { done. }
  iIntros (?) "Hdec".
  wp_pures.

  wp_apply (wp_Dec__GetInt with "[$Hdec]").
  iIntros "Hdec".
  wp_storeField.

  wp_apply (wp_Dec__GetInt with "[$Hdec]").
  iIntros "Hdec".
  wp_apply (wp_Dec__GetBytes with "[$Hdec]").
  { admit. } (* TODO: make a "safe_size_sl" predicate and keep it everywhere *)
  iIntros (??) "[Hsl Hdec]".
  wp_apply (wp_storeField with "Value").
  { apply slice_val_ty. }
  iIntros "Value".
  wp_pures.
  iApply "HΦ".
  iModIntro.
  iExists _.
  iFrame.
  iExists _; iFrame.
Admitted.

Lemma wp_encodeGetReply rep_ptr rep :
  {{{
       own_GetReply rep_ptr rep
  }}}
    encodeGetReply #rep_ptr
  {{{
       repData rep_sl , RET (slice_val rep_sl);
       typed_slice.is_slice rep_sl byteT 1%Qp repData ∗
       ⌜has_encoding_GetReply repData rep ⌝
  }}}.
Proof.
  iIntros (Φ) "Hrep HΦ".

  wp_lam.
  wp_pures.
  iNamed "Hrep".
  wp_loadField.
  wp_apply (wp_slice_len).
  wp_pures.

  wp_apply (wp_new_enc).
  iIntros (enc) "Henc".
  wp_pures.

  wp_loadField.
  wp_apply (wp_Enc__PutInt with "Henc").
  { admit. (* TODO: overflow *) }
  iIntros "Henc".
  wp_pures.

  wp_loadField.
  wp_apply (wp_slice_len).
  wp_apply (wp_Enc__PutInt with "Henc").
  { admit. (* TODO: overflow *) }
  iIntros "Henc".
  wp_pures.

  wp_loadField.
  iDestruct "HValue_sl" as (?) "HValue_sl".
  wp_apply (wp_Enc__PutBytes with "[$Henc $HValue_sl]").
  { admit. } (* TODO: overflow *)
  iIntros "[Henc Hsl]".
  wp_pures.
  wp_apply (wp_Enc__Finish with "[$Henc]").
  iIntros (rep_sl repData).
  iIntros "(% & % & Hrep_sl)".
  iApply "HΦ".
  iFrame.
  iDestruct (typed_slice.is_slice_small_sz with "Hsl") as %Hsz.
  iPureIntro.
  unfold has_encoding_GetReply.
  rewrite Hsz.
  assert (U64 (int.nat (Slice.sz val_sl)) = (Slice.sz val_sl)).
  { admit. }
  rewrite H1.
  rewrite app_nil_l in H.
  simpl in H.
  done.
Admitted.

End memkv_marshal_get_proof.
