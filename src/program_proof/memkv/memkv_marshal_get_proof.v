From Perennial.Helpers Require Import ModArith.
From Perennial.program_proof Require Import grove_prelude std_proof.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof Require Import marshal_proof.

(*
  Defines Coq request and reply types for shard server Get RPC. Also defines
  has_encoding for Get Request/Reply and provides WPs for {de|en}codeGetRe{ply|quest}()
 *)

Section memkv_marshal_get_proof.

Context `{!heapGS Σ}.

Record GetRequestC := mkGetRequestC {
  GR_Key : u64
}.

Record GetReplyC := mkGetReplyC {
  GR_Err : u64;
  GR_Value : list u8
}.

Definition own_GetRequest args_ptr args : iProp Σ :=
  "HKey" ∷ args_ptr ↦[GetRequest :: "Key"] #args.(GR_Key)
.

Definition own_GetReply reply_ptr rep : iProp Σ :=
  ∃ val_sl,
  "HErr" ∷ reply_ptr ↦[GetReply :: "Err"] #rep.(GR_Err) ∗
  "HValue" ∷ reply_ptr ↦[GetReply :: "Value"] (slice_val val_sl) ∗
  "#HValue_sl" ∷ typed_slice.own_slice_small val_sl byteT DfracDiscarded rep.(GR_Value)
.

Definition has_encoding_GetRequest (data:list u8) (args:GetRequestC) :=
  has_encoding data [ EncUInt64 args.(GR_Key) ].

Definition has_encoding_GetReply (data:list u8) (rep:GetReplyC) :=
  has_encoding data [ EncUInt64 rep.(GR_Err) ; EncUInt64 (length rep.(GR_Value)) ; EncBytes rep.(GR_Value) ].

Lemma wp_EncodeGetRequest args_ptr args :
  {{{
       own_GetRequest args_ptr args
  }}}
    EncodeGetRequest #args_ptr
  {{{
       (reqData:list u8) req_sl, RET (slice_val req_sl); ⌜has_encoding_GetRequest reqData args⌝ ∗
                                               typed_slice.own_slice req_sl byteT (DfracOwn 1) reqData ∗
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

  wp_apply (wp_Enc__Finish with "[$Henc]").
  iIntros (??) "(%Henc & Hlen & Hsl)".
  iApply "HΦ".
  iFrame.
  done.
Qed.

Lemma wp_DecodeGetRequest req_sl reqData args :
  {{{
       ⌜has_encoding_GetRequest reqData args⌝ ∗
       typed_slice.own_slice_small req_sl byteT (DfracOwn 1) reqData
  }}}
    DecodeGetRequest (slice_val req_sl)
  {{{
       (args_ptr:loc), RET #args_ptr; own_GetRequest args_ptr args
  }}}.
Proof.
  iIntros (Φ) "[%Henc Hsl] HΦ".
  wp_lam.
  wp_apply (wp_allocStruct); first val_ty.
  iIntros (rep_ptr) "Hrep".
  iDestruct (struct_fields_split with "Hrep") as "HH".
  iNamed "HH".
  wp_pures.
  wp_apply (wp_new_dec with "[$Hsl]"); first done.
  iIntros (?) "Hdec".
  wp_pures.

  wp_apply (wp_Dec__GetInt with "[$Hdec]").
  iIntros "Hdec".
  wp_storeField.

  iApply "HΦ". iModIntro. by iFrame.
Qed.

Lemma wp_DecodeGetReply rep rep_sl repData :
  {{{
       typed_slice.own_slice_small rep_sl byteT (DfracOwn 1) repData ∗
       ⌜has_encoding_GetReply repData rep ⌝
  }}}
    DecodeGetReply (slice_val rep_sl)
  {{{
       (rep_ptr:loc) , RET #rep_ptr;
       own_GetReply rep_ptr rep
  }}}.
Proof.
  iIntros (Φ) "[Hsl %Henc] HΦ".
  wp_lam.
  wp_apply (wp_allocStruct); first val_ty.
  iIntros (rep_ptr) "Hrep".
  iDestruct (struct_fields_split with "Hrep") as "HH".
  iNamed "HH".
  wp_pures.

  wp_apply (wp_new_dec with "[$Hsl]"); first done.
  iIntros (?) "Hdec".
  wp_pures.

  wp_apply (wp_Dec__GetInt with "[$Hdec]").
  iIntros "Hdec".
  wp_storeField.

  wp_apply (wp_Dec__GetInt with "[$Hdec]").
  iIntros "Hdec".
  wp_apply (wp_Dec__GetBytes with "[$Hdec]"); first done.
  iIntros (??) "[Hsl Hdec]".
  wp_storeField.

  iMod (own_slice_small_persist with "Hsl") as "#Hsl".

  wp_pures.
  iApply "HΦ".
  iModIntro.
  iExists _.
  by iFrame.
Qed.

Lemma wp_EncodeGetReply rep_ptr rep :
  {{{
       own_GetReply rep_ptr rep
  }}}
    EncodeGetReply #rep_ptr
  {{{
       repData rep_sl , RET (slice_val rep_sl);
       typed_slice.own_slice rep_sl byteT (DfracOwn 1) repData ∗
       ⌜has_encoding_GetReply repData rep ⌝
  }}}.
Proof.
  iIntros (Φ) "Hrep HΦ".

  wp_lam.
  wp_pures.
  iNamed "Hrep".
  wp_loadField.
  wp_apply (wp_slice_len).
  wp_apply wp_SumAssumeNoOverflow.
  change (word.add 8 8) with (W64 16).
  iIntros (Hoverflow).

  wp_apply (wp_new_enc).
  iIntros (enc) "Henc".
  wp_pures.

  wp_loadField.
  wp_apply (wp_Enc__PutInt with "Henc").
  { word. }
  iIntros "Henc".
  wp_pures.

  wp_loadField.
  iDestruct (typed_slice.own_slice_small_sz with "HValue_sl") as %Hsz.
  wp_apply (wp_slice_len).
  wp_apply (wp_Enc__PutInt with "Henc").
  { word. }
  iIntros "Henc".
  wp_pures.
  wp_loadField.
  wp_apply (wp_Enc__PutBytes with "[$Henc $HValue_sl]").
  { word. }
  iIntros "[Henc _]".
  wp_pures.

  wp_apply (wp_Enc__Finish with "[$Henc]").
  iIntros (rep_sl repData).
  iIntros "(% & % & Hrep_sl)".
  iApply "HΦ".
  iFrame.
  iPureIntro.
  unfold has_encoding_GetReply.
  replace (W64 (length rep.(GR_Value))) with val_sl.(Slice.sz) by word.
  done.
Qed.

End memkv_marshal_get_proof.
