From Perennial.Helpers Require Import ModArith.
From Perennial.program_proof Require Import grove_prelude std_proof.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof Require Import marshal_proof.

(*
  Defines Coq request and reply types for shard server Put RPC. Also defines
  has_encoding for Put Request/Reply and provides WPs for {de|en}codePutRe{ply|quest}()
 *)

Section memkv_marshal_put_proof.

Context `{!heapGS Σ}.

Record PutRequestC := mkPutRequestC {
  PR_Key : u64;
  PR_Value : list u8
}.

Record PutReplyC := mkPutReplyC {
  PR_Err : u64;
}.

Definition own_PutRequest args_ptr val_sl args : iProp Σ :=
  "HKey" ∷ args_ptr ↦[PutRequest :: "Key"] #args.(PR_Key) ∗
  "HValue" ∷ args_ptr ↦[PutRequest :: "Value"] (slice_val val_sl) ∗
  "#HValue_sl" ∷ typed_slice.own_slice_small val_sl byteT DfracDiscarded args.(PR_Value)
.

Definition own_PutReply reply_ptr rep : iProp Σ :=
  "HErr" ∷ reply_ptr ↦[PutReply :: "Err"] #rep.(PR_Err)
.

Definition has_encoding_PutRequest (data:list u8) (args:PutRequestC) : Prop :=
  has_encoding data [ EncUInt64 args.(PR_Key); EncUInt64 (length args.(PR_Value)) ; EncBytes args.(PR_Value) ].

Definition has_encoding_PutReply (data:list u8) (rep:PutReplyC) :=
  has_encoding data [ EncUInt64 rep.(PR_Err) ].

Lemma wp_EncodePutRequest args_ptr val_sl args :
  {{{
       own_PutRequest args_ptr val_sl args
  }}}
    EncodePutRequest #args_ptr
  {{{
       (reqData:list u8) req_sl, RET (slice_val req_sl); ⌜has_encoding_PutRequest reqData args⌝ ∗
                                               typed_slice.own_slice req_sl byteT (DfracOwn 1) reqData ∗
                                               own_PutRequest args_ptr val_sl args
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
  iIntros (Hnooverflow).

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

  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (rep_sl repData).
  iIntros "(%Henc & %Hlen & Hrep_sl)".
  iApply "HΦ".
  iFrame "∗#".
  iPureIntro.
  rewrite /has_encoding_PutRequest.
  replace (W64 (length args.(PR_Value))) with val_sl.(Slice.sz) by word.
  done.
Qed.

Lemma wp_DecodePutRequest req_sl reqData args :
  {{{
       ⌜has_encoding_PutRequest reqData args⌝ ∗
       typed_slice.own_slice_small req_sl byteT (DfracOwn 1) reqData
  }}}
    DecodePutRequest (slice_val req_sl)
  {{{
       (args_ptr:loc) val_sl, RET #args_ptr; own_PutRequest args_ptr val_sl args
  }}}.
Proof.
  iIntros (Φ) "[%Henc Hsl] HΦ".
  wp_lam.
  wp_apply (wp_allocStruct); first val_ty.
  iIntros (rep_ptr) "Hrep".
  iDestruct (struct_fields_split with "Hrep") as "HH".
  iNamed "HH".
  wp_pures.

  wp_apply (wp_new_dec with "[$Hsl]").
  { done. }
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
  iFrame "∗#".
  done.
Qed.

Lemma wp_EncodePutReply rep_ptr rep :
  {{{
       own_PutReply rep_ptr rep
  }}}
    EncodePutReply #rep_ptr
  {{{
       repData rep_sl , RET (slice_val rep_sl);
       typed_slice.own_slice rep_sl byteT (DfracOwn 1) repData ∗
       ⌜has_encoding_PutReply repData rep ⌝
  }}}.
Proof.
  iIntros (Φ) "Hrep HΦ".

  wp_lam.
  wp_pures.
  iNamed "Hrep".

  wp_apply (wp_new_enc).
  iIntros (enc) "Henc".
  wp_pures.

  wp_loadField.
  wp_apply (wp_Enc__PutInt with "Henc").
  { word. }
  iIntros "Henc".
  wp_pures.

  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (rep_sl repData).
  iIntros "(%Henc & %Hlen & Hrep_sl)".
  iApply "HΦ".
  iFrame.
  iPureIntro.
  rewrite /has_encoding_PutReply.
  done.
Qed.

Lemma wp_DecodePutReply rep rep_sl repData :
  {{{
       typed_slice.own_slice_small rep_sl byteT (DfracOwn 1) repData ∗
       ⌜has_encoding_PutReply repData rep ⌝
  }}}
    DecodePutReply (slice_val rep_sl)
  {{{
       (rep_ptr:loc) , RET #rep_ptr;
       own_PutReply rep_ptr rep
  }}}.
Proof.
  iIntros (Φ) "[Hsl %Henc] HΦ".
  wp_lam.
  wp_apply (wp_allocStruct).
  {
    naive_solver.
  }
  iIntros (rep_ptr) "Hrep".
  iDestruct (struct_fields_split with "Hrep") as "HH".
  iNamed "HH".
  wp_pures.

  wp_apply (wp_new_dec with "[$Hsl]").
  { done. }
  iIntros (?) "Hdec".
  wp_pures.

  wp_apply (wp_Dec__GetInt with "[$Hdec]").
  iIntros "Hdec".
  wp_storeField.

  iApply "HΦ".
  iModIntro.
  iFrame.
Qed.

End memkv_marshal_put_proof.
