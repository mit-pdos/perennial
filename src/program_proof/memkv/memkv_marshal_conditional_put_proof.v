From Perennial.Helpers Require Import ModArith.
From Perennial.program_proof Require Import grove_prelude std_proof.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof Require Import marshal_proof.

(*
  Defines Coq request and reply types for shard server Put RPC. Also defines
  has_encoding for Put Request/Reply and provides WPs for {de|en}codePutRe{ply|quest}()
 *)

Section memkv_marshal_conditional_put_proof.

Context `{!heapGS Σ}.

Record ConditionalPutRequestC := mkConditionalPutRequestC {
  CPR_Key : u64;
  CPR_ExpValue : list u8;
  CPR_NewValue : list u8;
}.

Record ConditionalPutReplyC := mkConditionalPutReplyC {
  CPR_Err : u64;
  CPR_Succ : bool;
}.

Definition own_ConditionalPutRequest args_ptr expv_sl newv_sl args : iProp Σ :=
  "HKey" ∷ args_ptr ↦[ConditionalPutRequest :: "Key"] #args.(CPR_Key) ∗
  "HExpValue" ∷ args_ptr ↦[ConditionalPutRequest :: "ExpectedValue"] (slice_val expv_sl) ∗
  "HNewValue" ∷ args_ptr ↦[ConditionalPutRequest :: "NewValue"] (slice_val newv_sl) ∗
  "#HExpValue_sl" ∷ typed_slice.own_slice_small expv_sl byteT DfracDiscarded args.(CPR_ExpValue) ∗
  "#HNewValue_sl" ∷ typed_slice.own_slice_small newv_sl byteT DfracDiscarded args.(CPR_NewValue)
.

Definition own_ConditionalPutReply reply_ptr rep : iProp Σ :=
  "HErr" ∷ reply_ptr ↦[ConditionalPutReply :: "Err"] #rep.(CPR_Err) ∗
  "HSucc" ∷ reply_ptr ↦[ConditionalPutReply :: "Success"] #rep.(CPR_Succ)
.

Definition has_encoding_ConditionalPutRequest (data:list u8) (args:ConditionalPutRequestC) : Prop :=
  has_encoding data [ EncUInt64 args.(CPR_Key);
    EncUInt64 (length args.(CPR_ExpValue)) ; EncBytes args.(CPR_ExpValue);
    EncUInt64 (length args.(CPR_NewValue)) ; EncBytes args.(CPR_NewValue)  ].

Definition has_encoding_ConditionalPutReply (data:list u8) (rep:ConditionalPutReplyC) :=
  has_encoding data [ EncUInt64 rep.(CPR_Err); EncBool rep.(CPR_Succ) ].

Lemma wp_EncodeConditionalPutRequest args_ptr expv_sl newv_sl args :
  {{{
       own_ConditionalPutRequest args_ptr expv_sl newv_sl args
  }}}
    EncodeConditionalPutRequest #args_ptr
  {{{
       (reqData:list u8) req_sl, RET (slice_val req_sl); ⌜has_encoding_ConditionalPutRequest reqData args⌝ ∗
         typed_slice.own_slice req_sl byteT (DfracOwn 1) reqData ∗
         own_ConditionalPutRequest args_ptr expv_sl newv_sl args
  }}}.
Proof.
  iIntros (Φ) "Hrep HΦ".

  wp_lam.
  wp_pures.
  iNamed "Hrep".

  wp_loadField.
  wp_apply (wp_slice_len).
  wp_loadField.
  wp_apply (wp_slice_len).
  wp_apply wp_SumAssumeNoOverflow.
  iIntros (Hnooverflow1). wp_pures.
  wp_apply wp_SumAssumeNoOverflow.
  change (word.add (word.add 8 8) 8) with (W64 24).
  iIntros (Hnooverflow2).

  wp_apply (wp_new_enc).
  iIntros (enc) "Henc".
  wp_pures.

  wp_loadField.
  wp_apply (wp_Enc__PutInt with "Henc").
  { word. }
  iIntros "Henc".
  wp_pures.

  wp_loadField.
  iMod (own_slice_small_persist with "HExpValue_sl") as "#HExpValue_sl'".
  iDestruct (typed_slice.own_slice_small_sz with "HExpValue_sl'") as %Hsz.
  wp_apply (wp_slice_len).
  wp_apply (wp_Enc__PutInt with "Henc").
  { word. }
  iIntros "Henc".
  wp_pures.
  wp_loadField.
  wp_apply (wp_Enc__PutBytes with "[$Henc $HExpValue_sl']").
  { word. }
  iIntros "[Henc _]".
  wp_pures.

  wp_loadField.
  iMod (own_slice_small_persist with "HNewValue_sl") as "#HNewValue_sl'".
  iDestruct (typed_slice.own_slice_small_sz with "HNewValue_sl'") as %Hsz'.
  wp_apply (wp_slice_len).
  wp_apply (wp_Enc__PutInt with "Henc").
  { word. }
  iIntros "Henc".
  wp_pures.
  wp_loadField.
  wp_apply (wp_Enc__PutBytes with "[$Henc $HNewValue_sl']").
  { word. }
  iIntros "[Henc _]".
  wp_pures.

  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (rep_sl repData).
  iIntros "(%Henc & %Hlen & Hrep_sl)".
  iApply "HΦ".
  iFrame "∗#".
  iPureIntro.
  rewrite /has_encoding_ConditionalPutRequest.
  replace (W64 (length args.(CPR_ExpValue))) with expv_sl.(Slice.sz) by word.
  replace (W64 (length args.(CPR_NewValue))) with newv_sl.(Slice.sz) by word.
  done.
Qed.

Lemma wp_DecodeConditionalPutRequest req_sl reqData args :
  {{{
       ⌜has_encoding_ConditionalPutRequest reqData args⌝ ∗
       typed_slice.own_slice_small req_sl byteT (DfracOwn 1) reqData
  }}}
    DecodeConditionalPutRequest (slice_val req_sl)
  {{{
       (args_ptr:loc) expv_sl newv_sl, RET #args_ptr; own_ConditionalPutRequest args_ptr expv_sl newv_sl args
  }}}.
Proof.
  iIntros (Φ) "[%Henc Hsl] HΦ".
  wp_lam.
  wp_apply (wp_allocStruct).
  { val_ty. }
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
  iIntros (??) "[Hexp_sl Hdec]".
  wp_storeField.

  wp_apply (wp_Dec__GetInt with "[$Hdec]").
  iIntros "Hdec".
  wp_apply (wp_Dec__GetBytes with "[$Hdec]"); first done.
  iIntros (??) "[Hnew_sl Hdec]".
  wp_storeField.

  wp_pures.
  iApply "HΦ".
  iFrame.

  iMod (own_slice_small_persist with "Hexp_sl") as "#Hexp_sl".
  iMod (own_slice_small_persist with "Hnew_sl") as "#Hnew_sl".
  iFrame "#".
  iPureIntro. done.
Qed.

Lemma wp_EncodeConditionalPutReply rep_ptr rep :
  {{{
       own_ConditionalPutReply rep_ptr rep
  }}}
    EncodeConditionalPutReply #rep_ptr
  {{{
       repData rep_sl, RET (slice_val rep_sl);
       typed_slice.own_slice rep_sl byteT (DfracOwn 1) repData ∗
       ⌜has_encoding_ConditionalPutReply repData rep ⌝
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

  wp_loadField.
  wp_apply (wp_Enc__PutBool with "Henc").
  { word. }
  iIntros "Henc".
  wp_pures.

  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (rep_sl repData).
  iIntros "(%Henc & %Hlen & Hrep_sl)".
  iApply "HΦ".
  iFrame.
  iPureIntro.
  rewrite /has_encoding_ConditionalPutReply.
  done.
Qed.

Lemma wp_DecodeConditionalPutReply rep rep_sl repData :
  {{{
       typed_slice.own_slice_small rep_sl byteT (DfracOwn 1) repData ∗
       ⌜has_encoding_ConditionalPutReply repData rep ⌝
  }}}
    DecodeConditionalPutReply (slice_val rep_sl)
  {{{
       (rep_ptr:loc) , RET #rep_ptr;
       own_ConditionalPutReply rep_ptr rep
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

  wp_apply (wp_Dec__GetBool with "[$Hdec]").
  iIntros "Hdec".
  wp_storeField.

  iApply "HΦ".
  iModIntro.
  iFrame.
Qed.

End memkv_marshal_conditional_put_proof.
