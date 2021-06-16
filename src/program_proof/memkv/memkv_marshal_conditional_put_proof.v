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
  CPR_CID : u64;
  CPR_Seq : u64;
  CPR_Key : u64;
  CPR_ExpValue : list u8;
  CPR_NewValue : list u8;
}.

Record ConditionalPutReplyC := mkConditionalPutReplyC {
  CPR_Err : u64;
  CPR_Succ : bool;
}.

Definition own_ConditionalPutRequest args_ptr expv_sl newv_sl args : iProp Σ :=
  "HCID" ∷ args_ptr ↦[ConditionalPutRequest :: "CID"] #args.(CPR_CID) ∗
  "HSeq" ∷ args_ptr ↦[ConditionalPutRequest :: "Seq"] #args.(CPR_Seq) ∗
  "HKey" ∷ args_ptr ↦[ConditionalPutRequest :: "Key"] #args.(CPR_Key) ∗
  "HExpValue" ∷ args_ptr ↦[ConditionalPutRequest :: "ExpectedValue"] (slice_val expv_sl) ∗
  "HNewValue" ∷ args_ptr ↦[ConditionalPutRequest :: "NewValue"] (slice_val newv_sl) ∗
  "#HExpValue_sl" ∷ readonly (typed_slice.is_slice_small expv_sl byteT 1%Qp args.(CPR_ExpValue)) ∗
  "#HNewValue_sl" ∷ readonly (typed_slice.is_slice_small newv_sl byteT 1%Qp args.(CPR_NewValue)) ∗
  "%HseqPositive" ∷ ⌜int.Z args.(CPR_Seq) > 0⌝
.

Definition own_ConditionalPutReply reply_ptr rep : iProp Σ :=
  "HErr" ∷ reply_ptr ↦[ConditionalPutReply :: "Err"] #rep.(CPR_Err) ∗
  "HSucc" ∷ reply_ptr ↦[ConditionalPutReply :: "Success"] #rep.(CPR_Succ)
.

Definition has_encoding_ConditionalPutRequest (data:list u8) (args:ConditionalPutRequestC) : Prop :=
  has_encoding data [ EncUInt64 args.(CPR_CID) ; EncUInt64 args.(CPR_Seq); EncUInt64 args.(CPR_Key);
    EncUInt64 (length args.(CPR_ExpValue)) ; EncBytes args.(CPR_ExpValue);
    EncUInt64 (length args.(CPR_NewValue)) ; EncBytes args.(CPR_NewValue)  ] ∧
  int.Z args.(CPR_Seq) > 0.

Definition has_encoding_ConditionalPutReply (data:list u8) (rep:ConditionalPutReplyC) :=
  has_encoding data [ EncUInt64 rep.(CPR_Err); EncBool rep.(CPR_Succ) ].

Lemma wp_encodeConditionalPutRequest args_ptr expv_sl newv_sl args :
  {{{
       own_ConditionalPutRequest args_ptr expv_sl newv_sl args
  }}}
    encodeConditionalPutRequest #args_ptr
  {{{
       (reqData:list u8) req_sl, RET (slice_val req_sl); ⌜has_encoding_ConditionalPutRequest reqData args⌝ ∗
         typed_slice.is_slice req_sl byteT 1%Qp reqData ∗
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
  change (word.add (word.add (word.add (word.add 8 8) 8) 8) 8) with (U64 40).
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
  wp_apply (wp_Enc__PutInt with "Henc").
  { word. }
  iIntros "Henc".
  wp_pures.

  wp_loadField.
  wp_apply (wp_Enc__PutInt with "Henc").
  { word. }
  iIntros "Henc".
  wp_pures.

  wp_loadField.
  iMod (readonly_load with "HExpValue_sl") as (q) "HExpValue_sl'".
  iDestruct (typed_slice.is_slice_small_sz with "HExpValue_sl'") as %Hsz.
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
  iMod (readonly_load with "HNewValue_sl") as (q') "HNewValue_sl'".
  iDestruct (typed_slice.is_slice_small_sz with "HNewValue_sl'") as %Hsz'.
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
  split; last word.
  rewrite /has_encoding_ConditionalPutRequest.
  split; last done.
  replace (U64 (length args.(CPR_ExpValue))) with expv_sl.(Slice.sz) by word.
  replace (U64 (length args.(CPR_NewValue))) with newv_sl.(Slice.sz) by word.
  done.
Qed.

Lemma wp_decodeConditionalPutRequest req_sl reqData args :
  {{{
       ⌜has_encoding_ConditionalPutRequest reqData args⌝ ∗
       typed_slice.is_slice req_sl byteT 1%Qp reqData
  }}}
    decodeConditionalPutRequest (slice_val req_sl)
  {{{
       (args_ptr:loc) expv_sl newv_sl, RET #args_ptr; own_ConditionalPutRequest args_ptr expv_sl newv_sl args
  }}}.
Proof.
  iIntros (Φ) "[%Henc Hsl] HΦ".
  wp_lam.
  wp_apply (wp_allocStruct).
  {
    rewrite zero_slice_val.
    naive_solver.
  }
  iIntros (rep_ptr) "Hrep".
  iDestruct (struct_fields_split with "Hrep") as "HH".
  iNamed "HH".
  wp_pures.

  iDestruct (typed_slice.is_slice_small_acc with "Hsl") as "[Hsl _]".
  destruct Henc as [Henc Hseq].
  wp_apply (wp_new_dec with "[$Hsl]").
  { done. }
  iIntros (?) "Hdec".
  wp_pures.

  wp_apply (wp_Dec__GetInt with "[$Hdec]").
  iIntros "Hdec".
  wp_storeField.

  wp_apply (wp_Dec__GetInt with "[$Hdec]").
  iIntros "Hdec".
  wp_storeField.

  wp_apply (wp_Dec__GetInt with "[$Hdec]").
  iIntros "Hdec".
  wp_storeField.

  wp_apply (wp_Dec__GetInt with "[$Hdec]").
  iIntros "Hdec".
  wp_apply (wp_Dec__GetBytes_ro with "[$Hdec]"); first done.
  iIntros (??) "[Hexp_sl Hdec]".
  wp_apply (wp_storeField with "ExpectedValue").
  { apply slice_val_ty. }
  iIntros "ExpectedValue".

  wp_apply (wp_Dec__GetInt with "[$Hdec]").
  iIntros "Hdec".
  wp_apply (wp_Dec__GetBytes_ro with "[$Hdec]"); first done.
  iIntros (??) "[Hnew_sl Hdec]".
  wp_apply (wp_storeField with "NewValue").
  { apply slice_val_ty. }
  iIntros "NewValue".

  wp_pures.
  iApply "HΦ".
  iFrame.
  iPureIntro. done.
Qed.

Lemma wp_encodeConditionalPutReply rep_ptr rep :
  {{{
       own_ConditionalPutReply rep_ptr rep
  }}}
    encodeConditionalPutReply #rep_ptr
  {{{
       repData rep_sl, RET (slice_val rep_sl);
       typed_slice.is_slice rep_sl byteT 1%Qp repData ∗
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

Lemma wp_decodeConditionalPutReply rep rep_sl repData :
  {{{
       typed_slice.is_slice rep_sl byteT 1%Qp repData ∗
       ⌜has_encoding_ConditionalPutReply repData rep ⌝
  }}}
    decodeConditionalPutReply (slice_val rep_sl)
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

  iDestruct (typed_slice.is_slice_small_acc with "Hsl") as "[Hsl _]".
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
