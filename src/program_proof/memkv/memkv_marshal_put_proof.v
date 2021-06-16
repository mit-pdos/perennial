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
  PR_CID : u64;
  PR_Seq : u64;
  PR_Key : u64;
  PR_Value : list u8
}.

Record PutReplyC := mkPutReplyC {
  PR_Err : u64;
}.

Definition own_PutRequest args_ptr val_sl args : iProp Σ :=
  "HCID" ∷ args_ptr ↦[PutRequest :: "CID"] #args.(PR_CID) ∗
  "HSeq" ∷ args_ptr ↦[PutRequest :: "Seq"] #args.(PR_Seq) ∗
  "HKey" ∷ args_ptr ↦[PutRequest :: "Key"] #args.(PR_Key) ∗
  "HValue" ∷ args_ptr ↦[PutRequest :: "Value"] (slice_val val_sl) ∗
  "#HValue_sl" ∷ readonly (typed_slice.is_slice_small val_sl byteT 1 args.(PR_Value)) ∗
  "%HseqPositive" ∷ ⌜int.Z args.(PR_Seq) > 0⌝
.

Definition own_PutReply reply_ptr rep : iProp Σ :=
  "HErr" ∷ reply_ptr ↦[PutReply :: "Err"] #rep.(PR_Err)
.

Definition has_encoding_PutRequest (data:list u8) (args:PutRequestC) : Prop :=
  has_encoding data [ EncUInt64 args.(PR_CID) ; EncUInt64 args.(PR_Seq); EncUInt64 args.(PR_Key); EncUInt64 (length args.(PR_Value)) ; EncBytes args.(PR_Value) ] ∧
  int.Z args.(PR_Seq) > 0.

Definition has_encoding_PutReply (data:list u8) (rep:PutReplyC) :=
  has_encoding data [ EncUInt64 rep.(PR_Err) ].

Lemma wp_encodePutRequest args_ptr val_sl args :
  {{{
       own_PutRequest args_ptr val_sl args
  }}}
    encodePutRequest #args_ptr
  {{{
       (reqData:list u8) req_sl, RET (slice_val req_sl); ⌜has_encoding_PutRequest reqData args⌝ ∗
                                               typed_slice.is_slice req_sl byteT 1%Qp reqData ∗
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
  change (word.add (word.add (word.add 8 8) 8) 8) with (U64 32).
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
  iMod (readonly_load with "HValue_sl") as (q) "HValue_sl'".
  iDestruct (typed_slice.is_slice_small_sz with "HValue_sl'") as %Hsz.
  wp_apply (wp_slice_len).
  wp_apply (wp_Enc__PutInt with "Henc").
  { word. }
  iIntros "Henc".
  wp_pures.
  wp_loadField.
  wp_apply (wp_Enc__PutBytes with "[$Henc $HValue_sl']").
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
  rewrite /has_encoding_PutRequest.
  split; last done.
  replace (U64 (length args.(PR_Value))) with val_sl.(Slice.sz) by word.
  done.
Qed.

Lemma wp_decodePutRequest req_sl reqData args :
  {{{
       ⌜has_encoding_PutRequest reqData args⌝ ∗
       typed_slice.is_slice req_sl byteT 1%Qp reqData
  }}}
    decodePutRequest (slice_val req_sl)
  {{{
       (args_ptr:loc) val_sl, RET #args_ptr; own_PutRequest args_ptr val_sl args
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
  iIntros (??) "[Hsl Hdec]".
  wp_apply (wp_storeField with "Value").
  { apply slice_val_ty. }
  iIntros "Value".

  wp_pures.
  iApply "HΦ".
  iFrame.
  iPureIntro. done.
Qed.

Lemma wp_encodePutReply rep_ptr rep :
  {{{
       own_PutReply rep_ptr rep
  }}}
    encodePutReply #rep_ptr
  {{{
       repData rep_sl , RET (slice_val rep_sl);
       typed_slice.is_slice rep_sl byteT 1%Qp repData ∗
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

Lemma wp_decodePutReply rep rep_sl repData :
  {{{
       typed_slice.is_slice rep_sl byteT 1%Qp repData ∗
       ⌜has_encoding_PutReply repData rep ⌝
  }}}
    decodePutReply (slice_val rep_sl)
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

  iDestruct (typed_slice.is_slice_small_acc with "Hsl") as "[Hsl _]".
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
