From Perennial.program_proof Require Import dist_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof Require Import marshal_proof.

(*
  Defines Coq request and reply types for shard server Put RPC. Also defines
  has_encoding for Put Request/Reply and provides WPs for {de|en}codePutRe{ply|quest}()
 *)

Section memkv_marshal_conditional_put_proof.

Context `{!heapG Σ}.

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
  "HExpValue_sl" ∷ typed_slice.is_slice expv_sl byteT 1%Qp args.(CPR_ExpValue) ∗
  "HNewValue_sl" ∷ typed_slice.is_slice newv_sl byteT 1%Qp args.(CPR_NewValue) ∗
  "%HseqPositive" ∷ ⌜int.Z args.(CPR_Seq) > 0⌝
.

Definition own_ConditionalPutReply reply_ptr rep : iProp Σ :=
  "HErr" ∷ reply_ptr ↦[ConditionalPutReply :: "Err"] #rep.(CPR_Err) ∗
  "HSucc" ∷ reply_ptr ↦[ConditionalPutReply :: "Success"] #rep.(CPR_Succ)
.

Definition has_encoding_ConditionalPutRequest (data:list u8) (args:ConditionalPutRequestC) : Prop :=
  has_encoding data [ EncUInt64 args.(CPR_CID) ; EncUInt64 args.(CPR_Seq); EncUInt64 args.(CPR_Key);
    EncUInt64 (length args.(CPR_ExpValue)) ; EncBytes args.(CPR_ExpValue);
    EncUInt64 (length args.(CPR_NewValue)) ; EncBytes args.(CPR_NewValue)  ].

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
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

End memkv_marshal_conditional_put_proof.
