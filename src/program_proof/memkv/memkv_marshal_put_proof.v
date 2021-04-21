From Perennial.program_proof Require Import disk_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.goose_lang Require Import ffi.grove_ffi.
From Perennial.program_proof Require Import marshal_proof.

(*
  Defines Coq request and reply types for shard server Put RPC. Also defines
  has_encoding for Put Request/Reply and provides WPs for {de|en}codePutRe{ply|quest}()
 *)

Section memkv_marshal_put_proof.

Context `{!heapG Σ}.

Record PutRequestC := mkPutRequestC {
  PR_CID : u64;
  PR_Seq : u64;
  PR_Key : u64;
  PR_Value : list u8
}.

Record PutReplyC := mkPutReplyC {
  PR_Err : u64;
}.

Definition own_PutRequest args_ptr args : iProp Σ :=
  ∃ val_sl,
  "HCID" ∷ args_ptr ↦[PutRequest :: "CID"] #args.(PR_CID) ∗
  "HSeq" ∷ args_ptr ↦[PutRequest :: "Seq"] #args.(PR_Seq) ∗
  "HKey" ∷ args_ptr ↦[PutRequest :: "Key"] #args.(PR_Key) ∗
  "HValue" ∷ args_ptr ↦[PutRequest :: "Value"] (slice_val val_sl) ∗
  "HValue_sl" ∷ typed_slice.is_slice val_sl byteT 1%Qp args.(PR_Value) ∗
  "%HseqPositive" ∷ ⌜int.Z args.(PR_Seq) > 0⌝
.

Definition own_PutReply reply_ptr rep : iProp Σ :=
  "HErr" ∷ reply_ptr ↦[PutReply :: "Err"] #rep.(PR_Err)
.

Definition has_encoding_PutRequest (data:list u8) (args:PutRequestC) : Prop :=
  has_encoding data [ EncUInt64 args.(PR_CID) ; EncUInt64 args.(PR_Seq); EncUInt64 args.(PR_Key); EncUInt64 (length args.(PR_Value)) ; EncBytes args.(PR_Value) ].

Definition has_encoding_PutReply (data:list u8) (rep:PutReplyC) :=
  has_encoding data [ EncUInt64 rep.(PR_Err) ].

Lemma wp_encodePutRequest args_ptr args :
  {{{
       own_PutRequest args_ptr args
  }}}
    encodePutRequest #args_ptr
  {{{
       (reqData:list u8) req_sl, RET (slice_val req_sl); ⌜has_encoding_PutRequest reqData args⌝ ∗
                                               typed_slice.is_slice req_sl byteT 1%Qp reqData ∗
                                               own_PutRequest args_ptr args
  }}}.
Proof.
Admitted.

Lemma wp_decodePutRequest req_sl reqData args :
  {{{
       ⌜has_encoding_PutRequest reqData args⌝ ∗
       typed_slice.is_slice req_sl byteT 1%Qp reqData
  }}}
    decodePutRequest (slice_val req_sl)
  {{{
       (args_ptr:loc), RET #args_ptr; own_PutRequest args_ptr args
  }}}.
Proof.
Admitted.

Lemma has_encoding_PutRequest_inj (reqRaw:list u8) req req' :
  has_encoding_PutRequest reqRaw req →
  has_encoding_PutRequest reqRaw req' →
  req = req'.
Proof.
  intros.
  unfold has_encoding_PutRequest in *.
Admitted.

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
Admitted.

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
Admitted.

End memkv_marshal_put_proof.
