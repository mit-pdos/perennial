From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.goose_lang Require Import ffi.grove_ffi.

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
  "HValue_sl" ∷ typed_slice.is_slice val_sl byteT 1%Qp rep.(GR_Value)
.

Axiom has_encoding_GetRequest : (list u8) → GetRequestC → Prop.
Axiom has_encoding_GetReply : (list u8) → GetReplyC → Prop.

Lemma wp_encodeGetRequest (cid seq key:u64) :
  {{{
       True
  }}}
    encodeGetRequest (#cid, (#seq, (#key, #())))%V
  {{{
       (reqData:list u8) req_sl, RET (slice_val req_sl); ⌜has_encoding_GetRequest reqData {| GR_CID:=cid; GR_Seq:=seq; GR_Key:=key |}⌝ ∗
                                               typed_slice.is_slice req_sl byteT 1%Qp reqData
  }}}.
Proof.
Admitted.

Lemma has_encoding_GetRequest_inj (reqRaw:list u8) req req' :
  has_encoding_GetRequest reqRaw req →
  has_encoding_GetRequest reqRaw req' →
  req = req'.
Proof.
Admitted.

Lemma wp_decodeGetReply rep rep_sl repData :
  {{{
       typed_slice.is_slice rep_sl byteT 1%Qp repData ∗
       ⌜has_encoding_GetReply repData rep ⌝
  }}}
    decodeGetReply (slice_val rep_sl)
  {{{
       (rep_ptr:loc) val_sl, RET #rep_ptr;
       rep_ptr ↦[GetReply.S :: "Err"] #rep.(GR_Err) ∗
       rep_ptr ↦[GetReply.S :: "Value"] (slice_val val_sl) ∗
       typed_slice.is_slice val_sl byteT 1%Qp rep.(GR_Value)
  }}}.
Proof.
Admitted.

End memkv_marshal_get_proof.
