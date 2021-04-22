From Perennial.program_proof Require Import dist_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof Require Export marshal_proof memkv.common_proof.

(*
  Defines Coq request type for shard server MoveShard RPC. Also defines
  has_encoding for MoveShard Requestand provides WPs for
  {de|en}codeInstallShardRequest()
 *)

Section memkv_marshal_move_shard_proof.

Record MoveShardRequestC := mkMoveShardRequestC {
  MR_CID : u64;
  MR_Seq : u64;
  MR_Sid : u64;
  MR_Dst : u64
}.

Definition has_encoding_MoveShardRequest (data:list u8) (args:MoveShardRequestC) : Prop.
Admitted.

Context `{!heapG Σ}.

Definition own_MoveShardRequest args_ptr args : iProp Σ :=
  "HCID" ∷ args_ptr ↦[MoveShardRequest :: "CID"] #args.(MR_CID) ∗
  "HSeq" ∷ args_ptr ↦[MoveShardRequest :: "Seq"] #args.(MR_Seq) ∗
  "HSid" ∷ args_ptr ↦[MoveShardRequest :: "Sid"] #args.(MR_Sid) ∗
  "HDst" ∷ args_ptr ↦[MoveShardRequest :: "Dst"] #args.(MR_Dst) ∗
  "%HseqPositive" ∷ ⌜int.Z args.(MR_Seq) > 0⌝
.

(* Pre: "HownShard" ∷ own_shard γ.(kv_gn) sid m *)

Lemma wp_encodeMoveShardRequest args_ptr args :
  {{{
       own_MoveShardRequest args_ptr args
  }}}
    encodeMoveShardRequest #args_ptr
  {{{
       (reqData:list u8) req_sl, RET (slice_val req_sl); ⌜has_encoding_MoveShardRequest reqData args⌝ ∗
                                               typed_slice.is_slice req_sl byteT 1%Qp reqData ∗
                                               own_MoveShardRequest args_ptr args
  }}}.
Proof.
Admitted.

Lemma wp_decodeMoveShardRequest args args_sl argsData :
  {{{
       typed_slice.is_slice args_sl byteT 1%Qp argsData ∗
       ⌜has_encoding_MoveShardRequest argsData args ⌝
  }}}
    decodeMoveShardRequest (slice_val args_sl)
  {{{
       (args_ptr:loc), RET #args_ptr;
       own_MoveShardRequest args_ptr args
  }}}.
Proof.
Admitted.

End memkv_marshal_move_shard_proof.
