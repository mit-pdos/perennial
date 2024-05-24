From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof Require Export marshal_proof memkv.common_proof.

(*
  Defines Coq request type for shard server MoveShard RPC. Also defines
  has_encoding for MoveShard Requestand provides WPs for
  {de|en}codeInstallShardRequest()
 *)

Section memkv_marshal_move_shard_proof.

Record MoveShardRequestC := mkMoveShardRequestC {
  MR_Sid : u64;
  MR_Dst : u64
}.

Definition has_encoding_MoveShardRequest (data:list u8) (args:MoveShardRequestC) : Prop :=
  has_encoding data [ EncUInt64 args.(MR_Sid) ; EncUInt64 args.(MR_Dst) ].

Context `{!heapGS Σ}.

Definition own_MoveShardRequest args_ptr args : iProp Σ :=
  "HSid" ∷ args_ptr ↦[MoveShardRequest :: "Sid"] #args.(MR_Sid) ∗
  "HDst" ∷ args_ptr ↦[MoveShardRequest :: "Dst"] #args.(MR_Dst)
.

Lemma wp_encodeMoveShardRequest args_ptr args :
  {{{
       own_MoveShardRequest args_ptr args
  }}}
    encodeMoveShardRequest #args_ptr
  {{{
     (reqData:list u8) req_sl, RET (slice_val req_sl);
       ⌜has_encoding_MoveShardRequest reqData args⌝ ∗
        typed_slice.own_slice req_sl byteT (DfracOwn 1) reqData ∗
        own_MoveShardRequest args_ptr args
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
  rewrite /has_encoding_MoveShardRequest.
  done.
Qed.

Lemma wp_decodeMoveShardRequest args args_sl argsData :
  {{{
       typed_slice.own_slice_small args_sl byteT (DfracOwn 1) argsData ∗
       ⌜has_encoding_MoveShardRequest argsData args ⌝
  }}}
    decodeMoveShardRequest (slice_val args_sl)
  {{{
       (args_ptr:loc), RET #args_ptr;
       own_MoveShardRequest args_ptr args
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

  wp_apply (wp_Dec__GetInt with "[$Hdec]").
  iIntros "Hdec".
  wp_storeField.

  iApply "HΦ".
  iModIntro.
  iFrame.
Qed.

End memkv_marshal_move_shard_proof.
