From Perennial.program_proof Require Import dist_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof Require Export marshal_proof memkv.common_proof.

(*
  Defines Coq request and reply types for shard server InstallShard RPC. Also defines
  has_encoding for InstallShard Request/Reply and provides WPs for {de|en}codeInstallShardRe{ply|quest}()
 *)

Section memkv_marshal_install_shard_proof.

Record InstallShardRequestC := mkInstallShardC {
  IR_CID : u64;
  IR_Seq : u64;
  IR_Sid : u64;
  IR_Kvs : gmap u64 (list u8)
}.

Definition has_encoding_InstallShardRequest (data:list u8) (args:InstallShardRequestC) : Prop.
Admitted.

Context `{!heapG Σ}.

Definition own_InstallShardRequest args_ptr args : iProp Σ :=
  ∃ (kvs_ptr:loc) (mv:gmap u64 goose_lang.val),
  "HCID" ∷ args_ptr ↦[InstallShardRequest :: "CID"] #args.(IR_CID) ∗
  "HSeq" ∷ args_ptr ↦[InstallShardRequest :: "Seq"] #args.(IR_Seq) ∗
  "HKey" ∷ args_ptr ↦[InstallShardRequest :: "Sid"] #args.(IR_Sid) ∗
  "HKvs" ∷ args_ptr ↦[InstallShardRequest :: "Kvs"] #kvs_ptr ∗
  "HKvsMap" ∷ map.is_map kvs_ptr 1 (mv, (slice_val Slice.nil)) ∗
  "%HseqPositive" ∷ ⌜int.Z args.(IR_Seq) > 0⌝ ∗
  "Hvals" ∷ ([∗ set] k ∈ (fin_to_set u64),
        ⌜shardOfC k ≠ args.(IR_Sid)⌝ ∨ (∃ q vsl, ⌜default (slice_val Slice.nil) (mv !! k) = (slice_val vsl)⌝ ∗ typed_slice.is_slice_small vsl byteT q (default [] (args.(IR_Kvs) !! k))) )
.

(* Pre: "HownShard" ∷ own_shard γ.(kv_gn) sid m *)

Lemma wp_encodeInstallShardRequest args_ptr args :
  {{{
       own_InstallShardRequest args_ptr args
  }}}
    encodeInstallShardRequest #args_ptr
  {{{
       (reqData:list u8) req_sl, RET (slice_val req_sl); ⌜has_encoding_InstallShardRequest reqData args⌝ ∗
                                               typed_slice.is_slice req_sl byteT 1%Qp reqData ∗
                                               own_InstallShardRequest args_ptr args
  }}}.
Proof.
Admitted.

Lemma wp_decodeInstallShardRequest args args_sl argsData :
  {{{
       typed_slice.is_slice args_sl byteT 1%Qp argsData ∗
       ⌜has_encoding_InstallShardRequest argsData args ⌝
  }}}
    decodeInstallShardRequest (slice_val args_sl)
  {{{
       (args_ptr:loc), RET #args_ptr;
       own_InstallShardRequest args_ptr args
  }}}.
Proof.
Admitted.

End memkv_marshal_install_shard_proof.
