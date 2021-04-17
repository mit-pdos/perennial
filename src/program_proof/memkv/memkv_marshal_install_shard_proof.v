From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.goose_lang Require Import ffi.grove_ffi.
From Perennial.program_proof Require Export marshal_proof common_proof.

(*
  Defines Coq request and reply types for shard server InstallShard RPC. Also defines
  has_encoding for InstallShard Request/Reply and provides WPs for {de|en}codeInstallShardRe{ply|quest}()
 *)

Section memkv_marshal_install_shard_proof.

Context `{!heapG Σ}.

Record InstallShardRequestC := mkInstallShardC {
  IR_CID : u64;
  IR_Seq : u64;
  IR_Sid : u64;
  IR_Kvs : gmap u64 (list u8)
}.

Definition own_InstallShardRequest args_ptr args : iProp Σ :=
  ∃ (kvs_ptr:loc) (mv:gmap u64 goose_lang.val),
  "HCID" ∷ args_ptr ↦[InstallShardRequest.S :: "CID"] #args.(IR_CID) ∗
  "HSeq" ∷ args_ptr ↦[InstallShardRequest.S :: "Seq"] #args.(IR_Seq) ∗
  "HKey" ∷ args_ptr ↦[InstallShardRequest.S :: "Sid"] #args.(IR_Sid) ∗
  "HKvs" ∷ args_ptr ↦[InstallShardRequest.S :: "Kvs"] #kvs_ptr ∗
  "HKvsMap" ∷ map.is_map kvs_ptr (mv, (slice_val Slice.nil)) ∗
  "%HseqPositive" ∷ ⌜int.Z args.(IR_Seq) > 0⌝ ∗
  "Hvals" ∷ ([∗ set] k ∈ (fin_to_set u64),
        ⌜shardOfC k ≠ args.(IR_Sid)⌝ ∨ (∃ vsl, ⌜default (slice_val Slice.nil) (mv !! k) = (slice_val vsl)⌝ ∗ typed_slice.is_slice vsl byteT (1%Qp) (default [] (args.(IR_Kvs) !! k))) )
.

(* Pre: "HownShard" ∷ own_shard γ.(kv_gn) sid m *)

Definition has_encoding_InstallShardRequest (data:list u8) (args:InstallShardRequestC) : iProp Σ.
Admitted.


End memkv_marshal_install_shard_proof.
