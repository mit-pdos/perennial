From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.goose_lang Require Import ffi.grove_ffi.
From Perennial.program_proof.lockservice Require Import rpc.
From Perennial.program_proof.memkv Require Export common_proof.
From Perennial.program_proof.memkv Require Export memkv_marshal_get_proof memkv_marshal_install_shard_proof memkv_marshal_getcid_proof memkv_marshal_move_shard_proof.

Section memkv_shard_definitions.

Context `{!heapG Σ, rpcG Σ GetReplyC}.

Axiom kvptsto : gname → u64 → list u8 → iProp Σ.

Global Instance kvptst_tmlss γkv k v : Timeless (kvptsto γkv k v).
Admitted.

Definition uKV_FRESHCID := 0.
Definition uKV_GET := 2.
Definition uKV_INS_SHARD := 3.

Record memkv_shard_names := {
 rpc_gn : rpc_names ;
 kv_gn : gname
}
.

Implicit Type γ : memkv_shard_names.

Definition PreShardGet Eo Ei γ key Q : iProp Σ :=
  |={Eo,Ei}=> (∃ v, kvptsto γ.(kv_gn) key v ∗ (kvptsto γ.(kv_gn) key v ={Ei,Eo}=∗ Q v))
.

Definition PostShardGet Eo Ei γ (key:u64) Q (rep:GetReplyC) : iProp Σ := ⌜rep.(GR_Err) ≠ 0⌝ ∗ (PreShardGet Eo Ei γ key Q) ∨
                                                        ⌜rep.(GR_Err) = 0⌝ ∗ (Q rep.(GR_Value)).

Definition own_shard γkv sid (m:gmap u64 (list u8)) : iProp Σ :=
  [∗ set] k ∈ (fin_to_set u64), ⌜shardOfC k ≠ sid⌝ ∨
                                kvptsto γkv k (default [] (m !! k))
.

Definition is_shard_server host γ : iProp Σ :=
  "#His_rpc" ∷ is_RPCServer γ.(rpc_gn) ∗
  "#HgetSpec" ∷ handler_is (coPset * coPset * (list u8 → iProp Σ) * rpc_request_names) host uKV_GET
             (λ x reqData, ∃ req, ⌜has_encoding_GetRequest reqData req⌝ ∗
                                   is_RPCRequest γ.(rpc_gn) x.2 (PreShardGet x.1.1.1 x.1.1.2 γ req.(GR_Key) x.1.2)
                                                            (PostShardGet x.1.1.1 x.1.1.2 γ req.(GR_Key) x.1.2)
                                                            {| Req_CID:=req.(GR_CID); Req_Seq:=req.(GR_Seq) |}
             ) (* pre *)
             (λ x reqData repData, ∃ req rep, ⌜has_encoding_GetReply repData rep⌝ ∗
                                              ⌜has_encoding_GetRequest reqData req⌝ ∗
                                              (RPCRequestStale γ.(rpc_gn) {| Req_CID:=req.(GR_CID); Req_Seq:=req.(GR_Seq) |} ∨
                                              RPCReplyReceipt γ.(rpc_gn) {| Req_CID:=req.(GR_CID); Req_Seq:=req.(GR_Seq) |} rep)
             ) (* post *) ∗

  "#HmoveSpec" ∷ handler_is (memkv_shard_names) host uKV_INS_SHARD
             (λ x reqData, ∃ args, ⌜has_encoding_MoveShardRequest reqData args⌝ ∗
                                  ⌜int.nat args.(MR_Sid) < uNSHARD⌝ ∗
                                  (* is_shard_server args.(MR_Dst) x *)
                                                                True
             ) (* pre *)
             (λ x reqData repData, True
             ) (* post *) ∗

  "#HinstallSpec" ∷ handler_is (rpc_request_names) host uKV_INS_SHARD
             (λ x reqData, ∃ args, ⌜has_encoding_InstallShardRequest reqData args⌝ ∗
                                  ⌜int.nat args.(IR_Sid) < uNSHARD⌝ ∗
                                  is_RPCRequest γ.(rpc_gn) x (own_shard γ.(kv_gn) args.(IR_Sid) args.(IR_Kvs))
                                                            (λ _, True)
                                                            {| Req_CID:=args.(IR_CID); Req_Seq:=args.(IR_Seq) |}
             ) (* pre *)
             (λ x reqData repData, True
             ) (* post *) ∗

  "#HfreshSpec" ∷ handler_is unit host uKV_FRESHCID
             (λ x reqData, True
             ) (* pre *)
             (λ x reqData repData, ∃ cid, ⌜has_encoding_CID repData cid⌝ ∗
              RPCClient_own_ghost γ.(rpc_gn) cid 1
             ) (* post *)
.

Definition own_MemKVShardClerk (ck:loc) γ : iProp Σ :=
  ∃ (cid seq:u64) (cl:loc) (host:u64),
    "Hcid" ∷ ck ↦[MemKVShardClerk.S :: "cid"] #cid ∗
    "Hseq" ∷ ck ↦[MemKVShardClerk.S :: "seq"] #seq ∗
    "Hcl" ∷ ck ↦[MemKVShardClerk.S :: "cl"] #cl ∗
    "Hcrpc" ∷ RPCClient_own_ghost γ.(rpc_gn) cid seq ∗
    "Hcl_own" ∷ grove_ffi.RPCClient_own cl host ∗
    "#His_shard" ∷ is_shard_server host γ ∗
    "%HseqPostitive" ∷ ⌜0%Z < int.Z seq⌝%Z
.

Definition memKVN := nroot .@ "memkv".

Definition own_MemKVShardServer (s:loc) γ : iProp Σ :=
  ∃ (lastReply_ptr lastSeq_ptr peers_ptr:loc) (kvss_sl shardMap_sl:Slice.t)
    (lastReplyM:gmap u64 GetReplyC) (lastReplyMV:gmap u64 goose_lang.val) (lastSeqM:gmap u64 u64) (nextCID:u64) (shardMapping:list bool) (kvs_ptrs:list loc)
    (peersM:gmap u64 loc),
  "HlastReply" ∷ s ↦[MemKVShardServer.S :: "lastReply"] #lastReply_ptr ∗
  "HlastReplyMap" ∷ map.is_map lastReply_ptr (lastReplyMV, #0) ∗ (* TODO: default *)
  "%HlastReplyMVdom" ∷ ⌜dom (gset u64) lastReplyMV = dom (gset u64) lastSeqM⌝ ∗
  "HlastReply_structs" ∷ ([∗ map] k ↦ v;rep ∈ lastReplyMV ; lastReplyM, (∃ val_sl q, ⌜v = (#rep.(GR_Err), (slice_val val_sl, #()))%V⌝ ∗ typed_slice.is_slice_small val_sl byteT q rep.(GR_Value))) ∗
  "HlastSeq" ∷ s ↦[MemKVShardServer.S :: "lastSeq"] #lastSeq_ptr ∗
  "HlastSeqMap" ∷ is_map lastSeq_ptr lastSeqM ∗
  "HnextCID" ∷ s ↦[MemKVShardServer.S :: "nextCID"] #nextCID ∗
  "HshardMap" ∷ s ↦[MemKVShardServer.S :: "shardMap"] (slice_val shardMap_sl) ∗
  "HshardMap_sl" ∷ typed_slice.is_slice shardMap_sl boolT 1%Qp shardMapping ∗
  "Hkvss" ∷ s ↦[MemKVShardServer.S :: "kvss"] (slice_val kvss_sl) ∗
  "Hkvss_sl" ∷ slice.is_slice kvss_sl (mapT (slice.T byteT)) 1%Qp (fmap (λ x:loc, #x) kvs_ptrs) ∗
  "Hpeers" ∷ s ↦[MemKVShardServer.S :: "peers"] #peers_ptr ∗
  "Hrpc" ∷ RPCServer_own_ghost γ.(rpc_gn) lastSeqM lastReplyM ∗
  "%HshardMapLength" ∷ ⌜length shardMapping = uNSHARD⌝ ∗
  "%HkvssLength" ∷ ⌜length kvs_ptrs = uNSHARD⌝ ∗
  "HownShards" ∷ ([∗ set] sid ∈ (fin_to_set u64),
                  ⌜(shardMapping !! (int.nat sid)) ≠ Some true⌝ ∨
                  (∃ (kvs_ptr:loc) (m:gmap u64 (list u8)) (mv:gmap u64 goose_lang.val),
                      own_shard γ.(kv_gn) sid m ∗ (* own shard *)
                      ⌜kvs_ptrs !! (int.nat sid) = Some kvs_ptr⌝ ∗
                      map.is_map kvs_ptr (mv, (slice_val Slice.nil)) ∗
                      ([∗ set] k ∈ (fin_to_set u64),
                       ⌜shardOfC k ≠ sid⌝ ∨ (∃ vsl, ⌜default (slice_val Slice.nil) (mv !! k) = (slice_val vsl)⌝ ∗ typed_slice.is_slice vsl byteT (1%Qp) (default [] (m !! k))) )
                  )
                 ) ∗
  "HpeersMap" ∷ is_map (V:=loc) peers_ptr peersM ∗
  "HpeerClerks" ∷ ([∗ map] k ↦ ck ∈ peersM, (∃ γsh, own_MemKVShardClerk ck γsh ∗ ⌜γsh.(kv_gn) = γ.(kv_gn)⌝)) ∗
  "Hcids" ∷ [∗ set] cid ∈ (fin_to_set u64), ⌜int.Z cid < int.Z nextCID⌝%Z ∨ (RPCClient_own_ghost γ.(rpc_gn) cid 1)
.

Definition is_MemKVShardServer (s:loc) γ : iProp Σ :=
  ∃ mu,
  "#His_srv" ∷ is_RPCServer γ.(rpc_gn) ∗
  "#Hmu" ∷ readonly (s ↦[MemKVShardServer.S :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock memKVN mu (own_MemKVShardServer s γ)
.

End memkv_shard_definitions.
