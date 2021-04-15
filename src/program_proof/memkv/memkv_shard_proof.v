From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.goose_lang Require Import ffi.grove_ffi.
From Perennial.program_proof.lockservice Require Import rpc.
From Perennial.program_proof.memkv Require Import memkv_marshal_get_proof.

Section memkv_shard_proof.

Context `{!heapG Σ, rpcG Σ GetReplyC}.

Axiom kvptsto : gname → u64 → list u8 → iProp Σ.

Global Instance kvptst_tmlss γkv k v : Timeless (kvptsto γkv k v).
Admitted.

Definition uKV_GET := 2.

Record memkv_shard_names := {
 rpc_gn : rpc_names ;
 kv_gn : gname
}
.

Implicit Type γ : memkv_shard_names.

(* FIXME: lastReplyMap type *)
Definition own_MemKVShardServer (s:loc) γ : iProp Σ :=
  ∃ (lastReply_ptr lastSeq_ptr kvss_ptr peers_ptr:loc) (shardMap_sl:Slice.t) (kvs_sl:Slice.t)
    (lastReplyM:gmap u64 u64) (lastSeqM:gmap u64 u64) (nextCID:u64) (shardMapping:list bool) (kvs_ptrs:list loc),
  "HlastReply" ∷ s ↦[MemKVShardServer.S :: "lastReply"] #lastReply_ptr ∗
  "HlastReplyMap" ∷ is_map lastReply_ptr lastReplyM ∗
  "HlastSeq" ∷ s ↦[MemKVShardServer.S :: "lastSeq"] #lastSeq_ptr ∗
  "HlastSeqMap" ∷ is_map lastSeq_ptr lastSeqM ∗
  "HnextCID" ∷ s ↦[MemKVShardServer.S :: "nextCID"] #nextCID ∗
  "HshardMap" ∷ s ↦[MemKVShardServer.S :: "shardMap"] (slice_val shardMap_sl) ∗
  "HshardMap_sl" ∷ typed_slice.is_slice shardMap_sl boolT 1%Qp shardMapping ∗
  "Hkvss" ∷ s ↦[MemKVShardServer.S :: "kvss"] #kvss_ptr ∗
  "Hkvss_sl" ∷ typed_slice.is_slice kvs_sl (refT (mapT (slice.T (byteT)))) 1%Qp kvs_ptrs ∗
  "Hpeers" ∷ s ↦[MemKVShardServer.S :: "peers"] #peers_ptr
.

Definition memKVN := nroot .@ "memkv".

Definition is_MemKVShardServer (s:loc) γ : iProp Σ :=
  ∃ mu,
  "#Hmu" ∷ readonly (s ↦[MemKVShardServer.S :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock memKVN mu (own_MemKVShardServer s γ)
.

Definition PreShardGet Eo Ei γ key Q : iProp Σ :=
  |={Eo,Ei}=> (∃ v, kvptsto γ.(kv_gn) key v ∗ (kvptsto γ.(kv_gn) key v ={Ei,Eo}=∗ Q v))
.

Definition PostShardGet Eo Ei γ (key:u64) Q (rep:GetReplyC) : iProp Σ := ⌜rep.(GR_Err) ≠ 0⌝ ∗ (PreShardGet Eo Ei γ key Q) ∨
                                                        ⌜rep.(GR_Err) = 0⌝ ∗ (Q rep.(GR_Value)).

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
             ) (* post *)
.

Lemma wp_GetRPC (s args_ptr reply_ptr:loc) args γ Eo Ei γreq Q :
  is_MemKVShardServer s γ -∗
  {{{
       own_GetRequest args_ptr args ∗
       (∃ dummy_rep, own_GetReply reply_ptr dummy_rep) ∗
       is_RPCRequest γ.(rpc_gn) γreq (PreShardGet Eo Ei γ args.(GR_Key) Q)
                                (PostShardGet Eo Ei γ args.(GR_Key) Q)
                                {| Req_CID:=args.(GR_CID); Req_Seq:=args.(GR_Seq) |}
  }}}
    MemKVShardServer__GetRPC #s #args_ptr #reply_ptr
  {{{
       rep, RET #();
       own_GetReply reply_ptr rep ∗
       (RPCRequestStale γ.(rpc_gn) {| Req_CID:=args.(GR_CID); Req_Seq:=args.(GR_Seq) |} ∨
        RPCReplyReceipt γ.(rpc_gn) {| Req_CID:=args.(GR_CID); Req_Seq:=args.(GR_Seq) |} rep)
  }}}.
Proof.
  iIntros "#His_shard !#" (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(Hargs & Hrep & #HreqInv)".
  iNamed "Hargs". iNamed "Hrep".

  wp_lam.
  wp_pures.

  iNamed "His_shard".
  wp_loadField.
  wp_apply (acquire_spec with "[$HmuInv]").
  iIntros "[Hlocked Hown]".

  iNamed "Hown".

  wp_pures.
  wp_lam.
  wp_pures.

  wp_loadField. wp_loadField.
  wp_apply (wp_MapGet with "HlastSeqMap").
  iIntros (v ok) "[%HseqGet HlastSeqMap]".
  wp_pures.

  wp_apply (wp_and ok (int.Z args.(GR_Seq) ≤ int.Z v)%Z).
  { wp_pures. by destruct ok. }
  { iIntros "_". admit. (* tweak code to make less annoying *) }

  wp_if_destruct.
  { (* reply table *)
    wp_loadField.
    wp_loadField.
    admit.
  }
  {
    wp_loadField.
    wp_loadField.
    wp_loadField.
    wp_apply (wp_MapInsert with "HlastSeqMap").
    { done. }
    iIntros "HlastSeqMap".

    wp_pures.
    wp_loadField.
    wp_lam. (* TODO: hide this away *)
    wp_pures.
    wp_loadField.
    iDestruct (typed_slice.is_slice_small_acc with "HshardMap_sl") as "[HshardMap_sl HshardMap_sl_close]".
    wp_apply (wp_SliceGet with "[$HshardMap_sl]").
    {
      iFrame.
    }
  }
  wp_apply.
Admitted.

End memkv_shard_proof.
