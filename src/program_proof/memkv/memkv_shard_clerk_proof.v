From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.goose_lang Require Import ffi.grove_ffi.
From Perennial.program_proof.lockservice Require Import rpc.

Section memkv_shard_clerk_proof.

Record GetRequestC := {
  GR_CID : u64;
  GR_Seq : u64;
  GR_Key : u64
}.

Record GetReplyC := {
  GR_Err : u64;
  GR_Value : list u8
}.

Axiom has_encoding_GetRequest : (list u8) → GetRequestC → Prop.
Axiom has_encoding_GetReply : (list u8) → GetReplyC → Prop.

Context `{!heapG Σ, rpcG Σ GetReply}.


Definition uKV_GET := 3.
Definition is_shard_server host : iProp Σ :=
  "HgetSpec" ∷ handler_is (list u8) host uKV_GET
             (λ x reqData, True ) (* pre *)
             (λ x reqData repData, ∃ req rep, ⌜has_encoding_GetReply repData rep⌝ ∗
                                              ⌜has_encoding_GetRequest reqData req⌝
                                              (* RPCReplyReceipt γ.(rpc_gn) req.CID req.Seq *)
             ) (* post *)
.

(*
Escrow setup:

server_proc (cid,seq)
server_tok (cid,seq)
client_tok (cid,seq)

inv (server_proc id ∨ kvptsto k v)
inv (RPCFreshReply id ∨ server_done id ∗ RPCReplyReceipt id v ∗ kvptsto k v)

□(server_start id ={⊤}=∗ PreCond)
□(∀ rep, server_tok id -∗ PostCond rep ={⊤}=∗ RPCReplyReceipt rep)

Meanwhile, client keeps a fupd
(RPCReplyReceipt rep ={⊤}=∗ PostCond rep)

*)

Record memkv_shard_names := {
 rpc_gn : rpc_names ;
 kv_gn : gname
}
.

Implicit Type γ : memkv_shard_names.

Definition own_MemKVShardClerk (ck:loc) γ : iProp Σ :=
  ∃ cid seq,
    RPCClient_own_ghost γ.(rpc_gn) cid seq
.

Axiom kvptsto : gname → u64 → list u8 → iProp Σ.

Lemma wp_MemKVShardClerk__Get γ (ck:loc) (key:u64) (v:list u8) (value_ptr:loc) :
  {{{
       kvptsto γ.(kv_gn) key v ∗
       own_MemKVShardClerk ck γ
  }}}
    MemKVShardClerk__Get #ck #key #value_ptr
  {{{
       (e:u64), RET #e; True
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  wp_lam.
  wp_pures.
Admitted.

End memkv_shard_clerk_proof.
