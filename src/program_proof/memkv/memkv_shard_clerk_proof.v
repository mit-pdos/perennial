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

Context `{!heapG Σ, rpcG Σ GetReplyC}.

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

Record memkv_shard_names := {
 rpc_gn : rpc_names ;
 kv_gn : gname
}
.

Implicit Type γ : memkv_shard_names.

Axiom kvptsto : gname → u64 → list u8 → iProp Σ.

Definition uKV_GET := 2.
Definition is_shard_server host γ : iProp Σ :=
  "HgetSpec" ∷ handler_is (list u8 * rpc_request_names) host uKV_GET
             (λ x reqData, ∃ req, ⌜has_encoding_GetRequest reqData req⌝ ∗
                                   is_RPCRequest γ.(rpc_gn) x.2 (kvptsto γ.(kv_gn) req.(GR_Key) x.1) (λ rep,
                                                                                           ⌜rep.(GR_Value) = x.1⌝ ∗
                                                                                           kvptsto γ.(kv_gn) req.(GR_Key) x.1) {| Req_CID:=req.(GR_CID); Req_Seq:=req.(GR_Seq) |}
             ) (* pre *)
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

Definition own_MemKVShardClerk (ck:loc) γ : iProp Σ :=
  ∃ (cid seq:u64) (cl:loc) (host:string),
    "Hcid" ∷ ck ↦[MemKVShardClerk.S :: "cid"] #cid ∗
    "Hseq" ∷ ck ↦[MemKVShardClerk.S :: "seq"] #seq ∗
    "Hcl" ∷ ck ↦[MemKVShardClerk.S :: "cl"] #cl ∗
    "Hcrpc" ∷ RPCClient_own_ghost γ.(rpc_gn) cid seq ∗
    "Hcl_own" ∷ grove_ffi.RPCClient_own cl host ∗
    "#His_shard" ∷ is_shard_server host γ
.

Lemma wp_MemKVShardClerk__Get γ (ck:loc) (key:u64) (v:list u8) (value_ptr:loc) :
  {{{
       kvptsto γ.(kv_gn) key v ∗
       own_MemKVShardClerk ck γ ∗
       (∃ dummy_sl, value_ptr ↦[slice.T byteT] (slice_val dummy_sl))
  }}}
    MemKVShardClerk__Get #ck #key #value_ptr
  {{{
       (e:u64), RET #e; True
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(Hkvptsto & Hck & Hval)".
  iNamed "Hck".
  wp_lam.
  wp_pures.
  wp_loadField.
  wp_loadField.

  wp_pures.
  wp_loadField.
  wp_storeField.

  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rawRep) "HrawRep".
  wp_pures.

  iAssert (∃ rep_sl, rawRep ↦[slice.T byteT] (slice_val rep_sl) )%I with "[HrawRep]" as "HrawRep".
  {
    iExists _; iFrame.
    admit.
  }
  iAssert (True)%I with "[Hkvptsto]" as "_".
  { done. }
  wp_forBreak_cond.
  iNamed "HrawRep".
  wp_pures.

  wp_apply (wp_encodeGetRequest).
  iIntros (reqData req_sl) "[%HencReq Hreq_sl]".
  wp_loadField.

  unfold is_shard_server.
  wp_apply (wp_RPCClient__Call with "[$His_shard $Hreq_sl $HrawRep $Hcl_own]").
  {
    admit.
  }
  iIntros (b rep_sl' repData) "HcallPost".
  wp_if_destruct.
  {
    wp_pures.
    iModIntro.
    iLeft.
    iFrame.
    iDestruct "HcallPost" as "(HrawRep & $ & HcallPost)".
    iSplitL ""; first done.
    iExists _; iFrame "HrawRep".
  }
  {
    iModIntro.
    iRight.
    iSplitL ""; first done.
    wp_pures.
    iDestruct "HcallPost" as "(HrawRep & Hcl_own & Hreq_sl & Hrep_sl & [%Hbad | HcallPost ])".
    { exfalso. naive_solver. }
    iDestruct "HcallPost" as "(_ & >Hpost)".
    wp_load.
    iDestruct "Hpost" as (??) "[% %]".
    wp_apply (wp_decodeGetReply with "[$Hrep_sl]").
    { done. }
    iIntros (??) "(HrepErr & HrepValue & HrepValue_sl)".
    wp_pures.
    wp_loadField.
    iNamed "Hval".
    wp_store.
    wp_loadField.
    iApply "HΦ".
    done.
  }
Admitted.

End memkv_shard_clerk_proof.
