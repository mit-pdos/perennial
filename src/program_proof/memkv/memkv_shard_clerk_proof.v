From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.goose_lang Require Import ffi.grove_ffi.
From Perennial.program_proof.lockservice Require Import rpc.

Section memkv_shard_clerk_proof.

Record GetRequestC := mkGetRequestC {
  GR_CID : u64;
  GR_Seq : u64;
  GR_Key : u64
}.

Record GetReplyC := mkGetReplyC {
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

Global Instance kvptst_tmlss γkv k v : Timeless (kvptsto γkv k v).
Admitted.

Definition uKV_GET := 2.

Definition PreShardGet γ (x:list u8 * rpc_request_names) (reqData:list u8) : iProp Σ :=
  ∃ req, ⌜has_encoding_GetRequest reqData req⌝ ∗
          is_RPCRequest γ.(rpc_gn) x.2 (kvptsto γ.(kv_gn) req.(GR_Key) x.1)
                                   (λ rep, ⌜rep.(GR_Value) = x.1⌝ ∗ kvptsto γ.(kv_gn) req.(GR_Key) x.1) {| Req_CID:=req.(GR_CID); Req_Seq:=req.(GR_Seq) |}
.

Definition PostShardGet γ (key:u64) (v:list u8) (rep:GetReplyC) : iProp Σ := ⌜rep.(GR_Err) ≠ 0⌝ ∗ (kvptsto γ.(kv_gn) key v) ∨
                                                          ⌜rep.(GR_Err) = 0⌝ ∗ (kvptsto γ.(kv_gn) key v) ∗ ⌜rep.(GR_Value) = v⌝.

Definition is_shard_server host γ : iProp Σ :=
  "#His_rpc" ∷ is_RPCServer γ.(rpc_gn) ∗
  "#HgetSpec" ∷ handler_is (list u8 * rpc_request_names) host uKV_GET
             (λ x reqData, ∃ req, ⌜has_encoding_GetRequest reqData req⌝ ∗
                                   is_RPCRequest γ.(rpc_gn) x.2 (kvptsto γ.(kv_gn) req.(GR_Key) x.1)
                                                            (PostShardGet γ req.(GR_Key) x.1)
                                                            {| Req_CID:=req.(GR_CID); Req_Seq:=req.(GR_Seq) |}
             ) (* pre *)
             (λ x reqData repData, ∃ req rep, ⌜has_encoding_GetReply repData rep⌝ ∗
                                              ⌜has_encoding_GetRequest reqData req⌝ ∗
                                              (RPCRequestStale γ.(rpc_gn) {| Req_CID:=req.(GR_CID); Req_Seq:=req.(GR_Seq) |} ∨
                                              RPCReplyReceipt γ.(rpc_gn) {| Req_CID:=req.(GR_CID); Req_Seq:=req.(GR_Seq) |} rep)
             ) (* post *)
.

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
       (e:u64), RET #e;
       own_MemKVShardClerk ck γ ∗ (
       ⌜e ≠ 0⌝ ∗ (kvptsto γ.(kv_gn) key v) ∗ (∃ some_sl, value_ptr ↦[slice.T byteT] (slice_val some_sl)) ∨
                         ⌜e = 0⌝ ∗ (kvptsto γ.(kv_gn) key v) ∗ ∃ some_sl, value_ptr ↦[slice.T byteT] (slice_val some_sl) ∗
                                                                                    typed_slice.is_slice some_sl byteT 1%Qp v
        )
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
  assert (int.nat seq + 1 = int.nat (word.add seq 1)) as Hoverflow.
  { simpl. admit. } (* FIXME: overflow guard *)
  iNamed "His_shard".
  iMod (make_request {| Req_CID:=_; Req_Seq:= _ |} _ (PostShardGet γ key v) with "His_rpc Hcrpc [Hkvptsto]") as "[Hcrpc HreqInv]".
  { done. }
  { done. }
  { iNext. iAccu. }
  iDestruct "HreqInv" as (?) "[#HreqInv Htok]".

  wp_forBreak_cond.
  iNamed "HrawRep".
  wp_pures.

  wp_apply (wp_encodeGetRequest).
  iIntros (reqData req_sl) "[%HencReq Hreq_sl]".
  wp_loadField.

  unfold is_shard_server.
  wp_apply (wp_RPCClient__Call with "[$HgetSpec $Hreq_sl $HrawRep $Hcl_own]").
  {
    iModIntro.
    iModIntro.
    iExists (mkGetRequestC _ _ _).
    iSplitL ""; first done.
    instantiate (1:= (_,_)).
    simpl.
    iFrame "HreqInv".
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
    iDestruct "Hpost" as (??) "(% & % & Hreceipt)".
    wp_apply (wp_decodeGetReply with "[$Hrep_sl]").
    { done. }
    iIntros (??) "(HrepErr & HrepValue & HrepValue_sl)".
    replace (req) with ({| GR_CID := cid; GR_Seq := seq; GR_Key := key |}); last first.
    { (* encoding injectivity *) admit. }
    wp_pures.
    wp_loadField.
    iNamed "Hval".
    wp_store.
    iDestruct "Hreceipt" as "[Hbad|Hreceipt]".
    {
      iDestruct (client_stale_seqno with "Hbad Hcrpc") as "%Hbad".
      exfalso.
      simpl in Hbad.
      word.
    }
    iMod (get_request_post with "HreqInv Hreceipt Htok") as ">Hpost".
    { done. }
    wp_loadField.
    iApply "HΦ".
    iSplitL "Hcl_own Hcrpc Hcl Hcid Hseq".
    { iExists _, _, _, _. iFrame "#∗". }
    iDestruct "Hpost" as "[Hpost|Hpost]".
    {
      iLeft. iDestruct "Hpost" as "[$ $]".
      iExists _; iFrame.
    }
    {
      iRight.
      iDestruct "Hpost" as "($&$&->)".
      iExists _; iFrame.
    }
  }
Admitted.

End memkv_shard_clerk_proof.
