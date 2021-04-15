From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.goose_lang Require Import ffi.grove_ffi.
From Perennial.program_proof.lockservice Require Import rpc.
From Perennial.program_proof.memkv Require Import memkv_shard_proof.

Section memkv_shard_clerk_proof.

Context `{!heapG Σ, rpcG Σ GetReplyC}.

Definition own_MemKVShardClerk (ck:loc) γ : iProp Σ :=
  ∃ (cid seq:u64) (cl:loc) (host:string),
    "Hcid" ∷ ck ↦[MemKVShardClerk.S :: "cid"] #cid ∗
    "Hseq" ∷ ck ↦[MemKVShardClerk.S :: "seq"] #seq ∗
    "Hcl" ∷ ck ↦[MemKVShardClerk.S :: "cl"] #cl ∗
    "Hcrpc" ∷ RPCClient_own_ghost γ.(rpc_gn) cid seq ∗
    "Hcl_own" ∷ grove_ffi.RPCClient_own cl host ∗
    "#His_shard" ∷ is_shard_server host γ
.

Lemma wp_MemKVShardClerk__Get Eo Ei γ (ck:loc) (key:u64) (value_ptr:loc) Q :
  {{{
       (|={Eo,Ei}=> (∃ v, kvptsto γ.(kv_gn) key v ∗ (kvptsto γ.(kv_gn) key v ={Ei,Eo}=∗ Q v))) ∗
       own_MemKVShardClerk ck γ ∗
       (∃ dummy_sl, value_ptr ↦[slice.T byteT] (slice_val dummy_sl))
  }}}
    MemKVShardClerk__Get #ck #key #value_ptr
  {{{
       (e:u64), RET #e;
       own_MemKVShardClerk ck γ ∗ (
       ⌜e ≠ 0⌝ ∗
        (|={Eo,Ei}=> (∃ v, kvptsto γ.(kv_gn) key v ∗ (kvptsto γ.(kv_gn) key v ={Ei,Eo}=∗ Q v))) ∗
        (∃ some_sl, value_ptr ↦[slice.T byteT] (slice_val some_sl)) ∨

        ⌜e = 0⌝ ∗
              ∃ some_sl v, value_ptr ↦[slice.T byteT] (slice_val some_sl) ∗
                                     typed_slice.is_slice some_sl byteT 1%Qp v ∗
                                     Q v
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
    rewrite (zero_slice_val).
    iExists _; iFrame.
  }
  assert (int.nat seq + 1 = int.nat (word.add seq 1)) as Hoverflow.
  { simpl. admit. } (* FIXME: overflow guard *)
  iNamed "His_shard".
  iMod (make_request {| Req_CID:=_; Req_Seq:= _ |} (PreShardGet Eo Ei γ key Q) (PostShardGet Eo Ei γ key Q) with "His_rpc Hcrpc [Hkvptsto]") as "[Hcrpc HreqInv]".
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
    instantiate (1:= (Eo,Ei,Q,γreq)).
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
    { eapply has_encoding_GetRequest_inj; done. }

    iDestruct "Hreceipt" as "[Hbad|Hreceipt]".
    {
      iDestruct (client_stale_seqno with "Hbad Hcrpc") as "%Hbad".
      exfalso.
      simpl in Hbad.
      word.
    }
    iMod (get_request_post with "HreqInv Hreceipt Htok") as "Hpost".
    { done. }
    (* Doing get_request_post here so we can strip off a ▷ *)

    wp_pures.
    wp_loadField.
    iNamed "Hval".
    wp_store.
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
      iDestruct "Hpost" as "($&HQ)".
      iExists _; iFrame.
      iExists _; iFrame.
    }
  }
Admitted.

End memkv_shard_clerk_proof.
