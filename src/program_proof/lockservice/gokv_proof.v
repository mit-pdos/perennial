From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.gokv Require Import goosekv.
From Perennial.goose_lang Require Import ffi.grove_ffi.
From Perennial.algebra Require Import mlist auth_map.
From iris.algebra Require Import mono_nat.
From Perennial.program_proof.lockservice Require Import rpc rpc_proof aof_proof.
From Perennial.program_proof Require Import marshal_proof.

Section gokv_proof.
Context `{!heapG Σ}.
Context `{!filesysG Σ}.
Context `{!rpcG Σ u64}.
Context `{!mapG Σ u64 u64}.
Context `{!aofG Σ}.

Record gokv_names := {
  kvs_gn : gname ;
  aof_gn : aof_vol_names ;
  rpc_gn : rpc_names ;
}.

Implicit Types γ : gokv_names.

Definition goKVN := nroot .@ "gokv".

Record GoKVServerC :=
{
  kvsM : gmap u64 u64;
  lastReplyM : gmap u64 u64;
  lastSeqM : gmap u64 u64;
}.

Definition has_gokv_encoding (data:list u8) (gkv:GoKVServerC) : Prop.
Admitted.

Lemma has_gokv_encoding_injective (data:list u8) (gkv1 gkv2:GoKVServerC) :
  has_gokv_encoding data gkv1 →
  has_gokv_encoding data gkv2 →
  gkv1 = gkv2.
Admitted.

Definition gokv_aof_ctx γrpc γkv (data:list u8) : iProp Σ :=
  ∃ gkv,
    "%Henc" ∷ ⌜has_gokv_encoding data gkv⌝ ∗
    "Hghost" ∷ map_ctx γkv 1 gkv.(kvsM) ∗
    "Hsrpc" ∷ RPCServer_own γrpc gkv.(lastSeqM) gkv.(lastReplyM)
.

Definition gokv_inv s γ : iProp Σ :=
  ∃ (kvs_ptr lastSeq_ptr aof_ptr lastReply_ptr:loc) gkv,
   "HlastSeqOwn" ∷ s ↦[GoKVServer.S :: "lastSeq"] #lastSeq_ptr ∗
   "HlastReplyOwn" ∷ s ↦[GoKVServer.S :: "lastReply"] #lastReply_ptr ∗
   "HlastSeqMap" ∷ is_map (lastSeq_ptr) gkv.(lastSeqM) ∗
   "HlastReplyMap" ∷ is_map (lastReply_ptr) gkv.(lastReplyM) ∗
   "HkvsOwn" ∷ s ↦[GoKVServer.S :: "kvs"] #kvs_ptr ∗
   "HkvsMap" ∷ is_map (kvs_ptr) gkv.(kvsM) ∗
   "#HaofOwn" ∷ readonly (s ↦[GoKVServer.S :: "opLog"] #aof_ptr) ∗
   "Haof_log" ∷ (∃ data, aof_log_own γ.(aof_gn) data ∗ ⌜has_gokv_encoding data gkv⌝) ∗
   "#His_aof" ∷ is_aof aof_ptr γ.(aof_gn) (gokv_aof_ctx γ.(rpc_gn) γ.(kvs_gn))
.

Definition is_gokvserver s γ : iProp Σ :=
  ∃ mu,
  "#Hmu" ∷ readonly (s ↦[GoKVServer.S :: "mu"] mu) ∗
  "#Hmu_inv" ∷ is_lock goKVN mu (gokv_inv s γ)
.

Lemma wp_CheckReplyTable (reply_ptr:loc) (req:RPCRequestID) (reply:Reply64) (lastSeq_ptr lastReply_ptr:loc) lastSeqM lastReplyM γrpc :
{{{
     "%" ∷ ⌜int.nat req.(Req_Seq) > 0⌝
    ∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM
    ∗ "HlastReplyMap" ∷ is_map (lastReply_ptr) lastReplyM
    ∗ "Hreply" ∷ own_reply reply_ptr reply
}}}
    lockservice.CheckReplyTable #lastSeq_ptr #lastReply_ptr #req.(Req_CID) #req.(Req_Seq) #reply_ptr
{{{
     (b:bool) (reply':Reply64), RET #b;
    "Hreply" ∷ own_reply reply_ptr reply' ∗ (
    "Hcases" ∷ ("%" ∷ ⌜b = false⌝ ∗
    "%" ∷ ⌜(int.Z req.(Req_Seq) > int.Z (map_get lastSeqM req.(Req_CID)).1)%Z⌝ ∗
    "%" ∷ ⌜reply'.(Rep_Stale) = false⌝ ∗
    "HlastSeqMap" ∷ is_map (lastSeq_ptr) (<[req.(Req_CID):=req.(Req_Seq)]>lastSeqM))
    ∨
    "%" ∷ ⌜b = true⌝ ∗
    "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM ∗
    (⌜reply'.(Rep_Stale) = true⌝ ∗ (RPCServer_own γrpc lastSeqM lastReplyM -∗ RPCRequestStale γrpc req)
      ∨ (RPCServer_own γrpc lastSeqM lastReplyM -∗ RPCReplyReceipt γrpc req reply'.(Rep_Ret)))
    ) ∗
    "HlastReplyMap" ∷ is_map (lastReply_ptr) lastReplyM
}}}
.
Admitted.

Lemma wp_encodeReq_put req_ptr rid args :
  {{{
       read_request req_ptr rid args
  }}}
    encodeReq #0 #req_ptr
  {{{
       sl (data:list u8), RET (slice_val sl);
       typed_slice.is_slice sl byteT 1 data ∗
       ⌜has_encoding data [EncUInt64 0; EncUInt64 rid.(Req_CID); EncUInt64 rid.(Req_Seq) ; EncUInt64 args.(U64_1) ; EncUInt64 args.(U64_2) ]⌝
  }}}
.
Proof.
Admitted.

Lemma wp_GoKVServer__Put (s:loc) va γ :
is_gokvserver s γ -∗
  {{{
       True
  }}}
    GoKVServer__Put #s
  {{{ (f:goose_lang.val), RET f;
        ∀ args req, is_rpcHandler f γ.(rpc_gn) args req (args.(U64_1) [[γ.(kvs_gn)]]↦ va) (λ v, ⌜v = va⌝ ∗ args.(U64_1) [[γ.(kvs_gn)]]↦ v)
  }}}.
Proof.
  iIntros "#Hls".
  iIntros (Φ) "!# _ Hpost".
  wp_lam.
  wp_pures.
  iApply "Hpost".
  iIntros (args req).
  clear Φ.
  iIntros (???? Φ) "!# Hpre HΦ".
  iNamed "Hls". wp_pures.
  iNamed "Hpre".

  wp_loadField.
  wp_apply (acquire_spec with "Hmu_inv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".

  iNamed "Hargs".
  wp_pures.
  repeat wp_loadField.

  wp_apply (wp_CheckReplyTable with "[$HlastSeqMap $Hreply $HlastReplyMap]").
  { iDestruct "HSeqPositive" as %?. iPureIntro. word. }
  iIntros (b reply').
  iIntros "HcheckPost".
  wp_if_destruct.
  {
    iNamed "HcheckPost".
    iDestruct "HcheckPost" as "[[Hbad|HcheckPost] HlastReplyMap]".
    { iNamed "Hbad". iNamed "Hcases". done. }
    iNamed "HcheckPost".
    wp_pures.
    wp_apply (wp_encodeReq_put with "[$]").
    iIntros (req_sl req_data) "[Hreq_sl %Hreq_enc]".
    wp_loadField.
    iDestruct "Haof_log" as (data) "[Haof_log %Hdata_enc]".
    iDestruct "HcheckPost" as "[Hcheck|Hcheck]".
    {
      iDestruct "Hcheck" as "(%Hstale & Hwand)".
      wp_apply (wp_AppendOnlyFile__Append with "His_aof [$Hreq_sl $Haof_log Hwand]").
      {
        iNamed 1.
        replace (gkv0) with (gkv); last first.
        { apply (has_gokv_encoding_injective data); done. }
        iDestruct ("Hwand" with "Hsrpc") as "#Hstale".
        instantiate (1:=RPCRequestStale γ.(rpc_gn) req).
        iFrame "#".
        iExists gkv.
        iFrame.
        iPureIntro.
        (* Pure fact about adding operation to log *)
        admit.
      }
      iIntros (l) "[Haof_log Hwand]".
      wp_pures.

      wp_loadField.
      wp_apply (release_spec with "[- HΦ Hwand Hreply]").
      {
        iFrame "#∗".
        iNext. iExists _, _, _, _, _. iFrame.
        iFrame "#∗".
        iExists _; iFrame.
        (* same pure fact as above *)
        admit.
      }
      wp_pures.
      wp_loadField.
      wp_apply (wp_AppendOnlyFile__WaitAppend with "His_aof").
      iIntros "Haof_lb".
      iMod ("Hwand" with "Haof_lb") as ">Hstale".
      wp_pures.
      iApply "HΦ".
      iExists _; iFrame "∗#".
      iLeft. iFrame. done.
    } (* end of stale case *)
    admit.
  }
  admit.
Admitted.
