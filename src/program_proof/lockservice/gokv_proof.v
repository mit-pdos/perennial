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
mkGoKVServerC {
  kvsM : gmap u64 u64;
  lastReplyM : gmap u64 u64;
  lastSeqM : gmap u64 u64;
}.

Record KVReq := mkKVReq {
  optype : u64 ; (* 0 = put, 1 = get *)
  rid : RPCRequestID ;
  args : RPCValsC ;
}.

Definition gokv_core s gkv : iProp Σ :=
  ∃ (kvs_ptr lastSeq_ptr aof_ptr lastReply_ptr:loc),
   "HlastSeqOwn" ∷ s ↦[GoKVServer.S :: "lastSeq"] #lastSeq_ptr ∗
   "HlastReplyOwn" ∷ s ↦[GoKVServer.S :: "lastReply"] #lastReply_ptr ∗
   "HlastSeqMap" ∷ is_map (lastSeq_ptr) gkv.(lastSeqM) ∗
   "HlastReplyMap" ∷ is_map (lastReply_ptr) gkv.(lastReplyM) ∗
   "HkvsOwn" ∷ s ↦[GoKVServer.S :: "kvs"] #kvs_ptr ∗
   "HkvsMap" ∷ is_map (kvs_ptr) gkv.(kvsM)
.

Definition apply_op_req (gkv:GoKVServerC) (rid:RPCRequestID) (args:RPCValsC) (gkv':GoKVServerC) : iProp Σ :=
  ∀ s req_ptr reply_ptr reply,
  {{{
       read_request req_ptr rid args ∗
       own_reply reply_ptr reply ∗
       gokv_core s gkv
  }}}
    GoKVServer__put_inner #s #req_ptr #reply_ptr
  {{{
       reply', RET #(); gokv_core s gkv' ∗
       own_reply reply_ptr reply'
  }}}.

Definition unknown (data:list u8) (gkv:GoKVServerC) : iProp Σ.
Admitted.

Definition has_gokv_encoding (data:list u8) (gkv:GoKVServerC) : iProp Σ :=
  ∃ (ops:list KVReq),
    □ (unknown data gkv).

Lemma has_gokv_encoding_injective (data:list u8) (gkv1 gkv2:GoKVServerC) :
  has_gokv_encoding data gkv1 -∗
  has_gokv_encoding data gkv2 -∗
  ⌜gkv1 = gkv2⌝.
Admitted.

Definition has_req_encoding_put data rid args :=
has_encoding data [EncUInt64 0; EncUInt64 rid.(Req_CID); EncUInt64 rid.(Req_Seq) ; EncUInt64 args.(U64_1) ; EncUInt64 args.(U64_2) ].

Lemma has_gokv_encoding_append (data req_data:list u8) (gkv gkv':GoKVServerC) :
  ∀ rid args,
    ⌜has_req_encoding_put req_data rid args⌝ -∗
     has_gokv_encoding data gkv -∗
     apply_op_req gkv rid args gkv' -∗
     has_gokv_encoding (data ++ req_data) gkv'.
Admitted.

Definition gokv_aof_ctx γrpc γkv (data:list u8) : iProp Σ :=
  ∃ gkv,
    "#Henc" ∷ has_gokv_encoding data gkv ∗
    "Hghost" ∷ map_ctx γkv 1 gkv.(kvsM) ∗
    "Hsrpc" ∷ RPCServer_own γrpc gkv.(lastSeqM) gkv.(lastReplyM)
.

Definition gokv_inv s γ : iProp Σ :=
  ∃ (aof_ptr:loc) gkv,
   "Hcore" ∷ gokv_core s gkv ∗
   "#HaofOwn" ∷ readonly (s ↦[GoKVServer.S :: "opLog"] #aof_ptr) ∗
   "Haof_log" ∷ (∃ data, aof_log_own γ.(aof_gn) data ∗ has_gokv_encoding data gkv) ∗
   "#His_aof" ∷ is_aof aof_ptr γ.(aof_gn) (gokv_aof_ctx γ.(rpc_gn) γ.(kvs_gn))
.

Definition is_gokvserver s γ : iProp Σ :=
  ∃ mu,
  "#Hmu" ∷ readonly (s ↦[GoKVServer.S :: "mu"] mu) ∗
  "#Hmu_inv" ∷ is_lock goKVN mu (gokv_inv s γ)
.

Definition reply_res γrpc req (reply:@RPCReply u64) : iProp Σ :=
  ⌜reply.(Rep_Stale) = true⌝ ∗ RPCRequestStale γrpc req
  ∨ RPCReplyReceipt γrpc req reply.(Rep_Ret)
.

Lemma wp_CheckReplyTable :
  ∀ lastSeqM lastReplyM req, ∃ b,
    ∀ (reply_ptr:loc) (reply:Reply64) (lastSeq_ptr lastReply_ptr:loc),
{{{
     "%" ∷ ⌜int.nat req.(Req_Seq) > 0⌝
    ∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM
    ∗ "HlastReplyMap" ∷ is_map (lastReply_ptr) lastReplyM
    ∗ "Hreply" ∷ own_reply reply_ptr reply
}}}
    lockservice.CheckReplyTable #lastSeq_ptr #lastReply_ptr #req.(Req_CID) #req.(Req_Seq) #reply_ptr
{{{
     (reply':Reply64), RET #b;
    "Hreply" ∷ own_reply reply_ptr reply' ∗ (
    "Hcases" ∷ ("%" ∷ ⌜b = false⌝ ∗
    "%" ∷ ⌜(int.Z req.(Req_Seq) > int.Z (map_get lastSeqM req.(Req_CID)).1)%Z⌝ ∗
    "%" ∷ ⌜reply'.(Rep_Stale) = false⌝ ∗
    "HlastSeqMap" ∷ is_map (lastSeq_ptr) (<[req.(Req_CID):=req.(Req_Seq)]>lastSeqM))
    ∨
    "%" ∷ ⌜b = true⌝ ∗
    "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM ∗
    "Hwand" ∷ (∀ γrpc, RPCServer_own γrpc lastSeqM lastReplyM -∗ reply_res γrpc req reply')
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
       ⌜has_req_encoding_put data rid args⌝
  }}}
.
Proof.
Admitted.

Lemma wp_GoKVServer__put_inner s req_ptr reply_ptr rid args gkv reply :
  ∃ gkv',
  {{{
       read_request req_ptr rid args ∗
       own_reply reply_ptr reply ∗
       gokv_core s gkv
  }}}
    GoKVServer__put_inner #s #req_ptr #reply_ptr
  {{{
       reply', RET #(); gokv_core s gkv' ∗
            (∀ data req_data γ, has_gokv_encoding data gkv →
                              ⌜has_req_encoding_put req_data rid args⌝ →
                              gokv_aof_ctx γ.(rpc_gn) γ.(kvs_gn) (data) ={⊤}=∗
                              gokv_aof_ctx γ.(rpc_gn) γ.(kvs_gn) (data ++ req_data) ∗ reply_res γ.(rpc_gn) rid reply' (* this should be resources for the reply' *)
            ) ∗
       own_reply reply_ptr reply'
  }}}
.
Proof.
  destruct (wp_CheckReplyTable gkv.(lastSeqM) gkv.(lastReplyM) rid) as [b H].
  eexists (if b then _ else _).
  iLöb as "IH" forall (s req_ptr reply_ptr reply).
  iIntros (Φ) "Hpre HΦ".
  wp_lam.
  wp_pures.
  iDestruct "Hpre" as "(#Hargs & Hreply & Hcore)".

  iNamed "Hcore".
  iNamed "Hargs".

  repeat wp_loadField.
  specialize (H reply_ptr reply lastSeq_ptr lastReply_ptr).
  wp_bind (lockservice.CheckReplyTable _ _ _ _ _).
  wp_apply (H with "[$HlastSeqMap $Hreply $HlastReplyMap]").
  { iDestruct "HSeqPositive" as %?. iPureIntro. word. }
  iIntros (reply').
  iIntros "HcheckPost".
  wp_if_destruct.
  {
    iNamed "HcheckPost".
    iDestruct "HcheckPost" as "[[Hbad|HcheckPost] HlastReplyMap]".
    { iNamed "Hbad". iNamed "Hcases". done. }
    iNamed "HcheckPost".
    iApply "HΦ".
    iSplitR "Hwand Hreply".
    {
      iExists _, _, _, _. iFrame "#∗".
    }
    {
      iFrame. iIntros (???) "#Henc1". iIntros (?) "Hctx".
      iNamed "Hctx".
      iDestruct (has_gokv_encoding_injective with "Henc1 Henc") as %<-.
      iDestruct ("Hwand" with "Hsrpc") as "#Hres".
      iFrame "#".
      iExists gkv.
      iFrame.
      iModIntro.
      iApply (has_gokv_encoding_append $! H1 with "Henc").
      unfold apply_op_req.
      iIntros.
      iIntros (?) "!# Hpre HΦ".
      (* Apply IH to get has_gokv_encoding *)
      wp_apply ("IH" with "[$Hpre]").

      iIntros (?) "HH".
      iApply "HΦ".
      iDestruct "HH" as "($ & _ & $)".
    }
  }
  (* case that we need to actually do an operation *)

  iDestruct "HcheckPost" as "(Hreply & [Hcheck|Hbad] & HlastReply)"; last first.
  {
    iNamed "Hbad". exfalso. done.
  }
  iNamed "Hcheck".
  iNamed "Hcases".

  wp_loadField.
  wp_loadField.
  wp_loadField.

  wp_apply (wp_MapInsert with "HkvsMap").
  { done. }
  iIntros "HkvsMap".

  iApply "HΦ".
  iSplitR "Hreply".
  {
    instantiate (1:= mkGoKVServerC _ _ _).
    iExists _, _, _, _.
    Opaque typed_map.map_insert.
    Opaque map_insert.
    iFrame "HlastSeqOwn HlastReplyOwn HkvsOwn ∗".
  }
  {
    iFrame. iIntros (???) "#Henc1". iIntros (?) "Hctx".
    iNamed "Hctx".
    iDestruct (has_gokv_encoding_injective with "Henc1 Henc") as %<-.
    rewrite sep_exist_r.
    iExists _.
    rewrite -sep_assoc.
    iSplitL "".
    {
      iModIntro. iApply (has_gokv_encoding_append $! H3 with "Henc").

      unfold apply_op_req.
      iIntros.
      iIntros (?) "!# Hpre HΦ".
      (* Apply IH to get has_gokv_encoding *)
      wp_apply ("IH" with "[$Hpre]").

      iIntros (?) "HH".
      iApply "HΦ".
      iDestruct "HH" as "($ & _ & $)".
    }
    iSimpl.
    (* TODO: want rpc request invariant here*)
    admit.
  }
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

  wp_pures.

  wp_apply (wp_GoKVServer__put_inner with "[$Hargs $Hreply $Hcore]").
  iIntros (gkv' reply') "(Hcore & HcommitFupd & Hreply)".
  wp_pures.

  wp_apply (wp_encodeReq_put with "[$Hargs]").
  iIntros (req_sl req_data) "[Hreq_sl %Hreq_enc]".
  wp_loadField.
  iDestruct "Haof_log" as (?) "[Haof_log %]".
  wp_apply (wp_AppendOnlyFile__Append with "His_aof [$Hreq_sl $Haof_log HcommitFupd]").
  {
    iIntros "Hctx".
    iMod ("HcommitFupd" $! data req_data γ with "[] [] Hctx") as "Hfupd".
    { done. }
    { done. }
    iFrame.
    by iModIntro.
  }

  iIntros (l) "[Haof_log Hwand]".
  wp_pures.

  wp_loadField.
  wp_apply (release_spec with "[- HΦ Hwand Hreply]").
  {
    iFrame "#∗".
    iNext. iExists _, _. iFrame "∗#".
    iExists _; iFrame.
    (* This should be true by virtue of the fact that the wp above worked *)
    admit.
  }
  wp_pures.
  wp_loadField.
  wp_apply (wp_AppendOnlyFile__WaitAppend with "His_aof").
  iIntros "Haof_lb".
  iMod ("Hwand" with "Haof_lb") as "Hreply_res".
  wp_pures.
  iApply "HΦ".
  iExists _; iFrame "∗#".
Admitted.
