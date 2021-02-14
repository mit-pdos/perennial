From iris.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.
From Perennial.goose_lang Require Import notation.
From Perennial.program_proof Require Import proof_prelude.
From RecordUpdate Require Import RecordUpdate.
From Perennial.algebra Require Import auth_map.
From Perennial.goose_lang.lib Require Import lock.
From Perennial.goose_lang.lib Require Import crash_lock.
From Perennial.Helpers Require Import NamedProps.
From Perennial.Helpers Require Import ModArith.
From Goose.github_com.mit_pdos.lockservice Require Import lockservice.
From Perennial.program_proof Require Import proof_prelude marshal_proof.
From Perennial.goose_lang Require Import ffi.grove_ffi.
From Perennial.program_proof.lockservice Require Import rpc_proof rpc_logatom rpc nondet fmcounter_map rpc_logatom_proof rpc_durable_proof kv_proof kv_durable wpc_proofmode.

Section kv_logatom_proof.
Context `{!heapG Σ, !kvserviceG Σ, stagedG Σ}.
Context `{!filesysG Σ}.

Lemma wpc_put_logatom_core γ (srv:loc) args req kvserver Q:
□(▷ Q -∗ |RN={γ.(ks_rpcGN),req.(Req_CID),req.(Req_Seq)}=> Put_Pre γ args) -∗
{{{
     (kv_core_mu srv γ).(core_own_vol) kvserver ∗
     <disc> Q
}}}
  KVServer__put_core #srv (into_val.to_val args) @ 36 ; ⊤
{{{
      kvserver' (r:u64) P', RET #r;
            <disc> (P' ∧ Q) ∗
            KVServer_core_own_vol srv kvserver' ∗
            <disc> (rpc_commit_fupd KVServerC (kv_core_mu srv γ) γ.(ks_rpcGN) req P' (Put_Post γ args r) kvserver kvserver')
}}}
{{{
     Q
}}}.
Proof.
  iIntros "#Hwand !#".
  iIntros (Φ Φc) "[Hvol Hpre] HΦ".
  iCache with "Hpre HΦ".
  { iDestruct "HΦ" as "[HΦc _]". iModIntro. by iApply "HΦc". }
  wpc_call; first done.

  iCache with "Hpre HΦ".
  { iDestruct "HΦ" as "[HΦc _]". iModIntro. by iApply "HΦc". }

  wpc_pures.
  iNamed "Hvol".
  wpc_loadField.

  wpc_bind (MapInsert _ _ _).
  wpc_frame.

  wp_apply (wp_MapInsert with "HkvsMap"); eauto; iIntros "HkvsMap".
  iNamed 1.
  wpc_pures.
  iDestruct "HΦ" as "[_ HΦ]".
  iApply ("HΦ" $! {| kvsM := <[args.(U64_1):=args.(U64_2)]> kvserver.(kvsM) |} _ (▷ Q)%I).
  iSplitL "Hpre".
  { iModIntro. iFrame. }

  iSplitR "".
  { iExists _. iFrame. }

  (* The commit point fupd *)
  iModIntro.
  iIntros "HQ Hghost".
  iMod ("Hwand" with "HQ") as "Hpre".
  iModIntro.

  iDestruct "Hpre" as (v) "Hpre".
  iMod (map_update with "Hghost Hpre") as "[Hkvctx Hptsto]".

  iModIntro.
  iFrame.
Qed.

Lemma wpc_get_logatom_core γ (srv:loc) old_v args req kvserver Q:
□(▷ Q -∗ |RN={γ.(ks_rpcGN),req.(Req_CID),req.(Req_Seq)}=> Get_Pre γ old_v args) -∗
{{{
     (kv_core_mu srv γ).(core_own_vol) kvserver ∗
     <disc> Q
}}}
  KVServer__get_core #srv (into_val.to_val args) @ 36 ; ⊤
{{{
      kvserver' (r:u64) P', RET #r;
            <disc> (P' ∧ Q) ∗
            KVServer_core_own_vol srv kvserver' ∗
            <disc> (rpc_commit_fupd KVServerC (kv_core_mu srv γ) γ.(ks_rpcGN) req P' (Get_Post γ old_v args r) kvserver kvserver')
}}}
{{{
     Q
}}}.
Proof.
  iIntros "#Hwand !#".
  iIntros (Φ Φc) "[Hvol Hpre] HΦ".
  iCache with "Hpre HΦ".
  { iDestruct "HΦ" as "[HΦc _]". iModIntro. by iApply "HΦc". }
  wpc_call; first done.

  iCache with "Hpre HΦ".
  { iDestruct "HΦ" as "[HΦc _]". iModIntro. by iApply "HΦc". }

  wpc_pures.
  iNamed "Hvol".
  wpc_loadField.

  wpc_bind (MapGet _ _).
  wpc_frame.

  wp_apply (wp_MapGet with "HkvsMap").
  iIntros (v ok) "[%Hmapget HkvsMap]".
  iNamed 1.

  wpc_pures.
  iDestruct "HΦ" as "[_ HΦ]".
  iApply ("HΦ" $! kvserver _ (▷ Q)%I).
  iSplitL "Hpre".
  { iModIntro. iFrame. }

  iSplitR "".
  { iExists _. iFrame. }

  (* The commit point fupd *)
  iModIntro.
  iIntros "HQ Hghost".
  iMod ("Hwand" with "HQ") as "Hpre".
  iModIntro.

  iDestruct (map_valid with "Hghost Hpre") as %Hvalid.

  iModIntro.
  iFrame.
  assert (old_v = v) as ->.
  {
    unfold map_get in *.
    rewrite Hvalid in Hmapget.
    naive_solver.
  }
  iFrame.
  done.
Qed.

Lemma KVServer__Put_is_rpcHandler {E s} γ srv cid :
is_kvserver γ srv -∗
{{{
    True
}}}
    KVServer__Put #srv @ s; E
{{{ (f:goose_lang.val), RET f;
    ∀ args, is_rpcHandler' f γ.(ks_rpcGN) cid args (Put_Pre γ args) (Put_Post γ args)
}}}.
Proof.
  iIntros "#His_kv !#" (Φ) "_ HΦ".
  wp_lam.
  wp_pures.
  iApply "HΦ".
  iIntros (args req) "!#". iIntros (Q) "#HQtmless #HQdisc #HwandQ".
  iApply is_rpcHandler_eta.
  iIntros "!#" (replyv reqv).
  simpl.
  iAssert (_) with "His_kv" as "His_kv2".
  iNamed "His_kv2".
  wp_loadField.
  wp_apply (RPCServer__HandleRequest_is_rpcHandler KVServerC with "[] [] [His_kv]").
  {
    clear Φ.
    iIntros (server) "!#". iIntros (Φ Φc) "Hpre HΦ".
    iNamed "Hpre".
    iMod ("HQtmless" with "Hpre") as "HQ".
    iDestruct ("HQdisc" with "HQ") as "HQ".
    wpc_pures.
    { iLeft in "HΦ". iModIntro. by iApply "HΦ". }

    iApply (wpc_put_logatom_core γ _ _ {|Req_CID:=_; Req_Seq:= _ |} with "HwandQ [$HQ $Hvol]").
    iSplit.
    { by iLeft in "HΦ". }
    iNext.
    by iRight in "HΦ".
  }
  {
    iIntros (server rpc_server server' rpc_server') "!#".
    clear Φ.
    iIntros (Φ Φc) "Hpre HΦ".
    wpc_pures.
    {
      iDestruct "Hpre" as "(_ & _ & Hdur)". (* Requires own_durable to be discretizable *)
      iDestruct "HΦ" as "[HΦc _]".
      iModIntro.
      iApply "HΦc".
      by iLeft.
    }
    wpc_apply (wpc_WriteDurableKVServer with "Hsv Hpre").
    iSplit.
    {
      by iDestruct "HΦ" as "[HΦc _]".
    }
    iNext. by iDestruct "HΦ" as "[_ HΦ]".
  }
  {
    iFrame "His_server".
  }
  iIntros (f) "His_rpcHandler".
  iFrame.
Qed.

Lemma KVServer__Get_is_rpcHandler {E s} γ srv cid old_v :
is_kvserver γ srv -∗
{{{
    True
}}}
    KVServer__Get #srv @ s; E
{{{ (f:goose_lang.val), RET f;
    ∀ args, is_rpcHandler' f γ.(ks_rpcGN) cid args (Get_Pre γ old_v args) (Get_Post γ old_v args)
}}}.
Proof.
  iIntros "#His_kv !#" (Φ) "_ HΦ".
  wp_lam.
  wp_pures.
  iApply "HΦ".
  iIntros (args req) "!#". iIntros (Q) "#HQtmless #HQdisc #HwandQ".
  iApply is_rpcHandler_eta.
  iIntros "!#" (replyv reqv).
  simpl.
  iAssert (_) with "His_kv" as "His_kv2".
  iNamed "His_kv2".
  wp_loadField.
  wp_apply (RPCServer__HandleRequest_is_rpcHandler KVServerC with "[] [] [His_kv]").
  {
    clear Φ.
    iIntros (server) "!#". iIntros (Φ Φc) "Hpre HΦ".
    iNamed "Hpre".
    iMod ("HQtmless" with "Hpre") as "HQ".
    iDestruct ("HQdisc" with "HQ") as "HQ".
    wpc_pures.
    { iLeft in "HΦ". iModIntro. by iApply "HΦ". }

    iApply (wpc_get_logatom_core γ _ _ _ {|Req_CID:=_; Req_Seq:= _ |} with "HwandQ [$HQ $Hvol]").
    iSplit.
    { by iLeft in "HΦ". }
    iNext.
    by iRight in "HΦ".
  }
  {
    iIntros (server rpc_server server' rpc_server') "!#".
    clear Φ.
    iIntros (Φ Φc) "Hpre HΦ".
    wpc_pures.
    {
      iDestruct "Hpre" as "(_ & _ & Hdur)". (* Requires own_durable to be discretizable *)
      iDestruct "HΦ" as "[HΦc _]".
      iModIntro.
      iApply "HΦc".
      by iLeft.
    }
    wpc_apply (wpc_WriteDurableKVServer with "Hsv Hpre").
    iSplit.
    {
      by iDestruct "HΦ" as "[HΦc _]".
    }
    iNext. by iDestruct "HΦ" as "[_ HΦ]".
  }
  {
    iFrame "His_server".
  }
  iIntros (f) "His_rpcHandler".
  iFrame.
Qed.

Definition own_kvclerk_cid γ ck_ptr srv cid : iProp Σ :=
  ∃ (cl_ptr:loc),
   "Hcl_ptr" ∷ ck_ptr ↦[KVClerk.S :: "client"] #cl_ptr ∗
   "Hprimary" ∷ ck_ptr ↦[KVClerk.S :: "primary"] #srv ∗
   "Hcl" ∷ own_rpcclient_cid cl_ptr γ.(ks_rpcGN) cid.

Notation "k [[ γ ]]↦ '_'" := (∃ v, k [[γ]]↦ v)%I
(at level 20, format "k  [[ γ ]]↦ '_'") : bi_scope.

Lemma wpc_KVClerk__Put k γ (kck srv:loc) (cid:u64) (key value:u64) :
  is_kvserver γ srv -∗
  {{{
       own_kvclerk_cid γ kck srv cid ∗
       |PN={γ.(ks_rpcGN),cid}=> (key [[γ.(ks_kvMapGN)]]↦ _)
  }}}
    KVClerk__Put #kck #key #value @ k; ⊤
  {{{
      RET #();
      own_kvclerk_cid γ kck srv cid ∗
      (key [[γ.(ks_kvMapGN)]]↦ value )
  }}}
  {{{
       |={⊤}=> |PN={γ.(ks_rpcGN),cid}=> (key [[γ.(ks_kvMapGN)]]↦ _)
  }}}
.
Proof.
  iIntros "#His_kv !#" (Φ Φc) "Hpre HΦ".
  iDestruct "Hpre" as "(Hclerk & Hq)".
  iCache with "Hq HΦ".
  {
    iDestruct "HΦ" as "[HΦc _]".
    iModIntro.
    iApply "HΦc".
    done.
  }
  wpc_call.
  { done. }
  iCache with "Hq HΦ".
  {
    iDestruct "HΦ" as "[HΦc _]".
    iModIntro.
    iApply "HΦc".
    done.
  }
  wpc_pures.
  iNamed "Hclerk".
  wpc_loadField.

  wpc_bind (KVServer__Put _).
  wpc_frame.
  wp_apply (KVServer__Put_is_rpcHandler  with "His_kv").
  iIntros (f) "#Hfspec".
  iNamed 1.

  wpc_loadField.
  pose (args:={|U64_1:=key; U64_2:=value |}).
  replace (#key, (#value, #()))%V with (into_val.to_val args) by done.
  iDestruct ("Hfspec" $! args) as "#Hfspec2".
  iApply wpc_fupd.
  wpc_apply (wpc_RPCClient__MakeRequest with "Hfspec2 [Hq Hcl His_kv]").
  { iNamed "His_kv". iFrame. iNamed "His_server". iNamed "Hlinv".
    iFrame "#".
  }
  iSplit.
  {
    iLeft in "HΦ".
    iModIntro.
    iIntros "Hpnfupd".
    iApply "HΦ".
    iMod "Hpnfupd".
    iModIntro.
    iModIntro.
    iDestruct "Hpnfupd" as "[>Hpre|>Hpost]".
    { iModIntro. done. }
    { iModIntro. (* Idempotence of puts is proved here *)
      unfold Put_Post.
      iDestruct "Hpost" as (_) "Hpost".
      iExists _; iFrame.
    }
  }
  iNext.
  iIntros (retv) "[Hcl >Hpost]".
  wpc_pures.
  {
    iLeft in "HΦ". iModIntro.
    iApply "HΦ".
    iModIntro. iModIntro. iModIntro.
    iExists _; iFrame "Hpost".
  }
  iRight in "HΦ". iModIntro.
  iApply "HΦ".
  iFrame. iExists _; iFrame.
Qed.

Lemma wpc_KVClerk__Get k γ (kck srv:loc) (old_v cid:u64) (key:u64) :
  is_kvserver γ srv -∗
  {{{
       own_kvclerk_cid γ kck srv cid ∗
       |PN={γ.(ks_rpcGN),cid}=> (key [[γ.(ks_kvMapGN)]]↦ old_v)
  }}}
    KVClerk__Get #kck #key @ k; ⊤
  {{{
      RET #old_v;
      own_kvclerk_cid γ kck srv cid ∗
      (key [[γ.(ks_kvMapGN)]]↦ old_v )
  }}}
  {{{
       |={⊤}=> |PN={γ.(ks_rpcGN),cid}=> (key [[γ.(ks_kvMapGN)]]↦ old_v)
  }}}
.
Proof.
  iIntros "#His_kv !#" (Φ Φc) "Hpre HΦ".
  iDestruct "Hpre" as "(Hclerk & Hq)".
  iCache with "Hq HΦ".
  {
    iDestruct "HΦ" as "[HΦc _]".
    iModIntro.
    iApply "HΦc".
    done.
  }
  wpc_call.
  { done. }
  iCache with "Hq HΦ".
  {
    iDestruct "HΦ" as "[HΦc _]".
    iModIntro.
    iApply "HΦc".
    done.
  }
  wpc_pures.
  iNamed "Hclerk".
  wpc_loadField.

  wpc_bind (KVServer__Get _).
  wpc_frame.
  wp_apply (KVServer__Get_is_rpcHandler  with "His_kv").
  iIntros (f) "#Hfspec".
  iNamed 1.

  wpc_loadField.
  pose (args:={|U64_1:=key; U64_2:=0 |}).
  replace (#key, (#0, #()))%V with (into_val.to_val args) by done.
  iDestruct ("Hfspec" $! args) as "#Hfspec2".
  iApply wpc_fupd.
  wpc_apply (wpc_RPCClient__MakeRequest with "Hfspec2 [Hq Hcl His_kv]").
  { iNamed "His_kv". iFrame. iNamed "His_server". iNamed "Hlinv".
    iFrame "#".
  }
  iSplit.
  {
    iLeft in "HΦ".
    iModIntro.
    iIntros "Hpnfupd".
    iApply "HΦ".
    iMod "Hpnfupd".
    iModIntro.
    iModIntro.
    iDestruct "Hpnfupd" as "[>Hpre|>Hpost]".
    { iModIntro. done. }
    { iModIntro. (* Idempotence of puts is proved here *)
      iDestruct "Hpost" as (ret ->) "$".
    }
  }
  iNext.
  iIntros (retv) "[Hcl >[%Hre Hptsto]]".
  rewrite Hre.
  iRight in "HΦ". iModIntro.
  iApply "HΦ".
  iFrame. iExists _; iFrame.
Qed.

End kv_logatom_proof.
