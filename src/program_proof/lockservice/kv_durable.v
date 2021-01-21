From Coq.Structures Require Import OrdersTac.
From stdpp Require Import gmap.
From iris.algebra Require Import numbers.
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
From Perennial.program_proof.lockservice Require Import rpc_proof rpc nondet kv_proof fmcounter_map rpc_durable_proof.
From Perennial.program_proof Require Import proof_prelude marshal_proof.

Section kv_durable_proof.
Context `{!heapG Σ, !kvserviceG Σ, stagedG Σ}.

Implicit Types (γ : kvservice_names).

Local Notation "k [[ γ ]]↦ '_'" := (∃ v, k [[γ]]↦ v)%I
(at level 20, format "k  [[ γ ]]↦ '_'") : bi_scope.

Record KVServerC :=
  {
  kvsM : gmap u64 u64;
  }.

Global Instance PutPre_disc γ args : Discretizable (Put_Pre γ args) := _.
Global Instance PutPre_timeless γ args : Timeless (Put_Pre γ args) := _.

Axiom KVServer_core_own_durable : KVServerC → RPCServerC  -> iProp Σ.

Definition KVServer_core_own_vol (srv:loc) kv_server : iProp Σ :=
  ∃ (kvs_ptr:loc),
  "HkvsOwn" ∷ srv ↦[KVServer.S :: "kvs"] #kvs_ptr ∗
  "HkvsMap" ∷ is_map (kvs_ptr) kv_server.(kvsM)
.

Definition KVServer_core_own_ghost γ kv_server : iProp Σ :=
  "Hkvctx" ∷ map_ctx γ.(ks_kvMapGN) 1 kv_server.(kvsM)
.

Definition RPCServer_own_vol (sv:loc) rpc_server : iProp Σ :=
  ∃ (lastSeq_ptr lastReply_ptr:loc),
    "HlastSeqOwn" ∷ sv ↦[RPCServer.S :: "lastSeq"] #lastSeq_ptr
∗ "HlastReplyOwn" ∷ sv ↦[RPCServer.S :: "lastReply"] #lastReply_ptr
∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) rpc_server.(lastSeqM)
∗ "HlastReplyMap" ∷ is_map (lastReply_ptr) rpc_server.(lastReplyM)
.

Definition RPCServer_own_ghost (sv:loc) γrpc rpc_server : iProp Σ :=
  "Hsrpc" ∷ RPCServer_own γrpc rpc_server.(lastSeqM) rpc_server.(lastReplyM) (* TODO: Probably should get better naming for this *)
.

Definition RPCServer_phys_own γrpc (sv:loc) rpc_server : iProp Σ :=
  "Hrpcvol" ∷ RPCServer_own_vol sv rpc_server ∗
  "Hrpcghost" ∷ RPCServer_own_ghost sv γrpc rpc_server
.

Instance durable_timeless kv_server rpc_server: Timeless (KVServer_core_own_durable kv_server rpc_server).
Admitted.

Instance durable_disc kv_server rpc_server: Discretizable (KVServer_core_own_durable kv_server rpc_server).
Admitted.

Definition own_kvclerk γ ck_ptr srv : iProp Σ :=
  ∃ (cl_ptr:loc),
   "Hcl_ptr" ∷ ck_ptr ↦[KVClerk.S :: "client"] #cl_ptr ∗
   "Hprimary" ∷ ck_ptr ↦[KVClerk.S :: "primary"] #srv ∗
   "Hcl" ∷ own_rpcclient cl_ptr γ.(ks_rpcGN).


Definition kv_core_mu srv γ : rpc_core_mu :=
  {|
  core_own_durable := λ server rpc_server, KVServer_core_own_durable server rpc_server;
  core_own_ghost := λ server, KVServer_core_own_ghost γ server;
  core_own_vol := λ server, KVServer_core_own_vol srv server
  |}.

Lemma wpc_put_core γ (srv:loc) args kvserver :
{{{
     (kv_core_mu srv γ).(core_own_vol) kvserver ∗
     Put_Pre γ args
}}}
  KVServer__put_core #srv (into_val.to_val args) @ 36 ; ⊤
{{{
      kvserver' (r:u64) P', RET #r;
            ⌜Discretizable P'⌝ ∗
             (P') ∗
            KVServer_core_own_vol srv kvserver' ∗
            □ (P' -∗ Put_Pre γ args) ∗
            (* TODO: putting this here because need to be discretizable *)
            □ (P' -∗ KVServer_core_own_ghost γ kvserver ={⊤∖↑rpcRequestInvN}=∗ Put_Post γ args r ∗ KVServer_core_own_ghost γ kvserver')
}}}
{{{
     Put_Pre γ args
}}}.
Proof.
  iIntros (Φ Φc) "[Hvol Hpre] HΦ".
  iCache with "Hpre HΦ".
  { iDestruct "HΦ" as "[HΦc _]". iModIntro. by iApply "HΦc". }
  wpc_call; first done.

  iCache with "Hpre HΦ".
  { iDestruct "HΦ" as "[HΦc _]". iModIntro. by iApply "HΦc". }

  wpc_pures.
  iNamed "Hvol".

  wpc_bind (struct.loadF _ _ _)%E.
  wpc_frame.
  wp_loadField.
  iNamed 1.

  wpc_bind (MapInsert _ _ _).
  wpc_frame.

  wp_apply (wp_MapInsert with "HkvsMap"); eauto; iIntros "HkvsMap".
  iNamed 1.
  wpc_pures.
  iDestruct "HΦ" as "[_ HΦ]".
  iApply ("HΦ" $! {| kvsM := <[args.1:=args.2.1]> kvserver.(kvsM) |} _ (Put_Pre γ args)).
  iFrame.
  iSplitL "".
  { iPureIntro. by apply PutPre_disc. }
  iSplitR "".
  { iExists _; iFrame. }
  iSplit; first eauto.
  iModIntro.
  iIntros "Hpre Hghost".
  iDestruct "Hpre" as (v) "Hpre".
  iMod (map_update with "Hghost Hpre") as "[Hkvctx Hptsto]".
  iModIntro. iFrame.
Qed.

Lemma wpc_WriteDurableKVServer γ (srv rpc_srv:loc) server rpc_server server' rpc_server':
readonly (srv ↦[lockservice.KVServer.S :: "sv"] #rpc_srv) -∗
{{{
    (kv_core_mu srv γ).(core_own_vol) server' ∗
    RPCServer_own_vol rpc_srv rpc_server' ∗
    (kv_core_mu srv γ).(core_own_durable) server rpc_server
}}}
  WriteDurableKVServer #srv @ 36 ; ⊤
{{{
      RET #();
    (kv_core_mu srv γ).(core_own_vol) server' ∗
    RPCServer_own_vol rpc_srv rpc_server' ∗
    (kv_core_mu srv γ).(core_own_durable) server' rpc_server'
}}}
{{{
     (kv_core_mu srv γ).(core_own_durable) server rpc_server ∨
     (kv_core_mu srv γ).(core_own_durable) server' rpc_server'
}}}.
Admitted.

Lemma wp_MapLen mref m:
{{{
    is_map (V:=u64) mref m
}}}
  (MapLen #mref)
{{{
  RET #(map_size m);
    is_map mref m
}}}.
Admitted.

Definition EncMap_invariant enc_v (r:Rec) sz map_sz (mtodo mdone:gmap u64 u64) : iProp Σ :=
  ∃ (l:list (u64 * u64)) remaining,
    ⌜(list_to_map l) = mdone⌝ ∗
    ⌜remaining > 8 * 2 * (map_size mtodo)⌝ ∗
    is_enc enc_v sz (r ++ [EncUInt64 map_sz] ++ (flat_map (λ u, [EncUInt64 u.1 ; EncUInt64 u.2]) l )) remaining
.

Lemma wp_EncMap e mref m sz r remaining :
8 < remaining →
{{{
    "Hmap" ∷ is_map (V:=u64) mref m ∗
    "Henc" ∷ is_enc e sz r remaining
}}}
  EncMap e #mref
{{{
     RET #(); True
}}}.
Proof.
  intros Hrem.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_lam. wp_pures.

  wp_apply (wp_MapLen with "Hmap").
  iIntros "Hmap".
  wp_apply (wp_Enc__PutInt with "Henc").
  { lia. }
  iIntros "Henc".
  wp_pures.
  wp_apply (wp_MapIter_2 _ _ _ _ (EncMap_invariant e r sz (map_size m)) with "Hmap [Henc] [] [HΦ]").
  { iExists [] . iExists (remaining-8). simpl. iFrame. (* TODO: adjust size of enc *) admit. }
  {
    clear Φ.
    iIntros (???? Φ) "!# [Hpre %Htodo] HΦ".
    wp_pures.
    iDestruct "Hpre" as (l rem' Hl Hrem') "Henc".

    assert (map_size mtodo ≠ 0%nat).
    { apply map_size_non_empty_iff.
      admit.
    }
    wp_apply (wp_Enc__PutInt with "Henc").
    {
      lia.
    }
    iIntros "Henc".
    wp_pures.

    wp_apply (wp_Enc__PutInt with "Henc").
    {
      lia.
    }
    iIntros "Henc".
    iApply "HΦ".
    iExists (l ++ [(k, v)]), (rem' - 8 - 8).
    iSplit.
    { iPureIntro. admit. }
    iSplit.
    { replace (map_size (delete k mtodo)) with (pred (map_size mtodo)).
      { admit. }
      { symmetry. apply map_size_delete. eauto. }.
    }
    (* TODO: flat_map of list append vs append to flat_map *)
    admit.
  }
  iIntros.
  iApply "HΦ".
Admitted.

Definition is_kvserver γ (srv rpc_srv:loc) : iProp Σ :=
  "#Hsv" ∷ readonly (srv ↦[KVServer.S :: "sv"] #rpc_srv) ∗
  "#His_server" ∷ is_server KVServerC (kv_core_mu srv γ) rpc_srv γ.(ks_rpcGN).

Lemma KVServer__Put_spec srv rpc_srv γ :
is_kvserver γ srv rpc_srv -∗
{{{
    True
}}}
    KVServer__Put #srv
{{{ (f:goose_lang.val), RET f;
        is_rpcHandler f γ.(ks_rpcGN) (Put_Pre γ) (Put_Post γ)
}}}.
Proof.
  iNamed 1.
  iIntros (Φ) "!# Hpre HΦ".
  wp_lam.
  wp_pures.
  iApply "HΦ".
  iApply is_rpcHandler_eta. simpl.
  iIntros "!#" (_ _).
  wp_pures.
  wp_loadField.
  clear Φ.
  iApply (RPCServer__HandleRequest_is_rpcHandler KVServerC); last by eauto.
  {
    iIntros (args server) "!#". iIntros (Φ Φc) "Hpre HΦ".
    iNamed "Hpre".
    iMod "Hpre".
    wpc_pures.
    {
      iDestruct "HΦ" as "[HΦc _]".
      iModIntro.
      by iApply "HΦc".
    }

    iApply (wpc_put_core γ with "[$Hpre $Hvol]").
    iSplit.
    {
      by iDestruct "HΦ" as "[HΦc _]".
    }
    by iDestruct "HΦ" as "[_ HΦ]".
  }
  {
    iIntros (server rpc_server server' rpc_server') "!#".
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
    iFrame "#".
  }
Qed.

End kv_durable_proof.
