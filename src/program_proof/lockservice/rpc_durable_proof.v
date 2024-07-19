From Coq.Structures Require Import OrdersTac.
From stdpp Require Import gmap.
From iris.algebra Require Import numbers.
From Perennial.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.
From Perennial.goose_lang Require Import notation.
From Perennial.program_proof Require Import disk_prelude.
From RecordUpdate Require Import RecordUpdate.
From Perennial.algebra Require Import auth_map.
From Perennial.goose_lang.lib Require Import lock.
From Perennial.goose_lang.lib Require Import crash_lock.
From Perennial.Helpers Require Import NamedProps.
From Perennial.Helpers Require Import ModArith.
From Goose.github_com.mit_pdos.lockservice Require Import lockservice.
From Perennial.program_proof.grove_shared Require Import erpc_lib fmcounter_map.
From Perennial.program_proof.lockservice Require Import rpc_proof rpc_logatom nondet kv_proof.

Section rpc_durable_proof.
Context `{!heapGS Σ, !rpcG Σ u64, !stagedG Σ}.

Record RPCServerC :=
  {
  lastSeqM : gmap u64 u64;
  lastReplyM  : gmap u64 u64;
  }.

(* Set of resources needed to make use of HandleRequest *)
Record rpc_core_mu {serverC:Type} := mkcore_mu
{
 core_own_durable : serverC → RPCServerC -> iProp Σ ; (* This also owns the durable rpc server state *)
 core_own_ghost : serverC → iProp Σ ;
 core_own_vol: serverC → iProp Σ ;

 core_durable_timeless server rpc_server : Timeless (core_own_durable server rpc_server) ;
 core_durable_disc server rpc_server : Discretizable (core_own_durable server rpc_server) ;

 core_ghost_timeless server : Timeless (core_own_ghost server) ;
 core_ghost_disc server : Discretizable (core_own_ghost server) ;

 core_vol_timeless server : Timeless (core_own_vol server) ;
}
.

Variable serverC : Type. (* Abstract state of the server, used by core_own_* functions *)

Variable core : @rpc_core_mu serverC.

Context (core_own_durable := core.(core_own_durable)).
Context (core_own_vol := core.(core_own_vol)).
Context (core_own_ghost := core.(core_own_ghost)).

Local Instance durable_timeless server rpc_server : Timeless (core_own_durable server rpc_server) := core.(core_durable_timeless) server rpc_server.
Local Instance vol_timeless server : Timeless (core_own_vol server) := core.(core_vol_timeless) server.
Local Instance ghost_timeless server : Timeless (core_own_ghost server) := core.(core_ghost_timeless) server.

Local Instance durable_disc server rpc_server : Discretizable (core_own_durable server rpc_server) := core.(core_durable_disc) server rpc_server.
Local Instance ghost_disc server : Discretizable (core_own_ghost server) := core.(core_ghost_disc) server.

Definition Server_mutex_cinv γrpc : iProp Σ :=
  ∃ server rpc_server,
  "Hcoredurable" ∷ core_own_durable server rpc_server ∗
  "Hcoreghost" ∷ core_own_ghost server ∗
  "Hsrpc" ∷ RPCServer_own γrpc rpc_server.(lastSeqM) rpc_server.(lastReplyM)
.

Definition RPCServer_own_vol (sv:loc) rpc_server : iProp Σ :=
  ∃ (lastSeq_ptr lastReply_ptr:loc),
    "HlastSeqOwn" ∷ sv ↦[RPCServer :: "lastSeq"] #lastSeq_ptr
∗ "HlastReplyOwn" ∷ sv ↦[RPCServer :: "lastReply"] #lastReply_ptr
∗ "HlastSeqMap" ∷ own_map (lastSeq_ptr) rpc_server.(lastSeqM)
∗ "HlastReplyMap" ∷ own_map (lastReply_ptr) rpc_server.(lastReplyM)
.

Definition RPCServer_own_ghost (sv:loc) γrpc rpc_server : iProp Σ :=
  "Hsrpc" ∷ RPCServer_own γrpc rpc_server.(lastSeqM) rpc_server.(lastReplyM) (* TODO: Probably should get better naming for this *)
.

(* TODO: rename RPCServer_own to RPCServer_own_ghost and get rid of all in this name *)
Definition RPCServer_all_own γrpc (sv:loc) rpc_server : iProp Σ :=
  "Hrpcvol" ∷ RPCServer_own_vol sv rpc_server ∗
  "Hrpcghost" ∷ RPCServer_own_ghost sv γrpc rpc_server
.

Definition Server_mutex_inv rpc_srv_ptr γrpc : iProp Σ :=
  ∃ server rpc_server,
    "Hcorevol" ∷ core_own_vol server ∗
    "Hcoreghost" ∷ core_own_ghost server ∗
    "Hcoredurable" ∷ core_own_durable server rpc_server ∗
    "Hrpc" ∷ RPCServer_all_own γrpc rpc_srv_ptr rpc_server
.

Definition mutexN : namespace := nroot .@ "server_mutexN".

Definition is_server rpc_srv_ptr γrpc : iProp Σ :=
  ∃ (mu_ptr:loc),
  "#Hlinv" ∷ is_RPCServer γrpc ∗
  "#Hmu_ptr" ∷ readonly(rpc_srv_ptr ↦[RPCServer :: "mu"] #mu_ptr) ∗
  "#Hmu" ∷ is_crash_lock mutexN 37 #mu_ptr (Server_mutex_inv rpc_srv_ptr γrpc)
    (|={⊤}=> Server_mutex_cinv γrpc) (* FIXME:(US) get rid of this fupd *)
.

Lemma CheckReplyTable_spec (reply_ptr:loc) (req:RPCRequestID) (reply:Reply64) γrpc (lastSeq_ptr lastReply_ptr:loc) lastSeqM lastReplyM :
{{{
     "%" ∷ ⌜uint.nat req.(Req_Seq) > 0⌝
    ∗ "#Hrinv" ∷ is_RPCServer γrpc
    ∗ "HlastSeqMap" ∷ own_map (lastSeq_ptr) lastSeqM
    ∗ "HlastReplyMap" ∷ own_map (lastReply_ptr) lastReplyM
    ∗ ("Hsrpc" ∷ RPCServer_own γrpc lastSeqM lastReplyM)
    ∗ ("Hreply" ∷ own_reply reply_ptr reply)
}}}
CheckReplyTable #lastSeq_ptr #lastReply_ptr #req.(Req_CID) #req.(Req_Seq) #reply_ptr @ 36; ⊤
{{{
     (b:bool) reply', RET #b;
      "Hreply" ∷ own_reply reply_ptr reply'
    ∗ "Hcases" ∷ ("%" ∷ ⌜b = false⌝
         ∗ "%" ∷ ⌜(uint.Z (map_get lastSeqM req.(Req_CID)).1 < uint.Z req.(Req_Seq))%Z⌝
         ∗ "%" ∷ ⌜reply'.(Rep_Stale) = false⌝
         ∗ "HlastSeqMap" ∷ own_map (lastSeq_ptr) (<[req.(Req_CID):=req.(Req_Seq)]>lastSeqM)
         ∨ 
         "%" ∷ ⌜b = true⌝
         ∗ "HlastSeqMap" ∷ own_map (lastSeq_ptr) lastSeqM
         ∗ ((⌜reply'.(Rep_Stale) = true⌝ ∗ RPCRequestStale γrpc req)
          ∨ RPCReplyReceipt γrpc req reply'.(Rep_Ret)))

    ∗ "HlastReplyMap" ∷ own_map (lastReply_ptr) lastReplyM
    ∗ ("Hsrpc" ∷ RPCServer_own γrpc lastSeqM lastReplyM)
}}}
{{{
    RPCServer_own γrpc lastSeqM lastReplyM
}}}
.
Proof.
  iIntros (Φ Φc) "Hpre Hpost".
  iNamed "Hpre".
  wpc_call.
  { iFrame. }
  { iFrame. }
  iCache with "Hsrpc Hpost".
  { iDestruct "Hpost" as "[Hpost _]". iModIntro. by iApply "Hpost". }
  wpc_pures.
  iApply wpc_fupd.
  wpc_frame.
  wp_apply (wp_MapGet with "HlastSeqMap").
  iIntros (v ok) "(HSeqMapGet&HlastSeqMap)"; iDestruct "HSeqMapGet" as %HSeqMapGet.
  wp_pures.
  iNamed "Hreply".
  wp_storeField.
  wp_apply (wp_and ok (uint.Z req.(Req_Seq) ≤ uint.Z v)%Z).
  { wp_pures. by destruct ok. }
  { iIntros "_". wp_pures. done. }
  rewrite bool_decide_decide.
  destruct (decide (ok ∧ uint.Z req.(Req_Seq) ≤ uint.Z v)%Z) as [ [Hok Hineq]|Hmiss].
  { (* Cache hit *)
    destruct ok; last done. clear Hok. (* ok = false *)
    wp_pures.
    apply map_get_true in HSeqMapGet.
    destruct bool_decide eqn:Hineqstrict.
    - wp_pures.
      apply bool_decide_eq_true in Hineqstrict.
      wp_storeField.
      iNamed 1.
      iMod (smaller_seqno_stale_fact with "[] Hsrpc") as "[Hsrpc #Hstale]"; eauto.
      iDestruct "Hpost" as "[_ Hpost]".
      iApply "Hpost".
      iModIntro.
      iSplitL "HReplyOwnStale HReplyOwnRet".
      { eauto with iFrame. instantiate (1:={| Rep_Ret:=_; Rep_Stale:=_ |}).
        iFrame. }
      iFrame; iFrame "#".
      iRight.
      eauto with iFrame.
    - wp_pures.
      assert (v = req.(Req_Seq)) as ->. {
        (* not strict + non-strict ineq ==> eq *)
        apply bool_decide_eq_false in Hineqstrict.
        assert (uint.Z req.(Req_Seq) = uint.Z v) by lia; word.
      }
      wp_apply (wp_MapGet with "HlastReplyMap").
      iIntros (reply_v reply_get_ok) "(HlastReplyMapGet & HlastReplyMap)"; iDestruct "HlastReplyMapGet" as %HlastReplyMapGet.
      wp_storeField.
      iNamed 1.
      iMod (server_replies_to_request with "[Hrinv] [Hsrpc]") as "[#Hreceipt Hsrpc]"; eauto.
      iApply "Hpost".
      iModIntro.
      iSplitL "HReplyOwnStale HReplyOwnRet".
      { eauto with iFrame. instantiate (1:={| Rep_Ret:=_; Rep_Stale:=_ |}).
        iFrame. }
      iFrame.
      iRight.
      by iFrame; iFrame "#".
  }
  { (* Cache miss *)
    wp_pures.
    apply not_and_r in Hmiss.
    wp_apply (wp_MapInsert _ _ lastSeqM _ req.(Req_Seq) (#req.(Req_Seq)) with "HlastSeqMap"); eauto.
    iIntros "HlastSeqMap".
    wp_pures.
    iNamed 1.
    iDestruct "Hpost" as "[_ Hpost]".
    iApply ("Hpost" $! _ ({| Rep_Stale:=false; Rep_Ret:=reply.(Rep_Ret) |}) ).
    iModIntro.
    iFrame; iFrame "#".
    iLeft. iFrame. iPureIntro.
    split; eauto. split; eauto. injection HSeqMapGet as <- Hv. simpl.
    destruct Hmiss as [Hnok|Hineq].
    - destruct ok; first done.
      destruct (lastSeqM !! req.(Req_CID)); first done.
      simpl. word.
    - word.
  }
Qed.

Context (coreFunction:goose_lang.val).
Context (makeDurable:goose_lang.val).
Context (PreCond:iProp Σ).
Context (PostCond:u64 -> iProp Σ).
Context (rpc_srv_ptr:loc).

Definition rpc_commit_fupd γrpc req P Q server server' : iProp Σ :=
  P -∗
  core_own_ghost server -∗
  (|RN={γrpc,req.(Req_CID),req.(Req_Seq)}=>
    |={⊤∖↑rpcRequestInvN req}=> Q ∗ core_own_ghost server')%I.

(* The above two lemmas should be turned into requirements to apply wp_RPCServer__HandleRequest;
   HandleRequest should prove is_rpcHandler, instead of this wp directly *)
Lemma RPCServer__HandleRequest_is_rpcHandler γrpc args req :
(∀  server,
 {{{
       "Hvol" ∷ core_own_vol server ∗
       "Hpre" ∷ ▷(PreCond)
 }}}
    coreFunction (into_val.to_val args) @ 36; ⊤
 {{{
      server' (r:u64) P', RET #r;
            <disc> (P' ∧ PreCond) ∗
            core_own_vol server' ∗
            <disc> (rpc_commit_fupd γrpc req P' (PostCond r) server server')
 }}}
 {{{
      (PreCond)
 }}}) -∗
(∀ server rpc_server server' rpc_server', {{{
     core_own_vol server' ∗
     RPCServer_own_vol rpc_srv_ptr rpc_server' ∗
     core_own_durable server rpc_server
  }}}
    makeDurable #() @ 36 ; ⊤
  {{{
       RET #();
     core_own_vol server' ∗
     RPCServer_own_vol rpc_srv_ptr rpc_server' ∗
     core_own_durable server' rpc_server'
  }}}
  {{{
    core_own_durable server rpc_server ∨ core_own_durable server' rpc_server'
  }}})-∗

{{{
  "#Hls" ∷ is_server rpc_srv_ptr γrpc
}}}
  RPCServer__HandleRequest #rpc_srv_ptr coreFunction makeDurable
{{{ f, RET f; is_rpcHandler f γrpc args req PreCond PostCond }}}.
Proof.
  iIntros "#HcoreSpec #HdurSpec".

  iIntros (Φ) "!# Hpre HΦ".
  iNamed "Hpre".
  wp_rec.
  wp_pures.
  iApply "HΦ".
  clear Φ.
  iIntros (???? Φ) "!# Hpre HΦ".
  iNamed "Hpre".
  iNamed "Hls".
  wp_loadField.
  wp_apply (crash_lock.acquire_spec with "Hmu"); first done.
  iIntros "Hlocked".
  wp_pures.
  iApply (wpc_wp _ _ _ _ _ True).

  (*
  iDestruct "Hlocked" as "(Hinv & #Hmu_nc & Hlocked)".
  iApply (wpc_na_crash_inv_open with "Hinv"); eauto.
  iSplit; first by iModIntro.
   *)
  wpc_bind_seq.
  crash_lock_open "Hlocked".
  { eauto. }
  { by iModIntro. }
  iIntros ">Hlsown".
  iNamed "Hlsown".
  iNamed "Hrpc". (* Could just keep it unfolded in definition *)
  iNamed "Hargs".

  unfold RPCServer_own_ghost. iNamed "Hrpcghost".
  iCache with "Hcoredurable Hcoreghost Hsrpc".
  { iModIntro. iSplit; first done.
    iNext. by iExists _, _; iFrame.
  }
  wpc_loadField.
  wpc_loadField.

  iNamed "Hrpcvol".
  (* Do loadField on non-readonly ptsto *)
  wpc_bind (struct.loadF _ _ _).
  wpc_frame.
  wp_loadField.
  iNamed 1.

  (* This is the style of the wpc_loadField tactic *)
  wpc_bind (struct.loadF _ _ _).
  wpc_frame_go "HlastSeqOwn" base.Right [INamed "HlastSeqOwn"].
  wp_loadField.
  iNamed 1.

  wpc_apply (CheckReplyTable_spec with "[$Hsrpc $HlastSeqMap $HlastReplyMap $Hreply]"); first eauto.
  {
    iSplit; eauto.
    iDestruct "HSeqPositive" as %?.
    iPureIntro. word.
  }
  iSplit.
  { iModIntro. iIntros. iSplit; first done.
    by iExists _, _; iFrame. }
  iNext.
  iIntros (b reply').
  iNamed 1.

  destruct b.
  - (* Seen request in reply table; easy because we don't touch durable state *)
    wpc_pures.
    iDestruct "Hcases" as "[Hcases|Hcases]".
    { (* Wrong case of postcondition of CheckReplyTable *) 
      iNamed "Hcases"; discriminate. }
    iNamed "Hcases".
    (* Do loadField on non-readonly ptsto *)
    iSplitR "Hcorevol Hcoredurable Hsrpc HlastSeqOwn HlastReplyOwn Hcoreghost HlastSeqMap HlastReplyMap"; last first.
    {
      iNext. iExists _, _; iFrame.
      iExists _, _; iFrame.
    }
    iIntros "Hlocked".
    iSplit.
    { by iModIntro. }
    wpc_pures; first by iModIntro.
    iApply (wp_wpc).
    wp_loadField.
    wp_apply (crash_lock.release_spec with "[$Hlocked]"); first done.
    wp_pures.
    iApply "HΦ".
    iExists _; iFrame.
  - (* Case of actually running core function and updating durable state *)
    wpc_pures.

    iDestruct "Hcases" as "[Hcases | [% _]]"; last discriminate.
    iNamed "Hcases".

    repeat (wpc_bind (struct.loadF _ _ _);
    wpc_frame;
    wp_loadField;
    iNamed 1).
    iMod (server_takes_request with "[] Hsrpc") as "(HγPre & Hpre & Hsrpc_proc)"; eauto.
    wpc_apply ("HcoreSpec" with "[$Hpre $Hcorevol]").
    iSplit.
    {
      iIntros "!> Hpre".
      iSplit; first done.
      iNext.
      iMod (server_returns_request with "[HargsInv] HγPre Hpre Hsrpc_proc") as "Hsrpc"; eauto.
      by iExists _, _; iFrame.
    }
    iNext.
    iIntros (kvserver' retval P').
    iIntros "(HP' & Hkvvol & Hfupd)".
    iCache with "Hcoredurable HγPre HP' Hsrpc_proc Hcoreghost".
    {
      iModIntro.
      iRight in "HP'".
      iSplit; first done.
      iNext.
      iMod (server_returns_request with "HargsInv HγPre HP' Hsrpc_proc") as "Hsrpc"; eauto.
      iModIntro.
      by iExists _, _; iFrame.
    }

    iNamed "Hreply".

    (* wpc_storeField *)
    wpc_bind (struct.storeF _ _ _ _).
    wpc_frame.
    wp_storeField.
    iNamed 1.

    wpc_pures.
    repeat (wpc_bind (struct.loadF _ _ _);
    wpc_frame;
    wp_loadField;
    iNamed 1).

    wpc_bind_seq.
    wpc_frame.
    wp_apply (wp_MapInsert with "HlastReplyMap"); first eauto; iIntros "HlastReplyMap".
    iNamed 1.
    wpc_pures.
    iApply wpc_fupd.
    wpc_apply ("HdurSpec" $! _ rpc_server _ {| lastSeqM := (<[req.(Req_CID):=req.(Req_Seq)]> rpc_server.(lastSeqM)) ;
                                                    lastReplyM := (<[req.(Req_CID):=retval]> rpc_server.(lastReplyM))
                                                 |}
                         with "[-HΦ Hcoreghost Hsrpc_proc HP' HγPre HReplyOwnRet HReplyOwnStale Hfupd]").
    { iFrame. iExists _, _. iFrame. }
    iSplit.
    { (* show that crash condition of makeDurable maintains our crash condition *)
      iModIntro.
      iIntros "Hcoredurable".
      iSplit; first done.

      iDestruct "Hcoredurable" as "[Hcoredurable|Hcoredurable]".
      + iNext.
        iRight in "HP'".
        iMod (server_returns_request with "HargsInv HγPre HP' Hsrpc_proc") as "Hsrpc"; eauto.
        iModIntro. iExists _, _; iFrame.
      + iNext. iLeft in "HP'". iMod (server_executes_durable_request with "HargsInv Hlinv Hsrpc_proc HγPre HP' [Hfupd] Hcoreghost") as "HH".
        { eauto. }
        { iIntros "HP' Hγproc #Hlb Hghost".
          unfold rpc_commit_fupd.
          (* TODO: avoid this unfolding *)
          rewrite rpc_logatom.rpc_atomic_pre_fupd_eq.
          iDestruct ("Hfupd" with "HP' Hghost Hγproc Hlb") as "Hfupd".
          iMod (fupd_mask_subseteq _) as "Hclose"; last iMod "Hfupd" as "[$ Hpre]".
          {
            apply subseteq_difference_r; last set_solver.
            destruct req; simpl.
            symmetry.
            apply rpcReqInvUpToN_prop_2.
            lia.
          }
          iMod "Hclose" as "_".

          iFrame.
        }
        iDestruct "HH" as "(Hreceipt & Hsrpc & Hkvghost)".
        iExists _, _; iFrame "Hcoredurable".
        by iFrame.
    }
    iNext. iIntros "(Hcorevol & Hsrvown & Hcoredurable)".
    iMod (server_executes_durable_request with "HargsInv Hlinv Hsrpc_proc HγPre HP' [Hfupd] Hcoreghost") as "HH"; eauto.
    {
      iIntros "HP' Hγproc #Hlb Hghost".
      iDestruct (own_disc_fupd_elim with "HP'") as ">HP'".
      iLeft in "HP'".
      iDestruct (own_disc_fupd_elim with "Hfupd") as ">Hfupd".

      unfold rpc_commit_fupd.
      (* TODO: avoid this unfolding *)
      rewrite rpc_logatom.rpc_atomic_pre_fupd_eq.
      iDestruct ("Hfupd" with "HP' Hghost Hγproc Hlb") as "Hfupd".
      iMod (fupd_mask_subseteq _) as "Hclose"; last iMod "Hfupd" as "[$ Hpre]".
      {
        apply subseteq_difference_r; last set_solver.
        destruct req; simpl.
        symmetry.
        apply rpcReqInvUpToN_prop_2.
        lia.
      }
      iMod "Hclose" as "_".
      iFrame.
    }
    iDestruct "HH" as "(Hreceipt & Hsrpc & Hcoreghost)".
    iModIntro.
    iSplitR "Hsrvown Hcorevol Hcoredurable Hcoreghost Hsrpc"; last first.
    {
      iNext.
      iExists _, _; iFrame "Hcoredurable".
      iFrame.
    }

    iIntros "Hlocked".
    iSplit; first by iModIntro.
    iApply (wp_wpc).

    wp_pures.
    wp_loadField.
    iApply wp_fupd.
    wp_apply (crash_lock.release_spec with "Hlocked"); first eauto.
    wp_pures.
    iApply "HΦ".
    iModIntro.
    iExists {| Rep_Stale:=_ ; Rep_Ret:=retval |}; iFrame.
Qed.

End rpc_durable_proof.
