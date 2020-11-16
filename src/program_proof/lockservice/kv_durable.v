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
From Perennial.program_proof.lockservice Require Import lockservice_crash rpc rpc_durable nondet kv_proof common_proof fmcounter_map.

Section kv_durable_proof.
Context `{!heapG Σ, !kvserviceG Σ, stagedG Σ}.

Implicit Types (γ : kvservice_names).

Local Notation "k [[ γ ]]↦ '_'" := (∃ v, k [[γ]]↦ v)%I
(at level 20, format "k  [[ γ ]]↦ '_'") : bi_scope.

Record RPCServerC :=
  {
  lastSeqM : gmap u64 u64;
  lastReplyM  : gmap u64 u64;
  }.

Record KVServerC :=
  {
  sv : RPCServerC ;
  kvsM : gmap u64 u64;
  }.

Axiom kvserver_durable_is : KVServerC -> iProp Σ.

Definition RPCServer_mutex_cinv γ : iProp Σ :=
  ∃ kv_server,
  "Hkvdurable" ∷ kvserver_durable_is kv_server
∗ "Hsrpc" ∷ RPCServer_own γ.(ks_rpcGN) kv_server.(sv).(lastSeqM) kv_server.(sv).(lastReplyM)
∗ "Hkvctx" ∷ map_ctx γ.(ks_kvMapGN) 1 kv_server.(kvsM)
.

Definition KVServer_own_core γ (srv:loc) kv_server : iProp Σ :=
  ∃ (kvs_ptr:loc),
  "HlocksOwn" ∷ srv ↦[KVServer.S :: "kvs"] #kvs_ptr
∗ "HkvsMap" ∷ is_map (kvs_ptr) kv_server.(kvsM)
∗ "Hkvctx" ∷ map_ctx γ.(ks_kvMapGN) 1 kv_server.(kvsM)
.

Definition RPCServer_own_phys γrpc (sv:loc) rpc_server : iProp Σ :=
  ∃ (lastSeq_ptr lastReply_ptr:loc),
    "HlastSeqOwn" ∷ sv ↦[RPCServer.S :: "lastSeq"] #lastSeq_ptr
∗ "HlastReplyOwn" ∷ sv ↦[RPCServer.S :: "lastReply"] #lastReply_ptr
∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) rpc_server.(lastSeqM)
∗ "HlastReplyMap" ∷ is_map (lastReply_ptr) rpc_server.(lastReplyM)
∗ ("Hsrpc" ∷ rpc.RPCServer_own γrpc rpc_server.(lastSeqM) rpc_server.(lastReplyM)) (* TODO: Probably should get better naming for this *)
.

(* Note: have to put the entire RPCServer_mutex_inv in a na_crash_inv because the crash obligation RPCServer_mutex_cinv existentially quantifies over both about the rpc state and core state *)

Instance durable_timeless kv_server : Timeless (kvserver_durable_is kv_server).
Admitted.

Instance durable_disc kv_server : Discretizable (kvserver_durable_is kv_server).
Admitted.

Definition RPCServer_mutex_inv srv_ptr sv_ptr γ : iProp Σ :=
  ∃ kv_server,
    "Hkv" ∷ KVServer_own_core γ srv_ptr kv_server ∗
    "Hrpc" ∷ RPCServer_own_phys γ.(ks_rpcGN) sv_ptr kv_server.(sv) ∗
    "Hkvdurable" ∷ kvserver_durable_is kv_server
.

Definition mutexN : namespace := nroot .@ "kvmutexN".

Definition is_kvserver (srv_ptr sv_ptr:loc) γ : iProp Σ :=
  ∃ (mu_ptr:loc),
  "#Hsv" ∷ readonly (srv_ptr ↦[KVServer.S :: "sv"] #sv_ptr) ∗
  "#Hlinv" ∷ is_RPCServer γ.(ks_rpcGN) ∗
  "#Hmu_ptr" ∷ readonly(sv_ptr ↦[RPCServer.S :: "mu"] #mu_ptr) ∗
  "#Hmu" ∷ is_crash_lock mutexN 37 #mu_ptr (RPCServer_mutex_inv srv_ptr sv_ptr γ)
    (RPCServer_mutex_cinv γ)
.

Definition own_kvclerk γ ck_ptr srv : iProp Σ :=
  ∃ (cl_ptr:loc),
   "Hcl_ptr" ∷ ck_ptr ↦[KVClerk.S :: "client"] #cl_ptr ∗
   "Hprimary" ∷ ck_ptr ↦[KVClerk.S :: "primary"] #srv ∗
   "Hcl" ∷ own_rpcclient cl_ptr γ.(ks_rpcGN).

Lemma CheckReplyTable_spec (reply_ptr:loc) (req:Request64) (reply:Reply64) γ (lastSeq_ptr lastReply_ptr:loc) lastSeqM lastReplyM :
{{{
     "%" ∷ ⌜int.nat req.(rpc.Seq) > 0⌝
    ∗ "#Hrinv" ∷ is_RPCServer γ.(ks_rpcGN)
    ∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM
    ∗ "HlastReplyMap" ∷ is_map (lastReply_ptr) lastReplyM
    ∗ ("Hsrpc" ∷ RPCServer_own γ.(ks_rpcGN) lastSeqM lastReplyM)
    ∗ ("Hreply" ∷ own_reply reply_ptr reply)
}}}
CheckReplyTable #lastSeq_ptr #lastReply_ptr #req.(CID) #req.(rpc.Seq) #reply_ptr @ NotStuck ; 36; ⊤
{{{
     (b:bool) reply', RET #b;
      "Hreply" ∷ own_reply reply_ptr reply'
    ∗ "Hcases" ∷ ("%" ∷ ⌜b = false⌝
         ∗ "%" ∷ ⌜(int.Z req.(rpc.Seq) > int.Z (map_get lastSeqM req.(CID)).1)%Z⌝
         ∗ "%" ∷ ⌜reply'.(Stale) = false⌝
         ∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) (<[req.(CID):=req.(rpc.Seq)]>lastSeqM)
         ∨ 
         "%" ∷ ⌜b = true⌝
         ∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM
         ∗ ((⌜reply'.(Stale) = true⌝ ∗ RPCRequestStale γ.(ks_rpcGN) req)
          ∨ RPCReplyReceipt γ.(ks_rpcGN) req reply'.(Ret)))

    ∗ "HlastReplyMap" ∷ is_map (lastReply_ptr) lastReplyM
    ∗ ("Hsrpc" ∷ RPCServer_own γ.(ks_rpcGN) lastSeqM lastReplyM)
}}}
{{{
    RPCServer_own γ.(ks_rpcGN) lastSeqM lastReplyM
}}}
.
Proof.
  iIntros (Φ Φc) "Hpre Hpost".
  iNamed "Hpre".
  wpc_call.
  { iNext. iFrame. }
  { iNext. iFrame. }
  iCache with "Hsrpc Hpost".
  { iDestruct "Hpost" as "[Hpost _]". iModIntro. iNext. by iApply "Hpost". }
  wpc_pures.
  iApply wpc_fupd.
  wpc_frame.
  wp_apply (wp_MapGet with "HlastSeqMap").
  iIntros (v ok) "(HSeqMapGet&HlastSeqMap)"; iDestruct "HSeqMapGet" as %HSeqMapGet.
  wp_pures.
  iNamed "Hreply".
  wp_storeField.
  wp_apply (wp_and ok (int.Z req.(rpc.Seq) ≤ int.Z v)%Z).
  { wp_pures. by destruct ok. }
  { iIntros "_". wp_pures. done. }
  rewrite bool_decide_decide.
  destruct (decide (ok ∧ int.Z req.(rpc.Seq) ≤ int.Z v)%Z) as [ [Hok Hineq]|Hmiss].
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
      { eauto with iFrame. instantiate (1:={| Ret:=_; Stale:=_ |}).
        iFrame. }
      iFrame; iFrame "#".
      iRight.
      eauto with iFrame.
    - wp_pures.
      assert (v = req.(rpc.Seq)) as ->. {
        (* not strict + non-strict ineq ==> eq *)
        apply bool_decide_eq_false in Hineqstrict.
        assert (int.Z req.(rpc.Seq) = int.Z v) by lia; word.
      }
      wp_apply (wp_MapGet with "HlastReplyMap").
      iIntros (reply_v reply_get_ok) "(HlastReplyMapGet & HlastReplyMap)"; iDestruct "HlastReplyMapGet" as %HlastReplyMapGet.
      wp_storeField.
      iNamed 1.
      iMod (server_replies_to_request with "[Hrinv] [Hsrpc]") as "[#Hreceipt Hsrpc]"; eauto.
      iApply "Hpost".
      iModIntro.
      iSplitL "HReplyOwnStale HReplyOwnRet".
      { eauto with iFrame. instantiate (1:={| Ret:=_; Stale:=_ |}).
        iFrame. }
      iFrame.
      iRight.
      by iFrame; iFrame "#".
  }
  { (* Cache miss *)
    wp_pures.
    apply not_and_r in Hmiss.
    wp_apply (wp_MapInsert _ _ lastSeqM _ req.(rpc.Seq) (#req.(rpc.Seq)) with "HlastSeqMap"); eauto.
    iIntros "HlastSeqMap".
    wp_seq.
    iNamed 1.
    iDestruct "Hpost" as "[_ Hpost]".
    iApply ("Hpost" $! _ ({| Stale:=false; Ret:=reply.(Ret) |}) ).
    iModIntro.
    iFrame; iFrame "#".
    iLeft. iFrame. iPureIntro.
    split; eauto. split; eauto. injection HSeqMapGet as <- Hv. simpl.
    destruct Hmiss as [Hnok|Hineq].
    - destruct ok; first done.
      destruct (lastSeqM !! req.(CID)); first done.
      simpl. word.
    - word.
  }
Qed.

Variable coreFunction:goose_lang.val.
Variable PreCond:RPCValC -> iProp Σ.
Variable PostCond:RPCValC -> u64 -> iProp Σ.

Lemma RPC_core_spec_example R (args:RPCValC) :
  {{{
       "HR" ∷ R ∗
       "#HgetP" ∷ □(R ={⊤, ⊤ ∖ ↑rpcRequestInvN }=∗ ▷ PreCond args ∗ (▷ PreCond args ={⊤ ∖ ↑rpcRequestInvN, ⊤}=∗ R))
 }}}
    coreFunction (into_val.to_val args) @ NotStuck ; 36; ⊤
 {{{
      (r:u64), RET #r; R ∗ (PreCond args ==∗ PostCond args r)
 }}}
 {{{
      R
 }}}
.
Admitted.

Lemma RPCServer__HandleRequest_spec' (makeDurable:goose_lang.val) (srv sv req_ptr reply_ptr:loc) (req:Request64) (reply:Reply64) γ γPost :
{{{
  "#Hls" ∷ is_kvserver srv sv γ
  ∗ "#HreqInv" ∷ is_durable_RPCRequest γ.(ks_rpcGN) γPost PreCond PostCond req
  ∗ "#Hreq" ∷ read_request req_ptr req
  ∗ "Hreply" ∷ own_reply reply_ptr reply
}}}
  RPCServer__HandleRequest #sv coreFunction makeDurable #req_ptr #reply_ptr
{{{ RET #false; ∃ reply':Reply64, own_reply reply_ptr reply'
    ∗ ((⌜reply'.(Stale) = true⌝ ∗ RPCRequestStale γ.(ks_rpcGN) req)
  ∨ RPCReplyReceipt γ.(ks_rpcGN) req reply'.(Ret))
}}}.
Proof.
  iIntros (Φ) "Hpre Hpost".
  iNamed "Hpre".
  wp_lam.
  wp_pures.
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
  iNamed "Hkv". iNamed "Hrpc".
  iNamed "Hreq".
  iCache with "Hkvdurable Hkvctx Hsrpc".
  { iModIntro; iNext. iSplit; first done.
    iExists _; iFrame.
  }
  wpc_loadField.
  wpc_loadField.

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

  (* TODO: understand exactly what's going on here *)
  wpc_apply (CheckReplyTable_spec with "[$Hsrpc $HlastSeqMap $HlastReplyMap $Hreply]"); first eauto.
  iSplit.
  { iModIntro. iNext. iIntros. iSplit; first done.
    iExists _; iFrame. }
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
    iSplitR "HlocksOwn HkvsMap Hkvdurable Hsrpc HlastSeqOwn HlastReplyOwn Hkvctx HlastSeqMap HlastReplyMap"; last first.
    {
      iNext. iExists _; iFrame. unfold KVServer_own_core.
      iSplitL "HlocksOwn HkvsMap".
      - iExists _; iFrame.
      - iExists _, _; iFrame.
    }
    iIntros "Hlocked".
    iSplit.
    { by iModIntro. }
    wpc_pures; first by iModIntro.
    iApply (wp_wpc).
    wp_loadField.
    wp_apply (crash_lock.release_spec with "[$Hlocked]"); first done.
    wp_pures.
    iApply "Hpost".
    iExists _; iFrame.
  - (* Case of actually running core function and updating durable state *)
    wpc_pures.

    iDestruct "Hcases" as "[Hcases | [% _]]"; last discriminate.
    iNamed "Hcases".

    repeat (wpc_bind (struct.loadF _ _ _);
    wpc_frame;
    wp_loadField;
    iNamed 1).
    wpc_apply (RPC_core_spec_example (RPCServer_own γ.(ks_rpcGN) kv_server.(kv_durable_proof.sv).(lastSeqM) kv_server.(kv_durable_proof.sv).(lastReplyM))
                 with "[Hsrpc]").
    {
      iSplitL "Hsrpc".
      { iFrame "Hsrpc". }
      iModIntro.
      iIntros "Hrpcs_own".
      iInv "HreqInv" as "Hrinv" "Hrclose".
      iDestruct "Hrinv" as "[Hlseqbound [Hrinv|Hproc]]".
      { admit. }
      {
        iAssert (▷ req.(CID) fm[[γ.(ks_rpcGN).(lseq)]]≥ int.nat req.(Seq))%I with "[Hproc]" as "#>Hlseq_lb".
        { iDestruct "Hproc" as "[Hlseq_lb _]"; done. }
        iNamed "Hrpcs_own".
        rewrite map_get_val in H1.
        iDestruct (big_sepS_elem_of_acc_impl req.(CID) with "Hlseq_own") as "[Hlseq_one Hlseq_own]";
          first by apply elem_of_fin_to_set.
        iDestruct (fmcounter_map_agree_lb with "Hlseq_one Hlseq_lb") as %Hlseq_lb_ineq.
        iExFalso; iPureIntro.
        simpl in H1.
        replace (int.Z req.(Seq)) with (Z.of_nat (int.nat req.(Seq))) in Hlseq_lb_ineq; last by apply u64_Z_through_nat.
        admit.
        (* lia. *)
      }
    }
   iSplit.
    {
      iModIntro. iNext. iIntros "Hsrpc".
      iSplit; first done.
      iExists _; iFrame.
    }
    iIntros (v).
    iNext.
    iIntros "[Hsrpc Hfupd]".

    (* wpc_loadField. *)
    wpc_bind (struct.storeF _ _ _ _).
    wpc_frame.
    (*
    wp_storeField.
    iNamed 1).
     *)

   (*
    wpc_bind (struct.loadF _ _ _).
    wpc_frame.
    wp_loadField.
    iNamed 1.

    iDestruct (na_crash_inv_alloc 36 ⊤ (RPCServer_mutex_cinv γ) (RPCServer_mutex_inv srv sv γ) with "[] []") as "HH".
    { admit. }
    { admit. }
    iMod (fupd_level_fupd with "HH") as "(Hfull&?)".
    wpc_frame.
    wp_apply (crash_lock.release_spec with "[$Hmu_nc $Hlocked $Hfull]"); first eauto.
    wp_seq.
    iNamed 1.
*)
Admitted.

End kv_proof.
