From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import disk_prelude marshal_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Goose.github_com.mit_pdos.lockservice Require Import lockservice.
From Perennial.program_proof.lockservice Require Import rpc_logatom rpc fmcounter_map wpc_proofmode common_proof rpc_proof rpc_durable_proof.
Require Import Decimal Ascii String DecimalString.
From Perennial.program_proof.lockservice Require Import grove_ffi.

Section rpc_proof.
Context `{!heapGS Σ}.
Context `{!rpcG Σ u64}.

Definition is_rpcHandler' f γrpc cid args PreCond PostCond : iProp Σ :=
  □(∀ seqno Q,
        □(▷ Q -∗ ◇ Q) -∗
        □(Q -∗ <disc> Q) -∗
        □(▷ Q -∗ |RN={γrpc,cid,seqno}=> PreCond) -∗
        is_rpcHandler f γrpc args {| Req_CID:=cid; Req_Seq:=seqno |} Q PostCond).

Definition own_rpcclient_cid (cl_ptr:loc) (γrpc:rpc_names) (cid:u64) : iProp Σ
  :=
    ∃ (cseqno:u64),
      "%" ∷ ⌜int.nat cseqno > 0⌝
    ∗ "Hcid" ∷ cl_ptr ↦[RPCClient :: "cid"] #cid
    ∗ "Hseq" ∷ cl_ptr ↦[RPCClient :: "seq"] #cseqno
    ∗ "Hcrpc" ∷ RPCClient_own γrpc cid cseqno
.

Lemma wpc_RPCClient__MakeRequest k (f:goose_lang.val) cl_ptr cid γrpc args (PreCond:iProp Σ) PostCond {_:Discretizable (PreCond)} {_:∀ reply, Discretizable (PostCond reply)}:
  is_rpcHandler' f γrpc cid args PreCond PostCond -∗
  {{{
    |PN={γrpc,cid}=> PreCond ∗
    own_rpcclient_cid cl_ptr γrpc cid ∗
    is_RPCServer γrpc
  }}}
    RPCClient__MakeRequest #cl_ptr f (into_val.to_val args) @ k ; ⊤
  {{{ (retv:u64), RET #retv; own_rpcclient_cid cl_ptr γrpc cid ∗ ▷ PostCond retv }}}
  {{{ |={⊤}=> |PN={γrpc,cid}=> (▷ PreCond ∨ ▷ (∃ ret, PostCond ret)) }}}.
Proof using Type*.
  iIntros "#Hfspec" (Φ Φc) "!# [Hpre [Hclerk #Hlinv]] HΦ".
  iNamed "Hclerk".

  iCache with "Hpre HΦ".
  { (* Use PreCond to show idemp_fupd *)
    iDestruct "HΦ" as "[HΦc _]".
    iModIntro.
    iApply "HΦc".
    iModIntro.
    iModIntro.
    iFrame.
  }
  wpc_rec _.
  { iFromCache. }

  iCache with "Hpre HΦ".
  { (* repeat crash proof *)
    iDestruct "HΦ" as "[HΦc _]".
    iModIntro.
    iApply "HΦc".
    iModIntro.
    iModIntro.
    iFrame.
  }
  wpc_pures.
  wpc_loadField.
  wpc_wpapply (overflow_guard_incr_spec).
  iIntros (HincrSafe).
  iNamed 1.

  wpc_pures.
  wpc_loadField.
  wpc_loadField.

  wpc_pures.
  wpc_wpapply (wp_allocStruct); first eauto.
  iIntros (req_ptr) "Hreq".
  iNamed 1.
  iDestruct (struct_fields_split with "Hreq") as "(HCID&HSeq&HArgs&_)".
  iMod (readonly_alloc_1 with "HCID") as "#HCID".
  iMod (readonly_alloc_1 with "HSeq") as "#HSeq".
  iMod (readonly_alloc_1 with "HArgs") as "#HArgs".

  wpc_pures.
  wpc_loadField.
  wpc_pures.
  wpc_storeField.
  wpc_pures.
  wpc_wpapply wp_ref_to; first eauto.
  iIntros (errb_ptr) "Herrb_ptr".
  iNamed 1.

  wpc_pures.
  wpc_wpapply (wp_allocStruct); first eauto.
  iIntros (reply_ptr) "Hreply".
  iNamed 1.
  wpc_pures.
  iDestruct (fmcounter_map_get_lb with "Hcrpc") as "#Hcseqno_lb".
  iDestruct (post_neutralize_instantiate with "Hcrpc Hpre") as ">[Hcrpc Hrnfupd]".

  iDestruct (rnfupd_disc_laterable with "Hrnfupd") as (Q) "(HQ&#HQtmlss&#HQdisc&#HQwand)".
  iMod (make_request {| Req_CID:=cid; Req_Seq:=cseqno|} Q PostCond with "[Hlinv] [Hcrpc] [HQ]") as "[Hcseq_own HallocPost]"; eauto.
  { simpl. word. }
  iDestruct "HallocPost" as (γP) "[#Hreqinv_init HγP]".
  (* Prepare the loop invariant *)
  iAssert (∃ (err:bool), errb_ptr ↦[boolT] #err)%I with "[Herrb_ptr]" as "Herrb_ptr".
  { iExists _. done. }
  iAssert (∃ reply', own_reply reply_ptr reply')%I with "[Hreply]" as "Hreply".
  { iDestruct (struct_fields_split with "Hreply") as "(?& ? & _)".
    iExists {| Rep_Ret:=_; Rep_Stale:=false |}. iFrame. }

  wpc_bind (For _ _ _). iApply (wpc_forBreak_cond_2 with "[-]").
  { by iNamedAccu. }
  {
    iNamed 1.
    iDestruct "HΦ" as "[HΦc _]".
    iModIntro.
    iApply "HΦc".
    iDestruct (neutralize_request with "Hlinv Hreqinv_init HγP") as ">Hpnfupd".
    { simpl. word. }
    iDestruct (own_disc_fupd_elim with "Hpnfupd") as ">Hpnfupd".
    iModIntro.
    iDestruct (neutralize_idemp γrpc cid with "Hcseqno_lb HQwand Hpnfupd") as "$".
  }
  {
    iIntros "!# __CTX"; iNamed "__CTX".

    iCache with "HγP HΦ".
    {
      iDestruct "HΦ" as "[HΦc _]".
      iModIntro. iApply "HΦc".
      iDestruct (neutralize_request with "Hlinv Hreqinv_init HγP") as ">Hpnfupd".
      { simpl. word. }
      iDestruct (own_disc_fupd_elim with "Hpnfupd") as ">Hpnfupd".
      iModIntro.
      iDestruct (neutralize_idemp γrpc cid with "Hcseqno_lb HQwand Hpnfupd") as "$".
    }

    iDestruct "Hreply" as (reply') "Hreply".
    wpc_pures.
    wpc_bind (RemoteProcedureCall _ _ _). wpc_frame.
    wp_apply (RemoteProcedureCall_spec with "[] [$Hreply]").
    { iDestruct ("Hfspec" $! cseqno Q with "HQtmlss HQdisc HQwand") as "$". }
    {
      iSplit; last first.
      { unfold read_request.
        iFrame "#∗".
        simpl. iPureIntro. lia.
      }
      iFrame "Hreqinv_init".
    }
    iIntros (v) "Hrpc_post". iNamed 1.
    iDestruct "Herrb_ptr" as (err') "Herrb_ptr".

    iDestruct "Hrpc_post" as (reply) "[Hreply [#Hre | [#Hre HCallPost]]]".
    {
      iDestruct "Hre" as %->.

      wpc_bind (store_ty _ _).
      wpc_frame.
      wp_store.
      iNamed 1.
      wpc_pures.
      wpc_bind (load_ty _ _).
      wpc_frame.
      wp_load.
      iNamed 1.
      wpc_pures.
      iLeft.
      iFrame.
      iSplitL ""; first done.
      iSplitL "Herrb_ptr"; eauto.
    }

    iDestruct "Hre" as %->.

    wpc_bind (store_ty _ _).
    wpc_frame.
    wp_store.
    iNamed 1.

    wpc_pures.

    wpc_bind (load_ty _ _).
    wpc_frame.
    wp_load.
    iNamed 1.

    iApply wpc_fupd.
    wpc_pures.
    iRight.
    iSplitL ""; first by iModIntro.

    iDestruct "HCallPost" as "[ [_ Hbad] | #Hrcptstoro]"; simpl.
    {
      iDestruct (client_stale_seqno with "Hbad Hcseq_own") as %bad. exfalso.
      simpl in bad. replace (int.nat (word.add cseqno 1))%nat with (int.nat cseqno + 1)%nat in bad by word.
      lia.
    }

    iModIntro.
    iSplit; last first.
    {
      iLeft in "HΦ". iModIntro.
      iApply "HΦ".
      iDestruct (neutralize_request with "Hlinv Hreqinv_init HγP") as ">Hpnfupd".
      { simpl. word. }
      iDestruct (own_disc_fupd_elim with "Hpnfupd") as ">Hpnfupd".
      iModIntro.
      iDestruct (neutralize_idemp γrpc cid with "Hcseqno_lb HQwand Hpnfupd") as "$".
    }

    wpc_pures.
    iNamed "Hreply".
    replace (RPCReply) with (lockservice_nocrash.RPCReply) by done.
    replace (lockservice_nocrash.RPCReply) with (RPCReply) by done.

    iApply wpc_fupd.
    wpc_frame.
    wp_loadField.
    iNamed 1.

    iMod (get_request_post with "Hreqinv_init Hrcptstoro HγP") as "HP"; first done.
    simpl.
    iModIntro.
    iRight in "HΦ".
    iApply "HΦ".
    iFrame.
    iExists _; iFrame.
    iPureIntro.
    word.
  }
Qed.

End rpc_proof.
