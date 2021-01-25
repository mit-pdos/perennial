From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import proof_prelude marshal_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Goose.github_com.mit_pdos.lockservice Require Import lockservice.
From Perennial.program_proof.lockservice Require Import rpc_proof rpc nondet kv_proof fmcounter_map.
Require Import Decimal Ascii String DecimalString.
From Perennial.goose_lang Require Import ffi.grove_ffi.

Section incr_proof.

(* Proof for increment backed by another increment service
 *)

Context `{!heapG Σ}.
Context `{!filesysG Σ}.

Definition has_encoding_for_short_clerk data cid seq (args:RPCValC) :=
   has_encoding data [EncUInt64 cid ; EncUInt64 seq ; EncUInt64 args.1 ; EncUInt64 args.2.1].

(* TODO: should probably make RPCValC to be nicer than (u64 * (u64 * ())); no need for the unit *)

(* TODO: these definitions should ultimately refer to incr_proof.v *)
Record incrservice_names := KVserviceGN {
  incr_rpcGN : rpc_names;
  (* fmcounter_map of key -> counter value *)
  incr_mapGN : gname;
}.

Axiom is_incrserver : incrservice_names → loc → iProp Σ.

Instance is_incrserver_pers γ incrserver : Persistent (is_incrserver γ incrserver).
Admitted.

Variable γback:incrservice_names.

Context `{!kvserviceG Σ}.

Lemma RPCRequest_merge req cid seq a1 a2:
  req ↦[RPCRequest.S :: "CID"] #cid -∗
  req ↦[RPCRequest.S :: "Seq"] #seq -∗
  req ↦[RPCRequest.S :: "Args"] (#a1, (#a2, #())) -∗
  req ↦[struct.t RPCRequest.S] (#cid, (#seq, ((#a1, (#a2, #())) , #())))
  .
Proof.
  iIntros.
  iApply struct_fields_split.
  iFrame. done.
Qed.

Lemma RPCVals_merge vals a1 a2:
  vals ↦[RPCVals.S :: "U64_1"] #a1 -∗
  vals ↦[RPCVals.S :: "U64_2"] #a2 -∗
  vals ↦[struct.t RPCVals.S] (#a1, (#a2, #()))
  .
Proof.
  iIntros.
  iApply struct_fields_split.
  iFrame. done.
Qed.

Definition own_short_incr_clerk (ck isrv:loc) (cid seq:u64) (args:RPCValC) : iProp Σ :=
  "cid" ∷ ck ↦[ShortTermIncrClerk.S :: "cid"] #cid ∗
  "seq" ∷ ck ↦[ShortTermIncrClerk.S :: "seq"] #seq ∗
  "incrserver" ∷ ck ↦[ShortTermIncrClerk.S :: "incrserver"] #isrv ∗
  "#req" ∷ (* ck ↦[ShortTermIncrClerk.S :: "req"] req_ptr ∗
  "Hread_req" ∷ read_request req_ptr {| Req_CID:=cid; Req_Seq:=seq; Req_Args:=args|} ∗ *)


  (readonly (ck ↦[ShortTermIncrClerk.S :: "req"] (#cid,
                                              (#(word.sub seq 1:u64),
                                              (#args.1, (#args.2.1, #()), #())))))
.

Variable c:nat. (* Old value of the ghost counter *)
Definition IncrPreCond : RPCValC → iProp Σ := (λ a, a.1 fm[[γback.(incr_mapGN)]]↦ c)%I.
Definition IncrPostCond : RPCValC → u64 → iProp Σ := (λ a r, a.1 fm[[γback.(incr_mapGN)]]↦ (c+1))%I.


Definition own_prepared_short_incr_clerk ck isrv cid seq args : iProp Σ :=
  own_short_incr_clerk ck isrv cid seq args ∗
  ⌜(int.nat (word.sub seq 1%nat) > 0)%Z⌝ ∗
  ∃ γPost, is_RPCRequest γback.(incr_rpcGN) γPost IncrPreCond IncrPostCond {| Req_CID:=cid; Req_Seq:=(word.sub seq 1:u64); Req_Args:=args |}
.

(* TODO: this should refer to a lemma in incr_proof.v *)

Lemma IncrServer__Increment_is_rpcHandler (isrv:loc) :
is_incrserver γback isrv -∗
{{{
     True
}}}
  IncrServer__Increment #isrv
{{{ (f:goose_lang.val), RET f;
        is_rpcHandler f γback.(incr_rpcGN) IncrPreCond IncrPostCond
}}}.
Admitted.

Lemma wp_ShortTermIncrClerk__MakePreparedRequest ck isrv cid seq args :
is_incrserver γback isrv -∗
{{{
     own_prepared_short_incr_clerk ck isrv cid seq args
}}}
    ShortTermIncrClerk__MakePreparedRequest #ck
{{{
     (reply':@RPCReply u64), RET #(reply'.(Rep_Ret)); ⌜reply'.(Rep_Stale) = true⌝
               ∗ RPCRequestStale γback.(incr_rpcGN)
                   {| Req_CID := cid; Req_Seq := word.sub seq 1; Req_Args := args |}
               ∨ RPCReplyReceipt γback.(incr_rpcGN)
                   {| Req_CID := cid; Req_Seq := word.sub seq 1; Req_Args := args |}
                   reply'.(Rep_Ret)
}}}
.
Proof using Type*.
  iIntros "#Hs_inv" (Φ) "!# (Hown_ck & %Hseq_ineq & HreqInv) Hpost".
  wp_lam.
  wp_apply wp_ref_to; first eauto.
  iIntros (errb_ptr) "Herrb_ptr".
  wp_pures.
  wp_apply (wp_allocStruct); first eauto.
  iIntros (reply_ptr) "Hreply".
  wp_pures.
  iNamed "HreqInv".
  iDestruct "HreqInv" as "#HreqInv".
  iNamed "Hown_ck".

  iAssert (∃ (err:bool), errb_ptr ↦[boolT] #err)%I with "[Herrb_ptr]" as "Herrb_ptr".
  { iExists _. done. }
  iAssert (∃ reply', own_reply reply_ptr reply')%I with "[Hreply]" as "Hreply".
  { iDestruct (struct_fields_split with "Hreply") as "(?& ? & _)".
    iExists {| Rep_Ret:=_; Rep_Stale:=false |}. iFrame. }

  wp_forBreak.
  iDestruct "Hreply" as (reply) "Hreply".
  wp_pures.

  (* Transform the readonly struct field into a bunch of readonly ptsto for each field via fieldRef *)
  iMod (readonly_load with "req") as (q) "req2".
  wp_apply (wp_struct_fieldRef_mapsto with "req2"); first done.
  iIntros (req) "[%Hacc_req Hreq]".
  iDestruct (struct_fields_split with "Hreq") as "Hreq".
  iNamed "Hreq".
  iMod (readonly_alloc (req ↦[RPCRequest.S :: "CID"] #cid) q with "[CID]") as "#CID"; first eauto.
  iMod (readonly_alloc (req ↦[RPCRequest.S :: "Seq"] #(word.sub seq 1:u64)) q with "[Seq]") as "#Seq"; first eauto.
  iMod (readonly_alloc (req ↦[RPCRequest.S :: "Args"] (into_val.to_val args)) q with "[Args]") as "#Args"; first eauto.

  wp_loadField.
  wp_apply (IncrServer__Increment_is_rpcHandler with "Hs_inv").
  iIntros (f) "#His_rpcHandler".
  wp_apply (RemoteProcedureCall_spec with "His_rpcHandler [$HreqInv $CID $Seq $Args Hreply]").
  {
    Opaque struct.t.
    simpl.
    Transparent struct.t.
    by iFrame.
  }
  iIntros (e) "HrpcPost".
  iDestruct "HrpcPost" as (reply') "[Hown_reply [%He|(%He & HrpcPost)]]".
  - rewrite He. iNamed "Herrb_ptr". wp_store. wp_load. wp_binop. wp_pures.
    iLeft.
    iFrame "#∗".
    iSplitL ""; first done.
    iSplitL "Herrb_ptr".
    { iExists _; iFrame. }
    { iExists _; iFrame. }
  - rewrite He.
    iNamed "Herrb_ptr".
    wp_store. wp_load. wp_binop. wp_pures.
    iRight.
    iSplitL ""; first done.
    wp_pures.
    iNamed "Hown_reply".
    wp_loadField.
    iApply "Hpost".
    iFrame "HrpcPost".
Qed.

Lemma wp_DecodeShortTermIncrClerk cid seq args (isrv:loc) (content:Slice.t) data :
{{{
     is_slice content byteT 1 data ∗
     ⌜has_encoding_for_short_clerk data cid seq args⌝
}}}
  DecodeShortTermIncrClerk #isrv (slice_val content)
{{{
     (ck:loc), RET #ck; own_short_incr_clerk ck isrv cid seq args
}}}.
Proof.
  iIntros (Φ) "[Hslice %Henc] HΦ".
  Opaque struct.t. (* TODO: put this here to avoid unfolding the struct defns all the way *)
  Opaque struct.get.
  wp_lam.
  wp_pures.
  iDestruct "Hslice" as "[Hsmall _]".
  wp_apply (wp_new_dec with "Hsmall"); first done.
  iIntros (decv) "His_dec".
  wp_pures.
  wp_apply (wp_allocStruct); first by apply zero_val_ty'.
  iIntros (ck) "Hck".
  iDestruct (struct_fields_split with "Hck") as "Hck".
  Transparent struct.t.
  iSimpl in "Hck".
  iNamed "Hck".
  Opaque struct.t.
  wp_pures.
  wp_storeField.

  wp_apply (wp_Dec__GetInt with "His_dec").
  iIntros "His_dec".
  wp_storeField.

  wp_apply (wp_Dec__GetInt with "His_dec").
  iIntros "His_dec".
  wp_storeField.

  wp_loadField.

  (* This block of proof writes to a field in a struct contained as a field in another struct *)
  wp_apply (wp_struct_fieldRef_mapsto with "req"); first done.
  iIntros (req) "[%Hacc_req Hreq]".
  symmetry in Hacc_req.
  iDestruct (struct_fields_split with "Hreq") as "Hreq".
  iNamed "Hreq".
  wp_storeField.
  iDestruct (RPCRequest_merge with "CID Seq Args") as "Hreq".
  iDestruct (Hacc_req with "Hreq") as "req".
  clear Hacc_req req.

  wp_loadField.
  wp_binop.

  wp_apply (wp_struct_fieldRef_mapsto with "req"); first done.
  iIntros (req) "[%Hacc_req Hreq]".
  iDestruct (struct_fields_split with "Hreq") as "Hreq".
  iNamed "Hreq".
  wp_storeField.
  iDestruct (RPCRequest_merge with "CID Seq Args") as "Hreq".
  iDestruct (Hacc_req with "Hreq") as "req".
  clear Hacc_req req.

  wp_apply (wp_Dec__GetInt with "His_dec").
  iIntros "His_dec".

  (* TODO: too much copy-paste *)
  (* Open ref to req field in ShortTermIncrClerk *)
  wp_apply (wp_struct_fieldRef_mapsto with "req"); first done.
  iIntros (req) "[%Hacc_req Hreq]".
  iDestruct (struct_fields_split with "Hreq") as "Hreq".
  iNamed "Hreq".
  (* Open ref to args field in RPCRequest *)
  wp_apply (wp_struct_fieldRef_mapsto with "Args"); first done.
  iIntros (Args) "[%Hacc_Args HArgs]".
  iDestruct (struct_fields_split with "HArgs") as "HArgs".
  iNamed "HArgs".
  wp_storeField.
  (* Close ref to args field in RPCRequest *)
  iDestruct (RPCVals_merge with "U64_1 U64_2") as "HArgs".
  iDestruct (Hacc_Args with "HArgs") as "Args".
  clear Hacc_Args Args.
  (* Close ref to req field in ShortTermIncrClerk *)
  iDestruct (RPCRequest_merge with "CID Seq Args") as "Hreq".
  iDestruct (Hacc_req with "Hreq") as "req".
  clear Hacc_req req.

  iApply wp_fupd.
  wp_apply (wp_Dec__GetInt with "His_dec").
  iIntros "His_dec".

  (* Open ref to req field in ShortTermIncrClerk *)
  wp_apply (wp_struct_fieldRef_mapsto with "req"); first done.
  iIntros (req) "[%Hacc_req Hreq]".
  iDestruct (struct_fields_split with "Hreq") as "Hreq".
  iNamed "Hreq".
  (* Open ref to args field in RPCRequest *)
  wp_apply (wp_struct_fieldRef_mapsto with "Args"); first done.
  iIntros (Args) "[%Hacc_Args HArgs]".
  iDestruct (struct_fields_split with "HArgs") as "HArgs".
  iNamed "HArgs".
  wp_storeField.
  (* Close ref to args field in RPCRequest *)
  iDestruct (RPCVals_merge with "U64_1 U64_2") as "HArgs".
  iDestruct (Hacc_Args with "HArgs") as "Args".
  clear Hacc_Args Args.
  (* Close ref to req field in ShortTermIncrClerk *)
  iDestruct (RPCRequest_merge with "CID Seq Args") as "Hreq".
  iDestruct (Hacc_req with "Hreq") as "req".
  clear Hacc_req req.

  iMod (readonly_alloc_1 with "req") as "req".
  iApply "HΦ".
  by iFrame.
Qed.

Variable old_v:u64.
Variable γ:incrservice_names.

Record ProxyServerC :=
  {
  kvsM:gmap u64 u64
  }.

Implicit Types server : ProxyServerC.

Definition ProxyIncrServer_core_own_vol (srv:loc) server : iProp Σ :=
  ∃ (incrserver:loc),
  "Hincrserver" ∷ srv ↦[IncrProxyServer.S :: "incrserver"] #incrserver ∗
  "#His_incrserver" ∷ is_incrserver γback incrserver
.

(* Either the proxy server has the mapsto fact for the backend, or, if it
   doesn't, then it has the  mapsto for γ, meaning backend mapsto is being used
   for a request, and thus belongs to some request's invariant.
 *)
Definition ProxyIncrServer_core_own_ghost server : iProp Σ :=
  "Hctx" ∷ map_ctx γ.(incr_mapGN) 1 server.(kvsM) ∗
  "Hback" ∷ [∗ map] k ↦ v ∈ server.(kvsM), (k [[γback.(incr_mapGN)]]↦ v ∨ k [[γ.(incr_mapGN)]]↦ v)
.

Print RPCClient_own.

Definition ProxyIncrCrashInvariant (sseq:u64) (args:RPCValC) : iProp Σ :=
  ("Hfown_oldv" ∷ ("procy_incr_request_" +:+ u64_to_string sseq) f↦ [] ∗
   "Hmapsto" ∷ args.1 [[γ.(incr_mapGN)]]↦ old_v ) ∨
  ("Hfown_oldv" ∷ ∃ data cid seq, ("procy_incr_request_" +:+ u64_to_string sseq) f↦ data ∗
   ⌜has_encoding_for_short_clerk data cid seq args⌝ ∗
   ⌜(int.nat (word.sub seq 1%nat) > 0)%Z⌝ ∗
   RPCClient_own γback.(incr_rpcGN) cid seq ∗
   ∃ γreq,
     is_RPCRequest γback.(incr_rpcGN) γreq IncrPreCond IncrPostCond {| Req_CID:=cid; Req_Seq:=(word.sub seq 1:u64); Req_Args:=args |}
  )
.

Lemma increment_proxy_core_idempotent (isrv:loc) server (seq:u64) (args:RPCValC) :
  {{{
       ProxyIncrCrashInvariant seq args ∗
       ProxyIncrServer_core_own_vol isrv server ∗
       ProxyIncrServer_core_own_ghost server
  }}}
    IncrProxyServer__proxy_increment_core #isrv #seq (into_val.to_val args) @ 37 ; ⊤
  {{{
      RET #0;
      (
        args.1 [[γ.(incr_mapGN)]]↦ old_v ={⊤}=∗
        args.1 [[γ.(incr_mapGN)]]↦ (U64(int.nat old_v + 1))
      ) ∗
      ProxyIncrCrashInvariant seq args
  }}}
  {{{
       ProxyIncrCrashInvariant seq args ∗
       ProxyIncrServer_core_own_ghost server
  }}}.
Proof.
  Opaque struct.t. (* TODO: put this here to avoid unfolding the struct defns all the way *)
  Opaque zero_val.
  iIntros (Φ Φc) "[HincrCrashInv [Hvol Hghost]] Hpost".
  wpc_call.
  { iFrame. }
  { iFrame. }
  unfold ProxyIncrCrashInvariant.
  iCache with "HincrCrashInv Hghost Hpost".
  {
    iDestruct "Hpost" as "[HΦc _]". iModIntro. iApply "HΦc".
    iFrame.
  }
  wpc_pures.

  wpc_bind (grove_ffi.U64ToString _).
  wpc_frame.
  wp_apply wp_U64ToString.
  iNamed 1.

  wpc_pures.

  wpc_bind (ref _)%E.
  wpc_frame.
  wp_apply (wp_ref_of_zero); first done.
  Transparent zero_val.
  iIntros (ck) "Hck".
  iNamed 1.
  iSimpl in "Hck".

  wpc_pures.

  iDestruct "HincrCrashInv" as "[Hcase|Hcase]".
  - iNamed "Hcase".
    iCache with "Hfown_oldv Hmapsto Hghost Hpost".
    { (* Re-prove crash obligation in the special case. Nothing interesting about this. *)
      iDestruct "Hpost" as "[HΦc _]". iModIntro. iApply "HΦc". iFrame. iLeft.
      iFrame.
    }

    wpc_apply (wpc_Read with "Hfown_oldv").
    iSplit.
    { (* Show that the crash obligation of the function we're calling implies our crash obligation *)
      iDestruct "Hpost" as "[Hpost _]".
      iModIntro. iIntros. iApply "Hpost".
      iFrame. iLeft. iFrame.
    }
    iNext.
    iIntros (content) "[Hcontent_slice Hfown_oldv]".
    wpc_pures.

    wpc_bind (slice.len _).
    wpc_frame.
    wp_apply wp_slice_len.
    iNamed 1.

    wpc_pures.
    iDestruct (slice.is_slice_sz with "Hcontent_slice") as "%Hslice_len".
    simpl in Hslice_len.
    assert (int.Z content.(Slice.sz) = 0) as -> by word.
    destruct bool_decide eqn:Hs.
    {
      apply bool_decide_eq_true in Hs.
      iExFalso; iPureIntro.
      done.
    }

    (* case that no durable short-term clerk was found *)
    wpc_pures.
    admit.
  - iNamed "Hcase".
    iCache with "Hfown_oldv Hghost Hpost".
    { (* Re-prove crash obligation in the special case. Nothing interesting about this. *)
      iDestruct "Hpost" as "[HΦc _]". iModIntro. iApply "HΦc". iFrame.
    }

    iNamed "Hfown_oldv".
    iDestruct "Hfown_oldv" as "(Hfown_oldv & %Henc & %Hpos & Hrpc_clientown & #Hprepared)".
    wpc_apply (wpc_Read with "Hfown_oldv").
    iSplit.
    { (* crash obligation of called implies our crash obligation *)
      iDestruct "Hpost" as "[Hpost _]".
      iModIntro. iIntros. iApply "Hpost". iFrame. iRight.
      by iExists _, _, _; iFrame "#∗".
    }
    iNext.
    iIntros (content) "[Hcontent_slice Hfown_oldv]".

    iCache with "Hfown_oldv Hrpc_clientown Hghost Hprepared Hpost".
    { (* Prove crash obligation after destructing above; TODO: do this earlier *)
      iDestruct "Hpost" as "[HΦc _]". iModIntro. iApply "HΦc". iFrame. iRight.
      by iExists _,_, _; iFrame "#∗".
    }
    wpc_pures.

    wpc_bind (slice.len _)%E.
    wpc_frame.
    wp_apply (wp_slice_len).
    iNamed 1.
    wpc_pures.

    iNamed "Hvol".

    destruct bool_decide eqn:Hlen.
    { (* Case: found old short-term clerk *)
      wpc_pures.

      wpc_bind (struct.loadF _ _ _)%E.
      wpc_frame.
      wp_loadField.
      iNamed 1.

      wpc_bind (DecodeShortTermIncrClerk _ _)%E.
      wpc_frame.
      wp_apply (wp_DecodeShortTermIncrClerk with "[Hcontent_slice]").
      { by iFrame. }
      iIntros (ck_v) "Hown_ck".
      iNamed 1.

      wpc_bind (_ <-[_] _)%E.
      wpc_frame.
      wp_store.
      iNamed 1.

      wpc_pures.

      wpc_bind (![_] _)%E.
      wpc_frame.
      wp_load.
      iNamed 1.

      wpc_bind (ShortTermIncrClerk__MakePreparedRequest #_)%E.
      wpc_frame.
      wp_apply (wp_ShortTermIncrClerk__MakePreparedRequest with "His_incrserver [$Hown_ck $Hprepared]").
      { done. }
      iIntros (v) "HmakeReqPost".
      iNamed 1.

      iDestruct "HmakeReqPost" as "[[% Hstale]|HmakeReqPost]".
      {
        iDestruct (client_stale_seqno with "Hstale Hrpc_clientown") as %Hbad.
        exfalso.
        simpl in Hbad.
        (* Hbad is impossible for *any* u64 *)
        rewrite u64_Z_through_nat in Hbad.
        rewrite Nat2Z.inj_add in Hbad.
        replace (Z.of_nat (int.nat (word.sub seq0 1))) with (int.Z (word.sub seq0 1))%nat in Hbad; last first.
        { by rewrite u64_Z_through_nat. }
        rewrite u64_Z_through_nat in Hpos.

        replace (Z.of_nat 1) with (1%Z) in * by eauto.
        rewrite word.unsigned_sub in Hbad.
        rewrite -unsigned_U64 in Hbad.
        set (n:=int.Z seq0) in *.
        assert (n=int.Z seq0) by eauto.
        assert (n < 2 ^ 64)%Z by word.
        replace (int.Z (1%Z)) with (1)%Z in Hbad by word.
        replace (int.Z (n - 1))%Z with (n - 1%Z)%Z in Hbad by word.
        lia.
      }
      i
      (* TODO: rule out stale case; the word.sub will be annoying, just rewrite
         the crash invariant to not have that *)
      wpc_pures.
      (* TODO: write spec for *)
      admit.
    }
    {
      (* TODO: Use has_encoding_length and is_slize_sz to get contradiction *)
      iExFalso.
      admit.
    }
Admitted.

End incr_proof.
