From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import proof_prelude marshal_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Goose.github_com.mit_pdos.lockservice Require Import lockservice.
From Perennial.program_proof.lockservice Require Import rpc_proof rpc nondet kv_proof fmcounter_map common_proof.
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

  "req" ∷ ((ck ↦[ShortTermIncrClerk.S :: "req"] (#cid,
                                              (#(word.sub seq 1:u64),
                                              (#args.1, (#args.2.1, #()), #()))))) ∗
  "%Hlseq_ineq" ∷ ⌜(int.nat seq > 0)%Z⌝
.

Variable old_v:u64.
Definition IncrPreCond : RPCValC → iProp Σ := (λ a, a.1 [[γback.(incr_mapGN)]]↦ old_v)%I.
Definition IncrPostCond : RPCValC → u64 → iProp Σ := (λ a r, a.1 [[γback.(incr_mapGN)]]↦ (word.add old_v 1))%I.

Definition own_unalloc_prepared_short_incr_clerk ck isrv (cid seq:u64) (args:RPCValC) : iProp Σ :=
  "cid" ∷ ck ↦[ShortTermIncrClerk.S :: "cid"] #cid ∗
  "seq" ∷ ck ↦[ShortTermIncrClerk.S :: "seq"] #seq ∗
  "incrserver" ∷ ck ↦[ShortTermIncrClerk.S :: "incrserver"] #isrv ∗
  "#req" ∷ (readonly (ck ↦[ShortTermIncrClerk.S :: "req"] (#cid,
                                              (#(word.sub seq 1:u64),
                                              (#args.1, (#args.2.1, #()), #()))))) ∗
  "%Hlseq_ineq" ∷ ⌜(int.nat (word.sub seq 1) > 0)%Z⌝
.

Definition own_alloc_prepared_short_incr_clerk ck isrv (cid seq:u64) (args:RPCValC) : iProp Σ :=
  "Hown" ∷ own_unalloc_prepared_short_incr_clerk ck isrv cid seq args ∗
  "#HreqInv" ∷ ∃ γPost, is_RPCRequest γback.(incr_rpcGN) γPost IncrPreCond IncrPostCond {| Req_CID:=cid; Req_Seq:=(word.sub seq 1:u64); Req_Args:=args |}
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
     own_alloc_prepared_short_incr_clerk ck isrv cid seq args
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
  iIntros "#Hs_inv" (Φ) "!# Hown_ck Hpost".
  iNamed "Hown_ck".
  iNamed "Hown".
  wp_lam.
  wp_apply wp_ref_to; first eauto.
  iIntros (errb_ptr) "Herrb_ptr".
  wp_pures.
  wp_apply (wp_allocStruct); first eauto.
  iIntros (reply_ptr) "Hreply".
  wp_pures.
  iNamed "HreqInv".
  iDestruct "HreqInv" as "#HreqInv".

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

Lemma wp_EncodeShortTermIncrClerk ck cid seq args (isrv:loc) :
{{{
     own_unalloc_prepared_short_incr_clerk ck isrv cid seq args
}}}
  EncodeShortTermIncrClerk #ck
{{{
     content data, RET (slice_val content);
     is_slice content byteT 1 data ∗
     ⌜has_encoding_for_short_clerk data cid seq args⌝ ∗
     ⌜(int.nat seq > 0)%Z⌝
     (* TODO: could put the > 0 in the has_encoding_for_short_clerk predicate *)
}}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".

  wp_lam.
  (* TODO: finish encoding proof *)
Admitted.

Lemma wp_DecodeShortTermIncrClerk cid seq args (isrv:loc) (content:Slice.t) data :
{{{
     is_slice content byteT 1 data ∗
     ⌜has_encoding_for_short_clerk data cid seq args⌝ ∗
     ⌜(int.nat (word.sub seq 1) > 0)%Z⌝
}}}
  DecodeShortTermIncrClerk #isrv (slice_val content)
{{{
     (ck:loc), RET #ck; own_unalloc_prepared_short_incr_clerk ck isrv cid seq args
}}}.
Proof.
  iIntros (Φ) "(Hslice & %Henc & %Hlseq_ineq) HΦ".
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
  iFrame.
  iPureIntro; lia.
Qed.

Lemma wp_PrepareRequest (ck isrv:loc) (args args_dummy:RPCValC) cid seq:
{{{
     own_short_incr_clerk ck isrv cid seq args_dummy
}}}
  ShortTermIncrClerk__PrepareRequest #ck (into_val.to_val args)
{{{
     RET #();
     own_unalloc_prepared_short_incr_clerk ck isrv cid (word.add seq 1) args
}}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iApply wp_fupd.
  wp_lam.
  wp_pures.
  iNamed "Hpre".
  wp_loadField.
  wp_apply (overflow_guard_incr_spec).
  iIntros (Hoverflow).
  wp_pures.
  wp_loadField.
  wp_loadField.
  wp_apply (wp_storeField with "req").
  { admit. } (* TODO: Typecheck *)
  iIntros "req".
  wp_pures.
  wp_loadField.
  wp_storeField.
  iMod (readonly_alloc_1 with "req") as "#req".
  iApply "HΦ".
  iFrame "#∗".
  replace (Z.of_nat 1%nat) with (1)%Z by lia.
  replace (word.sub (word.add seq 1%Z) 1%Z) with (seq); last by rewrite word.word_sub_add_l_same_r.
  by iFrame "req".
Admitted.

Variable γ:incrservice_names.

Record ProxyServerC :=
  {
  kvsM:gmap u64 u64 ;
  lastCID:u64
  }.

Implicit Types server : ProxyServerC.

Definition ProxyIncrServer_core_own_vol (srv:loc) server : iProp Σ :=
  ∃ (incrserver:loc),
  "Hincrserver" ∷ srv ↦[IncrProxyServer.S :: "incrserver"] #incrserver ∗
  "HlastCID" ∷ srv ↦[IncrProxyServer.S :: "lastCID"] #(server.(lastCID)) ∗
  "#His_incrserver" ∷ is_incrserver γback incrserver
.

(* Either the proxy server has the mapsto fact for the backend, or, if it
   doesn't, then it has the  mapsto for γ, meaning backend mapsto is being used
   for a request, and thus belongs to some request's invariant.
 *)
Definition ProxyIncrServer_core_own_ghost server : iProp Σ :=
  "Hctx" ∷ map_ctx γ.(incr_mapGN) 1 server.(kvsM) ∗
  "Hback" ∷ ([∗ map] k ↦ v ∈ server.(kvsM), (k [[γback.(incr_mapGN)]]↦ v ∨ k [[γ.(incr_mapGN)]]↦{1/2} v)) ∗
  "HownCIDs" ∷ ([∗ set] cid ∈ (fin_to_set u64), RPCClient_own γ.(incr_rpcGN) cid 0 ∨ ⌜int.Z cid < int.Z server.(lastCID)⌝%Z) ∗
  "Hfown_lastCID" ∷ (∃ data, "lastCID" f↦ data ∗ ⌜has_encoding data [EncUInt64 server.(lastCID)]⌝)
.

(* TODO: make this a wpc, since it owns ghost state *)
Lemma wp_MakeFreshIncrClerk (isrv:loc) server :
  {{{
      ProxyIncrServer_core_own_vol isrv server ∗
      ProxyIncrServer_core_own_ghost server
  }}}
    IncrProxyServer__MakeFreshIncrClerk #isrv
  {{{
      cid args seq (ck:loc), RET #ck; own_short_incr_clerk ck isrv cid seq args ∗
      RPCClient_own γback.(incr_rpcGN) cid seq
  }}}.
Proof.
  iIntros (Φ) "[Hvol Hghost] HΦ".
  iNamed "Hvol".
  iNamed "Hghost".
  wp_lam.
  wp_loadField.
  wp_pures.
  wp_loadField.
  wp_apply (overflow_guard_incr_spec).
  iIntros (HincrSafe).
  wp_pures.
  wp_loadField.
  wp_storeField.
  wp_apply (wp_new_enc).
  iIntros (enc_v) "Henc".
  wp_pures.
  wp_loadField.
  wp_apply (wp_Enc__PutInt with "Henc"); first done.
  iIntros "Henc".
  wp_pures.
  iDestruct "Hfown_lastCID" as (old_data) "[Hfown_lastCID %Hold_encoding]".
  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (content data) "(%Hencoding & %Hlength & Hcontent_slice)". simpl.

  wp_bind (Write _ _).
  Check wpc_wp.
  iApply (wpc_wp _ _ _ _ _ True).
  iApply (wpc_Write with "[$Hfown_lastCID $Hcontent_slice]").
  iSplit.
  { iModIntro. iIntros. done. }
  iNext.
  iIntros "Hfown_lastCID".

  wp_pures.
  wp_loadField.
  wp_pures.
Admitted.

Definition ProxyIncrCrashInvariant (sseq:u64) (args:RPCValC) : iProp Σ :=
  ("Hfown_oldv" ∷ ("procy_incr_request_" +:+ u64_to_string sseq) f↦ [] ∗
   "Hmapsto" ∷ args.1 [[γ.(incr_mapGN)]]↦ old_v ) ∨
  ("Hfown_oldv" ∷ ∃ data cid seq γreq, ("procy_incr_request_" +:+ u64_to_string sseq) f↦ data ∗
   "Hmapsto" ∷ args.1 [[γ.(incr_mapGN)]]↦{1/2} old_v ∗
   ⌜has_encoding_for_short_clerk data cid seq args⌝ ∗
   ⌜(int.nat (word.sub seq 1) > 0)%Z⌝ ∗
   RPCClient_own γback.(incr_rpcGN) cid seq ∗
   RPCRequest_token γreq ∗
   is_RPCRequest γback.(incr_rpcGN) γreq IncrPreCond IncrPostCond {| Req_CID:=cid; Req_Seq:=(word.sub seq 1:u64); Req_Args:=args |}
  )
.

Lemma increment_proxy_core_idempotent (isrv:loc) server (seq:u64) (args:RPCValC) :
is_RPCServer γback.(incr_rpcGN) -∗
  {{{
       ProxyIncrCrashInvariant seq args ∗
       ProxyIncrServer_core_own_vol isrv server ∗
       ProxyIncrServer_core_own_ghost server
  }}}
    IncrProxyServer__proxy_increment_core #isrv #seq (into_val.to_val args) @ 37 ; ⊤
  {{{
      SP server', RET #0;
      ProxyIncrServer_core_own_vol isrv server' ∗
      <disc> (SP ∧ ProxyIncrCrashInvariant seq args) ∗
      <disc> (
        ProxyIncrServer_core_own_ghost server -∗
        SP ={⊤}=∗
        ProxyIncrServer_core_own_ghost server' ∗
        args.1 [[γ.(incr_mapGN)]]↦ (word.add old_v 1)
      )
  }}}
  {{{
       |={⊤}=> ProxyIncrCrashInvariant seq args ∗
       ProxyIncrServer_core_own_ghost server
       (* Need this fupd because we need to use an invariant right after destructing into cases and right when trying to prove crash condition *)
  }}}.
Proof.
  Opaque struct.t. (* TODO: put this here to avoid unfolding the struct defns all the way *)
  Opaque zero_val.
  iIntros "#Hrpcsrv".
  iIntros (Φ Φc) "!# [HincrCrashInv [Hvol Hghost]] Hpost".
  wpc_call.
  { by iFrame. }
  { by iFrame. }
  iCache with "HincrCrashInv Hghost Hpost".
  {
    iDestruct "Hpost" as "[HΦc _]". iModIntro. iApply "HΦc".
    by iFrame.
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
      by iFrame.
    }

    wpc_apply (wpc_Read with "Hfown_oldv").
    iSplit.
    { (* Show that the crash obligation of the function we're calling implies our crash obligation *)
      iDestruct "Hpost" as "[Hpost _]".
      iModIntro. iIntros. iApply "Hpost".
      iFrame. iLeft. by iFrame.
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
    wpc_pures.

    wpc_bind (App _ #_)%E. wpc_frame.
    wp_apply (wp_MakeFreshIncrClerk).
    iIntros (cid args_dummy seq_init ck_ptr) "[Hownclerk Hrpcclient_own]".
    iNamed 1.
    iNamed "Hownclerk". (* Need to know that seq_init > 0 from here *)

    wpc_bind (store_ty _ _); wpc_frame.
    wp_store. iNamed 1.

    wpc_pures.

    wpc_bind (load_ty _ _); wpc_frame.
    wp_load. iNamed 1.

    wpc_bind (App _ #ck_ptr _)%E.
    wpc_frame.
    wp_apply (wp_PrepareRequest with "[cid seq incrserver req]").
    {
      iFrame. done.
    }
    iIntros "Hownclerk".
    iNamed 1.

    wpc_pures.

    wpc_bind (load_ty _ _); wpc_frame.
    wp_load. iNamed 1.

    wpc_bind (EncodeShortTermIncrClerk _). wpc_frame.
    wp_apply (wp_EncodeShortTermIncrClerk with "[$Hownclerk]").

    iIntros (content2 data2) "(Hcontent2_slice & %Henc)".
    iNamed 1.

    destruct Henc as [Henc Hineq].

    wpc_pures.
    wpc_apply (wpc_Write with "[$Hfown_oldv $Hcontent2_slice]").
    iSplit.
    { (* Prove that crash obligation of Write implies our crash obligation. *)
      iDestruct "Hpost" as "[HΦc _]".
      iModIntro.
      iIntros "[Hfown|Hfown]".
      - (* Write failed *)
        iApply "HΦc".
        iFrame "Hghost".
        iLeft. by iFrame.
      - (* Write succeeded  *)
        iApply "HΦc".
        iNamed "Hghost".
        iDestruct (map_valid with "Hctx Hmapsto") as %Hsome.
        iDestruct (big_sepM_lookup_acc with "Hback") as "[[Hbackend_one|Hbad] Hback_rest]"; first done.
        2: {
          iDestruct (ptsto_valid_2 with "Hbad Hmapsto") as %Hbad.
          contradiction.
        }
        iDestruct "Hmapsto" as "[Hmapsto Hmapsto2]".
        iSpecialize ("Hback_rest" with "[Hmapsto2]").
        { by iRight. }
        iMod (make_request {|Req_Seq:= _; Req_CID:=_; Req_Args:= args |} IncrPreCond IncrPostCond with "[ ] [$Hrpcclient_own] [Hbackend_one]") as "[Hrpcclient_own Hreq]"; eauto.
        {
          simpl.
          admit. (* Just make it so short lived clerks are one-shot clerks *)
        }
        iDestruct "Hreq" as (γreq) "[#His_req Hreqtok]".

        iFrame.
        iRight.
        iExists data2,_,(word.add seq_init 1),_.
        simpl.
        rewrite word.word_sub_add_l_same_r.
        iFrame "#∗".
        done.
    }
    iNext.

    (* TODO: this is copy pasted from above; commit to backend cid and seq *)
        iNamed "Hghost".
        iDestruct (map_valid with "Hctx Hmapsto") as %Hsome.
        iDestruct (big_sepM_lookup_acc with "Hback") as "[[Hbackend_one|Hbad] Hback_rest]"; first done.
        2: {
          iDestruct (ptsto_valid_2 with "Hbad Hmapsto") as %Hbad.
          contradiction.
        }
        iDestruct "Hmapsto" as "[Hmapsto Hmapsto2]".
        iDestruct ("Hback_rest" with "[Hmapsto2]") as "Hback".
        { by iRight. }
        iMod (make_request {|Req_Seq:= _; Req_CID:=_; Req_Args:= args |} IncrPreCond IncrPostCond with "[ ] [$Hrpcclient_own] [Hbackend_one]") as "[Hrpcclient_own Hreq]"; eauto.
        {
          simpl.
          admit. (* Just make it so short lived clerks are one-shot clerks *)
        }
        iDestruct "Hreq" as (γreq) "[#His_req Hreqtok]".
    (* End commit to backend cid and seq *)

    iIntros "[Hfown Hslice]".
    iCache with "Hfown Hback Hctx Hpost Hreqtok Hmapsto Hrpcclient_own".
    { (* Re-prove crash obligation in the special case. Nothing interesting about this. *)
      iDestruct "Hpost" as "[HΦc _]". iModIntro. iApply "HΦc". iFrame.
      iRight. iFrame.
      iExists _,_,_,_; iFrame "#∗".
      rewrite word.word_sub_add_l_same_r.
      by iFrame "His_req".
    }
    wpc_pures.

    (* Merge with other case of proof. *)
    admit.

  - iNamed "Hcase".
    iCache with "Hfown_oldv Hghost Hpost".
    { (* Re-prove crash obligation in the special case. Nothing interesting about this. *)
      iDestruct "Hpost" as "[HΦc _]". iModIntro. iApply "HΦc". by iFrame.
    }

    iNamed "Hfown_oldv".
    iDestruct "Hfown_oldv" as "(Hfown_oldv & Hmapsto & %Henc & %Hpos & Hrpc_clientown & HrpcToken & #Hisreq)".
    wpc_apply (wpc_Read with "Hfown_oldv").
    iSplit.
    { (* crash obligation of called implies our crash obligation *)
      iDestruct "Hpost" as "[Hpost _]".
      iModIntro. iIntros. iApply "Hpost". iFrame. iRight.
      by iExists _, _, _, _; iFrame "#∗".
    }
    iNext.
    iIntros (content) "[Hcontent_slice Hfown_oldv]".

    iCache with "Hfown_oldv Hrpc_clientown Hghost HrpcToken Hmapsto Hpost".
    { (* Prove crash obligation after destructing above; TODO: do this earlier *)
      iDestruct "Hpost" as "[HΦc _]". iModIntro. iApply "HΦc". iFrame. iRight.
      by iExists _,_,_, _; iFrame "#∗".
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
      wp_apply (wp_ShortTermIncrClerk__MakePreparedRequest with "His_incrserver [Hown_ck Hisreq]").
      { unfold own_alloc_prepared_short_incr_clerk.
        unfold own_unalloc_prepared_short_incr_clerk.
        iNamed "Hown_ck".
        iFrame "#∗".
        iSplit.
        { done.  }
        { iExists _; iFrame "Hisreq". }
      }

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
      wpc_pures.
      iDestruct "Hpost" as "[_ HΦ]".
      iApply ("HΦ" $! (|={⊤}=> args.1 [[γ.(incr_mapGN)]]↦{1/2} old_v ∗
                       args.1 [[γback.(incr_mapGN)]]↦ (word.add old_v 1)
                      )%I
              {| kvsM:= <[args.1:=(word.add old_v 1)]> server.(kvsM)|}
             ).
      iSplitL "Hincrserver".
      { iExists _. iFrame "Hincrserver #". }
      iSplitR "".
      {
        iModIntro. iSplit.
        { iFrame.
          iMod (get_request_post with "Hisreq HmakeReqPost HrpcToken") as ">Hbackmapsto"; first done.
          by iFrame.
        }
        { iRight. by iExists _,_,_,_; iFrame "#∗". }
      }

      (* Prove the fupd *)
      iModIntro.
      iIntros "Hghost >[Hγmapsto Hγbackmapsto]".
      iNamed "Hghost".
      iDestruct (map_valid with "Hctx Hγmapsto") as %HkInMap.
      iDestruct (big_sepM_insert_acc _ _ args.1 old_v with "Hback") as "[Hk Hback]".
      { done. }
      iDestruct "Hk" as "[Hk|Hk]".
      { (* Impossible case: big_sepM has γback ptsto *)
        iDestruct (ptsto_agree_frac_value with "Hγbackmapsto Hk") as %[_ Hbad].
        by exfalso.
      }
      (* Take the ↦{1/2} from the big_sepM element that we accessesd *)
      iCombine "Hγmapsto Hk" as "Hγmapsto".
      iMod (map_update _ _ _ with "Hctx Hγmapsto") as "[Hctx Hγmapsto]".
      iSpecialize ("Hback" $! (word.add old_v 1) with "[Hγbackmapsto]").
      { by iLeft. }
      iModIntro.
      iFrame.
    }
    {
      (* TODO: Use has_encoding_length and is_slize_sz to get contradiction *)
      iExFalso.
      admit.
    }
Admitted.

End incr_proof.
