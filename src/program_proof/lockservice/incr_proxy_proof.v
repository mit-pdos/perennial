From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import disk_prelude marshal_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Goose.github_com.mit_pdos.lockservice Require Import lockservice grove_common.
From Perennial.program_proof.lockservice Require Import rpc_proof rpc nondet kv_proof fmcounter_map common_proof.
Require Import Decimal Ascii String DecimalString.
From Perennial.program_proof.lockservice Require Import grove_ffi.

Section incr_proof.

(* Proof for increment backed by another increment service
 *)

Context `{!heapG Σ}.
Context `{!filesysG Σ}.

Definition has_encoding_for_onetime_clerk data cid (args:RPCValsC) :=
   has_encoding data [EncUInt64 cid ; EncUInt64 2 ; EncUInt64 args.(U64_1) ; EncUInt64 args.(U64_2)].

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
  req ↦[RPCRequest :: "CID"] #cid -∗
  req ↦[RPCRequest :: "Seq"] #seq -∗
  req ↦[RPCRequest :: "Args"] (#a1, (#a2, #())) -∗
  req ↦[struct.t RPCRequest] (#cid, (#seq, ((#a1, (#a2, #())) , #())))
  .
Proof.
  iIntros.
  iApply struct_fields_split.
  iFrame. done.
Qed.

Lemma RPCVals_merge vals a1 a2:
  vals ↦[RPCVals :: "U64_1"] #a1 -∗
  vals ↦[RPCVals :: "U64_2"] #a2 -∗
  vals ↦[struct.t RPCVals] (#a1, (#a2, #()))
.
Proof.
  iIntros.
  iApply struct_fields_split.
  iFrame. done.
Qed.

Definition own_onetime_incr_clerk (ck isrv:loc) (cid:u64) : iProp Σ :=
  "cid" ∷ ck ↦[ShortTermIncrClerk :: "cid"] #cid ∗
  "seq" ∷ ck ↦[ShortTermIncrClerk :: "seq"] #1 ∗
  "incrserver" ∷ ck ↦[ShortTermIncrClerk :: "incrserver"] #isrv ∗

  "req" ∷ (∃ (c s1 a1 a2:u64), ((ck ↦[ShortTermIncrClerk :: "req"] (#c,
                                              (#s1,
                                              (#a1, (#a2, #()), #()))))))
.

Variable old_v:u64.
Definition IncrPreCond : RPCValsC → iProp Σ := (λ a, a.(U64_1) [[γback.(incr_mapGN)]]↦ old_v)%I.
Definition IncrPostCond : RPCValsC → u64 → iProp Σ := (λ a r, a.(U64_1) [[γback.(incr_mapGN)]]↦ (word.add old_v 1))%I.

Definition own_unalloc_prepared_onetime_incr_clerk ck isrv (cid:u64) (args:RPCValsC) : iProp Σ :=
  "cid" ∷ ck ↦[ShortTermIncrClerk :: "cid"] #cid ∗
  "seq" ∷ ck ↦[ShortTermIncrClerk :: "seq"] #2 ∗
  "incrserver" ∷ ck ↦[ShortTermIncrClerk :: "incrserver"] #isrv ∗
  "#req" ∷ (readonly (ck ↦[ShortTermIncrClerk :: "req"] (#cid,
                                              (#1,
                                              (#args.(U64_1), (#args.(U64_2), #()), #())))))
.

Definition own_alloc_prepared_onetime_incr_clerk ck isrv (cid:u64) (args:RPCValsC) : iProp Σ :=
  "Hown" ∷ own_unalloc_prepared_onetime_incr_clerk ck isrv cid args ∗
  "#HreqInv" ∷ ∃ γPost, is_RPCRequest γback.(incr_rpcGN) γPost (IncrPreCond args) (IncrPostCond args) {| Req_CID:=cid; Req_Seq:=1; |}
.

(* TODO: this should refer to a lemma in incr_proof.v *)

Lemma IncrServer__Increment_is_rpcHandler (isrv:loc) :
is_incrserver γback isrv -∗
{{{
     True
}}}
  IncrServer__Increment #isrv
{{{ (f:goose_lang.val), RET f;
        ∀ args req, is_rpcHandler f γback.(incr_rpcGN) args req (IncrPreCond args) (IncrPostCond args)
}}}.
Admitted.

Lemma wp_ShortTermIncrClerk__MakePreparedRequest ck isrv cid args :
is_incrserver γback isrv -∗
{{{
     own_alloc_prepared_onetime_incr_clerk ck isrv cid args
}}}
    ShortTermIncrClerk__MakePreparedRequest #ck
{{{
     (reply':@RPCReply u64), RET #(reply'.(Rep_Ret)); ⌜reply'.(Rep_Stale) = true⌝
               ∗ RPCRequestStale γback.(incr_rpcGN)
                   {| Req_CID := cid; Req_Seq := 1; |}
               ∨ RPCReplyReceipt γback.(incr_rpcGN)
                   {| Req_CID := cid; Req_Seq := 1; |}
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
  iMod (readonly_alloc (req ↦[RPCRequest :: "CID"] #cid) q with "[CID]") as "#CID"; first eauto.
  iMod (readonly_alloc (req ↦[RPCRequest :: "Seq"] #1) q with "[Seq]") as "#Seq"; first eauto.
  iMod (readonly_alloc (req ↦[RPCRequest :: "Args"] (into_val.to_val args)) q with "[Args]") as "#Args"; first eauto.

  wp_loadField.
  wp_apply (IncrServer__Increment_is_rpcHandler with "Hs_inv").
  iIntros (f) "#His_rpcHandler".
*)
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

Lemma wp_EncodeShortTermIncrClerk ck cid args (isrv:loc) :
{{{
     own_unalloc_prepared_onetime_incr_clerk ck isrv cid args
}}}
  EncodeShortTermIncrClerk #ck
{{{
     content data, RET (slice_val content);
     is_slice content byteT 1 data ∗
     ⌜has_encoding_for_onetime_clerk data cid args⌝
}}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".

  wp_lam.

  wp_apply (wp_new_enc).
  iIntros (enc_v) "Henc".
  wp_pures.
  wp_loadField.
  wp_apply (wp_Enc__PutInt with "Henc"); first done.
  iIntros "Henc".

  wp_loadField.
  wp_apply (wp_Enc__PutInt with "Henc"); first done.
  iIntros "Henc".

  wp_pures.

  wp_loadField.
  wp_apply (wp_Enc__PutInt with "Henc"); first done.
  iIntros "Henc".

  wp_pures.
  wp_loadField.
  wp_pures.
  wp_apply (wp_Enc__PutInt with "Henc"); first done.
  iIntros "Henc".

  wp_pures.
  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (content data) "(%Hencoding & %Hsize & Hslice)".
  iApply "HΦ".
  iFrame.
  done.
Qed.

Lemma wp_DecodeShortTermIncrClerk cid args (isrv:loc) (content:Slice.t) data :
{{{
     is_slice content byteT 1 data ∗
     ⌜has_encoding_for_onetime_clerk data cid args⌝
}}}
  DecodeShortTermIncrClerk #isrv (slice_val content)
{{{
     (ck:loc), RET #ck; own_unalloc_prepared_onetime_incr_clerk ck isrv cid args
}}}.
Proof.
  iIntros (Φ) "(Hslice & %Henc) HΦ".
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

Lemma wp_PrepareRequest (ck isrv:loc) (args:RPCValsC) cid:
{{{
     own_onetime_incr_clerk ck isrv cid
}}}
  ShortTermIncrClerk__PrepareRequest #ck (into_val.to_val args)
{{{
     RET #();
     own_unalloc_prepared_onetime_incr_clerk ck isrv cid args
}}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iApply wp_fupd.
  wp_lam.
  wp_pures.
  iNamed "Hpre".
  iNamed "req".
  wp_loadField.
  wp_apply (overflow_guard_incr_spec).
  iIntros (Hoverflow).
  wp_pures.
  wp_loadField.
  wp_loadField.
  wp_apply (wp_storeField with "req").
  { (* Typecheck *)
    Transparent struct.t.
    eauto.
    Opaque struct.t.
  }
  iIntros "req".
  wp_pures.
  wp_loadField.
  wp_storeField.
  iMod (readonly_alloc_1 with "req") as "#req".
  iApply "HΦ".
  by iFrame "#∗".
Qed.

Variable γ:incrservice_names.

Record ProxyServerC :=
  {
  kvsM:gmap u64 u64 ;
  lastCID:u64 ;
  incrserver:loc (* This would normally be "IP address" or some such *)
  }.

Implicit Types server : ProxyServerC.

Definition ProxyIncrServer_core_own_vol (srv:loc) server : iProp Σ :=
  "Hincrserver" ∷ srv ↦[IncrProxyServer :: "incrserver"] #server.(incrserver) ∗
  "HlastCID" ∷ srv ↦[IncrProxyServer :: "lastCID"] #(server.(lastCID)) ∗
  "#His_incrserver" ∷ is_incrserver γback server.(incrserver)
.

(* Either the proxy server has the mapsto fact for the backend, or, if it
   doesn't, then it has the  mapsto for γ, meaning backend mapsto is being used
   for a request, and thus belongs to some request's invariant.
 *)
Definition ProxyIncrServer_core_own_ghost server : iProp Σ :=
  "Hctx" ∷ map_ctx γ.(incr_mapGN) 1 server.(kvsM) ∗
  "Hback" ∷ ([∗ map] k ↦ v ∈ server.(kvsM), (k [[γback.(incr_mapGN)]]↦ v ∨ k [[γ.(incr_mapGN)]]↦{1/2} v)) ∗
  "HownCIDs" ∷ ([∗ set] cid ∈ (fin_to_set u64), RPCClient_own γback.(incr_rpcGN) cid 0 ∨ ⌜int.Z cid < int.Z server.(lastCID)⌝%Z) ∗
  "Hfown_lastCID" ∷ (∃ data, "lastCID" f↦ data ∗ ⌜has_encoding data [EncUInt64 server.(lastCID)]⌝)
.

Tactic Notation "wpc_loadField" :=
  lazymatch goal with
  | |- envs_entails _ (wpc _ _ _ _ _ _) =>
    wpc_bind (struct.loadF _ _ (Val _));
    lazymatch goal with
    | |- envs_entails ?env (wpc _ _ _
                                (App (Val (struct.loadF ?d ?fname))
                                     (Val (LitV (LitLoc ?l)))) _ _) =>
      match env with
      | context[Esnoc _ ?i (l ↦[d :: fname] _)%I] =>
        wpc_frame_go i base.Right [i]; [idtac]
      | _ => wpc_frame_go "" base.Right (@nil ident); [idtac]
      | _ => fail 1 "wpc_loadField: could not frame automatically"
      end;
      wp_loadField;
      iNamed 1
    | _ => fail 1 "wpc_loadField: could not bind a struct.loadF"
    end
  | _ => fail 1 "wpc_loadField: not a wpc"
  end.

Tactic Notation "wpc_storeField" :=
  wpc_bind (struct.storeF _ _ _ _);
  wpc_frame;
  wp_storeField;
  iNamed 1.

(* Hom(P, Hom(Q, R)) ≃ Hom(P ⊗ Q, R) ≃ Hom(Q, Hom(P, R)) *)
Lemma wand_commute {P Q R:iProp Σ} :
(P -∗ (Q -∗ R)) -∗ (Q -∗ (P -∗ R)).
Proof.
  iIntros "HR Q P".
  by iSpecialize ("HR" with "P Q").
Qed.

(* TODO: make this a wpc, since it owns ghost state *)
Lemma wpc_MakeFreshIncrClerk (isrv:loc) server :
  {{{
      ProxyIncrServer_core_own_vol isrv server ∗
      ProxyIncrServer_core_own_ghost server
  }}}
    IncrProxyServer__MakeFreshIncrClerk #isrv @ 37 ; ⊤
    (* IncrProxyServer__proxy_increment_core #isrv @ 37 ; ⊤ *)
  {{{
      cid (ck:loc), RET #ck; own_onetime_incr_clerk ck server.(incrserver) cid ∗
      RPCClient_own γback.(incr_rpcGN) cid 1 ∗
      ProxyIncrServer_core_own_vol isrv {| kvsM:=server.(kvsM) ; incrserver:=server.(incrserver) ; lastCID:=(word.add server.(lastCID) 1)|} ∗
      ProxyIncrServer_core_own_ghost {| kvsM:=server.(kvsM) ; incrserver:=server.(incrserver) ; lastCID:=(word.add server.(lastCID) 1) |}
  }}}
  {{{
      ∃ lastCID', ProxyIncrServer_core_own_ghost {| kvsM:=server.(kvsM) ; incrserver:=server.(incrserver) ; lastCID:=lastCID' |}
  }}}.
Proof.
  iIntros (Φ Φc) "[Hvol Hghost] HΦ".
  iNamed "Hvol".
  iNamed "Hghost".

  iCache with "HΦ Hctx Hback Hfown_lastCID HownCIDs".
  { iDestruct "HΦ" as "[HΦc _]".
    iModIntro.
    iApply "HΦc".
    by iExists _; iFrame.
  }

  wpc_rec Hcrash;
  [ try iFromCache; crash_case .. | try wpc_pure1 Hcrash; [try iFromCache; crash_case ..  | repeat (wpc_pure1 Hcrash; []); clear Hcrash] ].

  iDestruct "Hfown_lastCID" as (old_data) "[Hfown_lastCID %Hold_encoding]".
  iCache with "HΦ Hctx Hback Hfown_lastCID HownCIDs".
  { iDestruct "HΦ" as "[HΦc _]".
    iModIntro.
    iApply "HΦc".
    iFrame.
    iExists _; iFrame.
    by iExists _; iFrame.
  }

  wpc_loadField.
  wpc_pures.
  wpc_loadField.

  Tactic Notation "wpc_wpapply" open_constr(lem) :=
  iPoseProofCore lem as false (fun H =>
    lazymatch goal with
    | |- envs_entails _ (wpc ?s ?k ?E1 ?e ?Q ?Qc) =>
      reshape_expr e ltac:(fun K e' =>
        wpc_bind_core K; (wpc_frame; iApplyHyp H; try iNext; try wp_expr_simpl; solve_bi_true))
    | _ => fail "wpc_wpapply: not a wpc"
    end
      ).

  wpc_wpapply (overflow_guard_incr_spec).
  iIntros (HincrSafe).
  iNamed 1.

  wpc_pures.
  wpc_loadField.
  wpc_pures.

  wpc_storeField.
  wpc_pures.

  wpc_wpapply (wp_new_enc).
  iIntros (enc_v) "Henc".
  iNamed 1.

  wpc_pures.
  wpc_loadField.

  wpc_wpapply (wp_Enc__PutInt with "Henc"); first done.
  iIntros "Henc".
  iNamed 1.

  wpc_pures.
  wpc_wpapply (wp_Enc__Finish with "Henc").
  iIntros (content data) "(%Hencoding & %Hlength & Hcontent_slice)".
  iNamed 1.

  wpc_apply (wpc_Write with "[$Hfown_lastCID $Hcontent_slice]").
  iSplit.
  { iDestruct "HΦ" as "[HΦc _]". iModIntro. iIntros "Hcases". iApply "HΦc".
    iDestruct "Hcases" as "[Hcases|Hcases]".
    { iExists _; iFrame. iExists _; iFrame. done. }
    { (* Case that lastCID was updated on durable storage *)
      iDestruct (big_sepS_impl _ (λ cid, RPCClient_own γback.(incr_rpcGN) cid 0 ∨
                                         ⌜int.Z cid < int.Z server.(lastCID) + 1⌝%Z)%I with "HownCIDs []") as "HownCIDs".
      {
        iModIntro. iIntros (x Hxin) "[Hrpcclient_own|%Hineq]".
        { iLeft. iFrame. }
        { iRight. iPureIntro. lia. }
      }
      iExists (word.add server.(lastCID) 1).
      rewrite HincrSafe. iFrame.
      by iExists _; iFrame.
    }
  }
  iNext. iIntros "[Hfown_lastCID Hcontent_slice]".


  (* Get RPCClient_own, and increase lastCID *)
  iDestruct (big_sepS_elem_of_acc_impl (server.(lastCID)) with "HownCIDs") as "(HownCID & HownCIDs_rest)".
  { apply elem_of_fin_to_set. }
  iDestruct "HownCID" as "[HownCID|%Hbad]"; last by lia.
  (* Weaken the big_sepS; after this, we won't be able to get RPCClient anymore, because lastCID will have increased *)
  iDestruct ("HownCIDs_rest" $! (λ cid, RPCClient_own γback.(incr_rpcGN) cid 0 ∨
                                     ⌜int.Z cid < int.Z server.(lastCID) + 1⌝%Z)%I with "[] []") as "HownCIDs".
  {
    iModIntro. iIntros (x Hxin Hdistinct) "[Hrpcclient_own|%Hineq]".
    { iLeft. iFrame. }
    { iRight. iPureIntro. lia. }
  }
  {
    iRight. iPureIntro. lia.
  }

  (* Set RPCClient_own seq to 1*)
  iMod (fmcounter_map_update (int.nat 1) with "HownCID") as "[HownCID _]".
  { word. }

  iCache with "HΦ Hctx Hback Hfown_lastCID HownCIDs".
  { iDestruct "HΦ" as "[HΦc _]".
    iModIntro.
    iApply "HΦc".
    iFrame.
    iExists (word.add server.(lastCID) 1).
    rewrite HincrSafe. iFrame.
    by iExists _; iFrame.
  }
  wpc_pures.
  wpc_wpapply (wp_allocStruct).
  { by apply zero_val_ty'. }
  iIntros (l) "Hl".
  iNamed 1.
  wpc_pures.

  iDestruct (struct_fields_split with "Hl") as "Hl".
  iNamed "Hl". simpl.
  wpc_storeField.
  wpc_pures.
  wpc_storeField.
  wpc_pures.
  wpc_loadField.
  wpc_storeField.
  wpc_pures.

  iApply "HΦ".
  iFrame.
  Transparent struct.t.
  simpl.
  Opaque struct.t.

  iSplitL "req".
  { iExists _, _, _, _; iFrame. }
  rewrite HincrSafe.
  iFrame "#∗".
  by iExists _; iFrame.
Qed.

Definition ProxyIncrCrashInvariant (sseq:u64) (args:RPCValsC) : iProp Σ :=
  ("Hfown_oldv" ∷ ("procy_incr_request_" +:+ u64_to_string sseq) f↦ [] ∗
   "Hmapsto" ∷ args.(U64_1) [[γ.(incr_mapGN)]]↦ old_v ) ∨
  ("Hfown_oldv" ∷ ∃ data cid γreq, ("procy_incr_request_" +:+ u64_to_string sseq) f↦ data ∗
   "Hmapsto" ∷ args.(U64_1) [[γ.(incr_mapGN)]]↦{1/2} old_v ∗
   ⌜has_encoding_for_onetime_clerk data cid args⌝ ∗
   RPCClient_own γback.(incr_rpcGN) cid 2 ∗
   RPCRequest_token γreq ∗
   is_RPCRequest γback.(incr_rpcGN) γreq (IncrPreCond args) (IncrPostCond args) {| Req_CID:=cid; Req_Seq:=1; |}
  )
.

Lemma increment_proxy_core_idempotent (isrv:loc) server (seq:u64) (args:RPCValsC) :
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
        args.(U64_1) [[γ.(incr_mapGN)]]↦ (word.add old_v 1)
      )
  }}}
  {{{
       |={⊤}=> ProxyIncrCrashInvariant seq args ∗
      ∃ lastCID', ProxyIncrServer_core_own_ghost {| kvsM:=server.(kvsM) ; incrserver:=server.(incrserver) ; lastCID:=lastCID' |}
       (* Need this fupd because we need to use an invariant right after destructing into cases and right when trying to prove crash condition *)
  }}}.
Proof.
  Opaque struct.t. (* TODO: put this here to avoid unfolding the struct defns all the way *)
  Opaque zero_val.
  iIntros "#Hrpcsrv".
  iIntros (Φ Φc) "!# [HincrCrashInv [Hvol Hghost]] Hpost".
  wpc_call.
  { iFrame. by iExists _; iFrame. }
  { iFrame. by iExists _; iFrame. }
  iCache with "HincrCrashInv Hghost Hpost".
  {
    iDestruct "Hpost" as "[HΦc _]". iModIntro. iApply "HΦc".
    iFrame. by iExists _; iFrame.
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
      iDestruct "Hpost" as "[HΦc _]". iModIntro. iApply "HΦc". iFrame. iSplitR "Hghost".
      - iLeft. by iFrame.
      - by iExists _; iFrame.
    }

    wpc_apply (wpc_Read with "Hfown_oldv").
    iSplit.
    { (* Show that the crash obligation of the function we're calling implies our crash obligation *)
      iDestruct "Hpost" as "[Hpost _]".
      iModIntro. iIntros. iApply "Hpost".
      iSplitR "Hghost".
      - iLeft. by iFrame.
      - by iExists _; iFrame.
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

    wpc_apply (wpc_MakeFreshIncrClerk with "[Hvol Hghost]").
    { iFrame. }
    iSplit.
    { iDestruct "Hpost" as "[HΦc _]". iModIntro. iIntros.
      iApply "HΦc". iFrame.
      iLeft. by iFrame.
    }

    iNext. iIntros (cid ck_ptr) "(Hownclerk & Hrpcclient_own & Hvol & Hghost)".
    iNamed "Hownclerk".

    iCache with "Hfown_oldv Hmapsto Hghost Hpost".
    { (* Re-prove crash obligation in the special case. Nothing interesting about this. *)
      iDestruct "Hpost" as "[HΦc _]". iModIntro. iApply "HΦc". iSplitR "Hghost".
      - iLeft. by iFrame.
      - by iExists _; iFrame.
    }

    wpc_bind (store_ty _ _); wpc_frame.
    wp_store. iNamed 1.

    wpc_pures.

    wpc_bind (load_ty _ _); wpc_frame.
    wp_load. iNamed 1.

    wpc_bind (App _ #ck_ptr _)%E.
    wpc_frame.
    wp_apply (wp_PrepareRequest with "[cid seq incrserver req]").
    {
      iFrame.
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

    wpc_pures.
    wpc_apply (wpc_Write with "[$Hfown_oldv $Hcontent2_slice]").
    iSplit.
    { (* Prove that crash obligation of Write implies our crash obligation. *)
      iDestruct "Hpost" as "[HΦc _]".
      iModIntro.
      iIntros "[Hfown|Hfown]".
      - (* Write failed *)
        iApply "HΦc".
        iSplitR "Hghost".
        + iLeft. by iFrame.
        + by iExists _; iFrame.
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
        iMod (make_request {|Req_Seq:= _; Req_CID:=_; |} (IncrPreCond args) (IncrPostCond args) with "[ ] [$Hrpcclient_own] [Hbackend_one]") as "[Hrpcclient_own Hreq]"; eauto.

        iDestruct "Hreq" as (γreq) "[#His_req Hreqtok]".

        iSplitR "Hback_rest Hctx HownCIDs Hfown_lastCID".
        { iRight.
          iExists data2,_,_.
          iFrame "#∗".
          simpl.
          done.
        }
        {
          by iExists _; iFrame.
        }
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
        iMod (make_request {|Req_Seq:= _; Req_CID:=_; |} (IncrPreCond args) (IncrPostCond args) with "[ ] [$Hrpcclient_own] [Hbackend_one]") as "[Hrpcclient_own Hreq]"; eauto.
        iDestruct "Hreq" as (γreq) "[#His_req Hreqtok]".
    (* End commit to backend cid and seq *)

    iIntros "[Hfown Hslice]".
    iCache with "Hfown HownCIDs Hfown_lastCID Hback Hctx Hpost Hreqtok Hmapsto Hrpcclient_own".
    { (* Re-prove crash obligation in the special case. Nothing interesting about this. *)
      iDestruct "Hpost" as "[HΦc _]". iModIntro. iApply "HΦc".
      iSplitL "Hreqtok Hmapsto Hrpcclient_own Hfown".
      - iRight. iFrame. iExists _,_,_; iFrame "#∗".
        done.
      - by iExists _; iFrame.
    }
    wpc_pures.

    (* Merge with other case of proof. *)
    admit.

  - iNamed "Hcase".
    iCache with "Hfown_oldv Hghost Hpost".
    { (* Re-prove crash obligation in the special case. Nothing interesting about this. *)
      iDestruct "Hpost" as "[HΦc _]". iModIntro. iApply "HΦc". iSplitR "Hghost".
      - iRight. by iFrame.
      - by iExists _; iFrame.
    }

    iNamed "Hfown_oldv".
    iDestruct "Hfown_oldv" as "(Hfown_oldv & Hmapsto & %Henc & Hrpc_clientown & HrpcToken & #Hisreq)".
    wpc_apply (wpc_Read with "Hfown_oldv").
    iSplit.
    { (* crash obligation of called implies our crash obligation *)
      iDestruct "Hpost" as "[HΦc _]".
      iModIntro. iIntros. iApply "HΦc".
      iSplitR "Hghost".
      - iRight. by iExists _, _, _; iFrame "#∗".
      - by iExists _; iFrame.
    }
    iNext.
    iIntros (content) "[Hcontent_slice Hfown_oldv]".

    iCache with "Hfown_oldv Hrpc_clientown Hghost HrpcToken Hmapsto Hpost".
    { (* Prove crash obligation after destructing above; TODO: do this earlier *)
      iDestruct "Hpost" as "[HΦc _]". iModIntro. iApply "HΦc". iFrame.
      iSplitR "Hghost".
      - iRight. by iExists _,_, _; iFrame "#∗".
      - eauto.
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
      { iNamed "Hown_ck".
        iFrame "#∗".
        iExists _; iFrame "Hisreq".
      }

      iIntros (v) "HmakeReqPost".
      iNamed 1.

      iDestruct "HmakeReqPost" as "[[% Hstale]|HmakeReqPost]".
      {
        iDestruct (client_stale_seqno with "Hstale Hrpc_clientown") as %Hbad.
        exfalso.
        simpl in Hbad.
        replace (int.nat 1 + 1) with (2) in Hbad by word.
        replace (int.nat 2%nat) with (2) in Hbad by word.
        done.
      }
      wpc_pures.
      iDestruct "Hpost" as "[_ HΦ]".
      iApply ("HΦ" $! (|={⊤}=> args.(U64_1) [[γ.(incr_mapGN)]]↦{1/2} old_v ∗
                       args.(U64_1) [[γback.(incr_mapGN)]]↦ (word.add old_v 1)
                      )%I
              {| kvsM:= <[args.(U64_1):=(word.add old_v 1)]> server.(kvsM)|}
             ).
      iSplitL "Hincrserver HlastCID".
      { iFrame "HlastCID Hincrserver #". }
      iSplitR "".
      {
        iModIntro. iSplit.
        { iFrame.
          iMod (get_request_post with "Hisreq HmakeReqPost HrpcToken") as ">Hbackmapsto"; first done.
          by iFrame.
        }
        { iRight. by iExists _,_,_; iFrame "#∗". }
      }

      (* Prove the fupd *)
      iModIntro.
      iIntros "Hghost >[Hγmapsto Hγbackmapsto]".
      iNamed "Hghost".
      iDestruct (map_valid with "Hctx Hγmapsto") as %HkInMap.
      iDestruct (big_sepM_insert_acc _ _ args.(U64_1) old_v with "Hback") as "[Hk Hback]".
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
      iExFalso.
      iDestruct (is_slice_sz with "Hcontent_slice") as %Hbad.
      apply bool_decide_eq_false in Hlen.
      assert (int.Z content.(Slice.sz) = 0)%Z.
      { apply Znot_lt_ge in Hlen.
        replace (int.Z (U64 0)) with 0%Z in Hlen by word.
        word.
      }
      assert (content.(Slice.sz) = 0)%Z by word.
      rewrite H0 in Hbad.
      replace (int.nat 0%Z) with (0) in Hbad by word.
      apply length_zero_iff_nil in Hbad.
      rewrite Hbad in Henc.
      unfold has_encoding_for_onetime_clerk in Henc.
      apply has_encoding_length in Henc.
      simpl in Henc.
      lia.
    }
Admitted.

End incr_proof.
