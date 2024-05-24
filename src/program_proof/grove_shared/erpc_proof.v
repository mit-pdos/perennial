From Perennial.Helpers Require Import ModArith.
From Goose.github_com.mit_pdos.gokv Require Import erpc.
From Perennial.goose_lang Require Import adequacy.
From Perennial.base_logic Require Import lib.ghost_map lib.mono_nat lib.saved_spec.
From Perennial.program_proof Require Import grove_prelude std_proof marshal_stateless_proof.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec erpc_lib.

Notation erpcG Σ := (erpc_lib.erpcG Σ (list u8)).
Notation erpcΣ := (erpc_lib.erpcΣ (list u8)).

Definition erpcN := nroot .@ "erpc".

(** Spec for an eRPC handler.
This is isomorphic to RpcSpec, but to avoid confusion we use distinct types. *)
Polymorphic Record eRPCSpec@{u} {Σ} :=
  { espec_ty : Type@{u};
    espec_Pre : espec_ty → list u8 → iProp Σ;
    espec_Post : espec_ty → list u8 → list u8 → iProp Σ }.

Section erpc_defs.
Context `{!erpcG Σ, !urpcregG Σ, !gooseGlobalGS Σ}.

Local Definition encode_request (rid : eRPCRequestID) (payload : list u8) :=
  u64_le rid.(Req_CID) ++ u64_le rid.(Req_Seq) ++ payload.

(** [Spec] is the spec of the eRPC handler;
    we compute the spec of the underlying uRPC handler. *)
Polymorphic Definition eRPCSpec_uRPC@{u} γerpc (spec : eRPCSpec (Σ:=Σ)) : RpcSpec@{u} :=
 {| spec_ty := erpc_request_names * eRPCRequestID * (list u8) * spec.(espec_ty@{u});
    spec_Pre :=(λ '(γreq, rid, payload, x) req,
                  ⌜req = encode_request rid payload ∧ uint.Z rid.(Req_Seq) > 0⌝ ∗
                  is_eRPCRequest γerpc γreq
                     (spec.(espec_Pre) x payload)
                     (spec.(espec_Post) x payload)
                     rid
             )%I;
    spec_Post :=(λ '(γreq, rid, payload, x) req rep,
                (eRPCRequestStale γerpc rid ∨
                 eRPCReplyReceipt γerpc rid rep)
             )%I
 |}.

(** Convenience function to say that a given rpcid has such a handler *)
Polymorphic Definition is_erpc_spec `{!urpcregG Σ} Γsrv γerpc (host:u64) (rpcid:u64) (spec : eRPCSpec) :=
  is_urpc_spec Γsrv host rpcid (eRPCSpec_uRPC γerpc spec).

(** What a client needs to get started *)
Definition erpc_make_client_pre γ cid : iProp Σ :=
  is_eRPCServer γ ∗ is_eRPCClient_ghost γ cid 1.

(** The "pre-server" state: initialization happens in two phasees,
  a ghost-init step globally before any server starts and the
  Hoare triple actually initializing the server. This is because
  the clients also need the γ, so we cannot allocate that
  in a WP on the server. *)
Definition own_erpc_pre_server (γ : erpc_names) : iProp Σ :=
  "#His_srv" ∷ is_eRPCServer γ ∗
  "HRPCserver_own" ∷ eRPCServer_own_ghost γ ∅ ∅ ∗
  "Hcids" ∷ [∗ set] cid ∈ (fin_to_set u64), is_eRPCClient_ghost γ cid 1.

Lemma erpc_init_server_ghost :
  ⊢ |={⊤}=> ∃ γ, own_erpc_pre_server γ.
Proof.  
  iMod make_rpc_server as (γ) "(#Hserv & ? & Hcids)"; first solve_ndisj.
  iExists γ. iModIntro. iFrame. done.
Qed.

End erpc_defs.

Section erpc_proof.
Context `{!heapGS Σ, !urpcregG Σ, !erpcG Σ}.

Local Definition own_erpc_server (γ : erpc_names) (s : loc) : iProp Σ :=
  ∃ (lastReply_ptr lastSeq_ptr:loc)
    (lastReplyM:gmap u64 (list u8)) (lastReplyMV:gmap u64 goose_lang.val)
    (lastSeqM:gmap u64 u64) (nextCID:u64),
  "HlastReply" ∷ s ↦[erpc.Server :: "lastReply"] #lastReply_ptr ∗
  "HlastReplyMap" ∷ map.own_map lastReply_ptr (DfracOwn 1) (lastReplyMV, zero_val (slice.T byteT)) ∗ (* TODO: default *)
  "%HlastReplyMVdom" ∷ ⌜dom lastReplyMV = dom lastSeqM⌝ ∗
  "HlastReply_structs" ∷ ([∗ map] k ↦ v;rep ∈ lastReplyMV ; lastReplyM,
    ∃ val_sl q, ⌜v = slice_val val_sl⌝ ∗ typed_slice.own_slice_small val_sl byteT q rep) ∗
  "HlastSeq" ∷ s ↦[erpc.Server :: "lastSeq"] #lastSeq_ptr ∗
  "HlastSeqMap" ∷ own_map lastSeq_ptr (DfracOwn 1) lastSeqM ∗
  "HnextCID" ∷ s ↦[erpc.Server :: "nextCID"] #nextCID ∗
  "Herpc" ∷ eRPCServer_own_ghost γ lastSeqM lastReplyM ∗
  "Hcids" ∷ [∗ set] cid ∈ (fin_to_set u64), ⌜uint.Z cid < uint.Z nextCID⌝%Z ∨ (is_eRPCClient_ghost γ cid 1)
.

Definition is_erpc_server (γ : erpc_names) (s:loc) : iProp Σ :=
  ∃ mu,
  "#His_srv" ∷ is_eRPCServer γ ∗
  "#Hmu" ∷ readonly (s ↦[erpc.Server :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock erpcN mu (own_erpc_server γ s)
.

Definition own_erpc_client (γ : erpc_names) (c:loc) : iProp Σ :=
  ∃ (cid seq:u64),
    "Hcid" ∷ c ↦[erpc.Client :: "cid"] #cid ∗
    "Hseq" ∷ c ↦[erpc.Client :: "nextSeq"] #seq ∗
    "Hcrpc" ∷ is_eRPCClient_ghost γ cid seq ∗
    "#Hserv" ∷ is_eRPCServer γ ∗
    "%HseqPostitive" ∷ ⌜0%Z < uint.Z seq⌝%Z
.

Polymorphic Definition is_erpc_handler (f : val) (spec : eRPCSpec)
   : iProp Σ :=
  ∀ (x : spec.(espec_ty)) (reqData : list u8) req repptr,
  {{{
    own_slice_small req byteT (DfracOwn 1) reqData ∗
    repptr ↦[slice.T byteT] (slice_val Slice.nil) ∗
    spec.(espec_Pre) x reqData
  }}}
    f (slice_val req) #repptr
  {{{ rep_sl q repData, RET #();
      repptr ↦[slice.T byteT] (slice_val rep_sl) ∗
      own_slice_small rep_sl byteT q repData ∗
      spec.(espec_Post) x reqData repData
  }}}.

Lemma wp_erpc_Server_HandleRequest spec γ s f :
  {{{ is_erpc_server γ s }}}
    Server__HandleRequest #s f
  {{{ f', RET f';
      □ (is_erpc_handler f spec -∗
      is_urpc_handler f' $ eRPCSpec_uRPC γ spec) }}}.
Proof.
  iIntros (Φ) "#Hs HΦ". wp_call. iModIntro.
  iApply "HΦ". iModIntro. clear Φ.
  iIntros "#Hf".
  iIntros ([[[γreq rid] payload] x] reqData req repptr Φ) "!# Hpre HΦ". wp_lam.
  iDestruct "Hpre" as "(Hreq & Hrepptr & Hpre)". simpl.
  iDestruct "Hpre" as "[[-> %Hseqpos] #HreqInv]".

  wp_apply (wp_ReadInt with "Hreq"). clear req.
  iIntros (req) "Hreq".
  wp_apply (wp_ReadInt with "Hreq"). clear req.
  iIntros (req) "Hreq".
  wp_pures.

  iNamed "Hs".
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]". iNamed "Hown".

  wp_loadField.
  wp_apply (wp_MapGet with "HlastSeqMap").
  iIntros (seqno ok) "[%HseqGet HlastSeqMap]".
  wp_pures.
  assert (seqno = (map_get lastSeqM rid.(Req_CID)).1) as Hseqno by rewrite HseqGet //.
  clear ok HseqGet.

  case_bool_decide as Hif.
  - (* we hit the reply table *)
    wp_loadField.
    wp_apply (map.wp_MapGet with "HlastReplyMap").
    iIntros (reply replyOk) "[%HlookupReply HlastReplyMap]".
    wp_pures.

    assert (lastSeqM !! rid.(Req_CID) = Some seqno) as HseqGet.
    { move: Hseqno. rewrite /map_get.
      destruct (lastSeqM !! rid.(Req_CID)) eqn:Hlk; rewrite /=; first naive_solver.
      intros ->. exfalso. naive_solver. }

    (* get a copy of the own_slice for the slice we're giving in reply *)
    assert (is_Some (lastReplyMV !! rid.(Req_CID))) as [xx HlastReplyMVlookup].
    {
      assert (rid.(Req_CID) ∈ dom lastSeqM).
      { by eapply elem_of_dom_2. }
      assert (rid.(Req_CID) ∈ dom lastReplyMV).
      { rewrite -HlastReplyMVdom in H. done. }
      apply elem_of_dom.
      done.
    }

    iDestruct (big_sepM2_lookup_iff with "HlastReply_structs") as %Hdom.
    assert (is_Some (lastReplyM !! rid.(Req_CID))) as [? HlastReplyMlookup].
    { apply Hdom. naive_solver. }

    iDestruct (big_sepM2_lookup_acc _ _ _ rid.(Req_CID) with "HlastReply_structs") as "[HlastReply_struct HlastReply_structs]".
    { done. }
    { done. }

    iDestruct "HlastReply_struct" as (srv_val_sl ?) "[%Hxx Hsrv_val_sl]".
    assert (xx = reply) as ->.
    {
      unfold map.map_get in HlookupReply.
      rewrite HlastReplyMVlookup in HlookupReply.
      naive_solver.
    }

    subst reply.
    iMod (own_slice_small_persist with "Hsrv_val_sl") as "#Hsrv_val_sl".
    iSpecialize ("HlastReply_structs" with "[Hsrv_val_sl]").
    {
      iExists _, _.
      iFrame "∗#".
      done.
    }
    wp_store.

    (* now split into stale/nonstale cases *)
    destruct (Z.lt_ge_cases (uint.Z rid.(Req_Seq)) (uint.Z seqno)) as [Hcase|Hcase].
    { (* Stale *)
      iMod (smaller_seqno_stale_fact _ rid seqno with "His_srv Herpc") as "HH".
      { done. }
      { done. }
      { done. }
      iDestruct "HH" as "[Hrpc #Hstale]".
      wp_loadField.
      wp_apply (release_spec with "[-HΦ Hsrv_val_sl Hrepptr]").
      {
        iFrame "∗#".
        iNext.
        iExists _,_,_, _, _, _.
        iFrame.
        done.
      }
      wp_pures. iApply "HΦ". iModIntro.
      iFrame "Hsrv_val_sl Hrepptr".
      by iLeft.
    }
    { (* Not stale *)
      assert (seqno = rid.(Req_Seq)) as -> by word.
      iMod (server_replies_to_request _ rid with "His_srv Herpc") as "HH".
      { done. }
      { done. }
      { eexists []. naive_solver. }

      iDestruct "HH" as "[#Hreceipt Hrpc]".

      (* prove that rid.(Req_CID) is in lastReplyMV (probably just add [∗ map] _ ↦ _;_ ∈ lastReplyMV ; lastSeq, True) *)
      wp_loadField.
      wp_apply (release_spec with "[-HΦ Hsrv_val_sl Hrepptr]").
      {
        iFrame "∗#".
        iNext.
        iExists _,_,_, _, _, _.
        iFrame.
        done.
      }
      wp_pures. iModIntro. iApply "HΦ".
      iFrame "Hsrv_val_sl Hrepptr".
      iRight.
      rewrite HlastReplyMlookup.
      done.
    }
  - (* we have to call the handler *)
    assert (uint.Z seqno < uint.Z rid.(Req_Seq))%Z as HseqFresh.
    { simpl. word. }

    (* get resources out of escrow *)
    iMod (server_takes_request with "HreqInv Herpc") as "HH".
    { done. }
    { rewrite -Hseqno //. }
    iDestruct "HH" as "(Hγpre & Hpre & Hproc)".

    (* *Now* we reduce the if, which takes a step. And call the handler. *)
    wp_apply ("Hf" with "[$Hreq $Hrepptr $Hpre]").
    iIntros (rep_sl ??) "(Hrepptr & Hrep & Hspecpost)".

    wp_loadField.
    wp_apply (wp_MapInsert with "HlastSeqMap").
    { done. }
    iIntros "HlastSeqMap".
    wp_load.
    wp_loadField.
    wp_apply (map.wp_MapInsert with "HlastReplyMap").
    iIntros "HlastReplyMap".
    wp_pures.

    iMod (server_completes_request with "His_srv HreqInv Hγpre Hspecpost Hproc") as "HH".
    { done. }
    { done. }
    { rewrite -Hseqno. simpl. done. }
    iDestruct "HH" as "(#Hreceipt & Hrpc)".

    wp_loadField.
    iMod (own_slice_small_persist with "Hrep") as "#Hrep".
    wp_apply (release_spec with "[-HΦ Hrep Hrepptr]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      iExists _,_,_, _, _, _.
      iFrame.
      iSplitR.
      {
        iPureIntro.
        simpl.
        rewrite !dom_insert_L.
        congruence.
      }
      iApply (big_sepM2_insert_2 with "[Hrep] HlastReply_structs").
      simpl.
      iExists _, _.
      iSplitR; first done.
      done.
    }
    wp_pures. iApply "HΦ". iFrame "∗#". done.
Qed.

Lemma wp_erpc_MakeServer γ :
  {{{ own_erpc_pre_server γ }}}
    MakeServer #()
  {{{ s, RET #s; is_erpc_server γ s }}}.
Proof.
  iIntros (Φ) "(#Hserv & ? & Hcids) HΦ".
  wp_lam.
  wp_apply (wp_allocStruct); first val_ty.
  iIntros (srv) "srv".
  iDestruct (struct_fields_split with "srv") as "srv". iNamed "srv". simpl.
  wp_pures.
  wp_apply (map.wp_NewMap).
  iIntros (lastReply_ptr) "HlastReplyMap".
  wp_storeField.
  wp_apply (wp_NewMap).
  iIntros (lastSeq_ptr) "HlastSeqMap".
  wp_storeField.
  wp_storeField.
  wp_apply (wp_new_free_lock). iIntros (lk) "Hfree".
  wp_storeField.

  iMod (alloc_lock erpcN _ lk (own_erpc_server γ srv) with "[$] [-mu HΦ]").
  {
    iNext.
    iExists _, _, _, _, _, _.
    iFrame "lastReply lastSeq nextCID".
    iFrame.
    iSplit.
    { iPureIntro. rewrite ?dom_empty_L //. }
    iSplit.
    { rewrite big_sepM2_empty //. }
    iApply (big_sepS_mono with "Hcids"); by eauto.
  }
  wp_pures. iApply "HΦ". iExists _.
  iMod (readonly_alloc_1 with "mu") as "$".
  by iFrame "∗#".
Qed.

Lemma wp_erpc_GetFreshCID s γ :
  {{{ is_erpc_server γ s }}}
    Server__GetFreshCID #s
  {{{ (cid : u64), RET #cid; erpc_make_client_pre γ cid }}}.
Proof.
  iIntros (Φ) "Hs HΦ". wp_lam.
  iNamed "Hs".
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]". iNamed "Hown".

  wp_loadField.
  wp_loadField.
  wp_apply wp_SumAssumeNoOverflow. iIntros (Hoverflow).
  wp_storeField.

  iDestruct (big_sepS_delete _ _ nextCID with "Hcids") as "[Hcid Hcids]".
  { set_solver. }

  wp_loadField.
  wp_apply (release_spec with "[-HΦ Hcid]").
  {
    iFrame "HmuInv Hlocked".
    iNext.
    iExists _,_,_,_,_,_.
    iFrame "HlastReply_structs ∗".
    iSplit; first done.
    iApply (big_sepS_delete _ _ nextCID with "[Hcids]").
    { set_solver. }
    iSplitR.
    {
      iLeft.
      iPureIntro.
      word.
    }
    iApply (big_sepS_impl with "Hcids").
    iModIntro. iIntros (??) "[%Hineq|$]".
    iLeft. iPureIntro.
    word.
  }
  wp_pures.
  iApply "HΦ".
  iModIntro.
  iDestruct "Hcid" as "[%Hbad|$]"; last done.
  exfalso.
  word.
Qed.

Polymorphic Lemma wp_erpc_NewRequest (spec : eRPCSpec) (x : spec.(espec_ty)) c payload payload_sl q γ :
  {{{
    own_erpc_client γ c ∗
    own_slice_small payload_sl byteT q payload ∗
    spec.(espec_Pre) x payload
  }}}
    Client__NewRequest #c (slice_val payload_sl)
  {{{ y req req_sl, RET (slice_val req_sl);
    own_slice req_sl byteT (DfracOwn 1) req ∗
    (* The newly computed request *persistently* satisfies the precondition
       of the underlying uRPC. *)
    □(eRPCSpec_uRPC γ spec).(spec_Pre) y req ∗
    (* And when a reply comes back, we can convert it to the [spec] level and
       relate it to the original request [payload].
       (We could give back [own_erpc_client] earlier but then we'd have to ask
       for it again here.) *)
    (∀ rep, (eRPCSpec_uRPC γ spec).(spec_Post) y req rep ={⊤}=∗
      own_erpc_client γ c ∗ ▷ spec.(espec_Post) x payload rep)
  }}}.
Proof.
  iIntros (Φ) "(Hc & Hpayload & Hpre) HΦ". wp_lam.
  iNamed "Hc".

  wp_loadField.
  wp_loadField.
  wp_apply wp_SumAssumeNoOverflow.
  iIntros (Hnooverflow).
  wp_storeField.
  wp_apply wp_slice_len.
  wp_apply (wp_NewSliceWithCap (V:=u8)).
  { apply encoding.unsigned_64_nonneg. (* FIXME why does [word] not solve this? *) }
  iIntros (req_ptr) "Hreq".
  set len := (X in (Slice.mk req_ptr _ X)).
  wp_pures.
  rewrite replicate_0.

  wp_loadField.
  wp_apply (wp_WriteInt with "Hreq"). clear req_ptr len.
  iIntros (req_sl) "Hreq".
  wp_apply (wp_WriteInt with "Hreq"). clear req_sl.
  iIntros (req_sl) "Hreq".
  wp_apply (wp_WriteBytes with "[$Hreq $Hpayload]"). clear req_sl.
  iIntros (req_sl) "[Hreq _]".
  rewrite -!app_assoc app_nil_l.
  wp_pures.

  iMod (make_request {| Req_CID:=_; Req_Seq:= _ |}
    (spec.(espec_Pre) x payload) (spec.(espec_Post) x payload) with "Hserv Hcrpc [$Hpre]")
    as "[Hcrpc [%γreq [#Hisreq Hreqtok]]]".
  { done. }
  { simpl. word. }
  iApply ("HΦ" $! (γreq, _, _, _)). iFrame "Hreq".
  cbv [eRPCSpec_uRPC spec_Pre spec_Post]. iFrame "Hisreq".
  iSplitR.
  { iPureIntro. split; first done. simpl. word. }
  iIntros "!> %rep [Hbad|Hreceipt]".
  {
    iDestruct (client_stale_seqno with "Hbad Hcrpc") as "%Hbad".
    exfalso.
    simpl in Hbad.
    word.
  }
  iMod (get_request_post with "Hisreq Hreceipt Hreqtok") as "$".
  { done. }
  iModIntro.
  iExists _, _. iFrame "∗ #".
  iPureIntro. simpl. word.
Qed.

Lemma wp_erpc_MakeClient γ cid :
  {{{ erpc_make_client_pre γ cid }}}
    MakeClient #cid
  {{{ c, RET #c; own_erpc_client γ c }}}.
Proof.
  iIntros (Φ) "[#Hserv Hcid] HΦ". wp_lam.
  wp_apply (wp_allocStruct); first val_ty.
  iIntros (c) "c".
  iDestruct (struct_fields_split with "c") as "c". iNamed "c". simpl.
  wp_pures.
  do 2 wp_storeField.

  iApply "HΦ". iExists _, _. iFrame.
  iModIntro. iFrame "Hserv".
  iPureIntro. done.
Qed.

End erpc_proof.
