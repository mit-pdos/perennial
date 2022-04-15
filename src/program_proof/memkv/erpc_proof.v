From Perennial.Helpers Require Import ModArith.
From Goose.github_com.mit_pdos.gokv Require Import erpc.
From Perennial.goose_lang Require Import adequacy.
From Perennial.base_logic Require Import lib.ghost_map lib.mono_nat lib.saved_spec.
From Perennial.program_proof Require Import grove_prelude std_proof marshal_stateless_proof.
From Perennial.program_proof.memkv Require Import urpc_proof urpc_spec erpc_lib.

Notation erpcG Σ := (erpc_lib.erpcG Σ (list u8)).

Definition erpcN := nroot .@ "erpc".

(** Spec for an eRPC handler.
This is isomorphic to uRPCSpec, but to avoid confusion we use distinct types. *)
Record eRPCSpec {Σ} :=
  { espec_rpcid : u64;
    espec_ty : Type;
    espec_Pre : espec_ty → list u8 → iProp Σ;
    espec_Post : espec_ty → list u8 → list u8 → iProp Σ }.

Section erpc_defs.
Context `{!erpcG Σ, !urpcregG Σ, !gooseGlobalGS Σ}.

Local Definition encode_request (rid : eRPCRequestID) (payload : list u8) :=
  u64_le rid.(Req_CID) ++ u64_le rid.(Req_Seq) ++ payload.

(** [Spec] is the spec of the eRPC handler;
    we compute the spec of the underlying uRPC handler. *)
Definition eRPCSpec_uRPC γerpc (spec : eRPCSpec (Σ:=Σ)) : uRPCSpec :=
 {| spec_rpcid := spec.(espec_rpcid);
    spec_ty := erpc_request_names * eRPCRequestID * (list u8) * spec.(espec_ty);
    spec_Pre :=(λ '(γreq, rid, payload, x) req,
                  ⌜req = encode_request rid payload ∧ int.Z rid.(Req_Seq) > 0⌝ ∗
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
Definition handler_erpc_spec `{!urpcregG Σ} Γsrv γerpc (host:u64) (spec : eRPCSpec) :=
  handler_urpc_spec Γsrv host (eRPCSpec_uRPC γerpc spec).

End erpc_defs.

Section erpc_proof.

Context `{hG: !heapGS Σ}.
Context `{!urpcregG Σ, !erpcG Σ}.

Definition own_erpc_server (s : loc) (γ : erpc_names) : iProp Σ :=
  ∃ (lastReply_ptr lastSeq_ptr:loc)
    (lastReplyM:gmap u64 (list u8)) (lastReplyMV:gmap u64 goose_lang.val)
    (lastSeqM:gmap u64 u64) (nextCID:u64),
  "HlastReply" ∷ s ↦[erpc.Server :: "lastReply"] #lastReply_ptr ∗
  "HlastReplyMap" ∷ map.is_map lastReply_ptr 1 (lastReplyMV, zero_val (slice.T byteT)) ∗ (* TODO: default *)
  "%HlastReplyMVdom" ∷ ⌜dom (gset u64) lastReplyMV = dom (gset u64) lastSeqM⌝ ∗
  "HlastReply_structs" ∷ ([∗ map] k ↦ v;rep ∈ lastReplyMV ; lastReplyM,
    ∃ val_sl q, ⌜v = slice_val val_sl⌝ ∗ typed_slice.is_slice_small val_sl byteT q rep) ∗
  "HlastSeq" ∷ s ↦[erpc.Server :: "lastSeq"] #lastSeq_ptr ∗
  "HlastSeqMap" ∷ is_map lastSeq_ptr 1 lastSeqM ∗
  "HnextCID" ∷ s ↦[erpc.Server :: "nextCID"] #nextCID ∗
  "Herpc" ∷ eRPCServer_own_ghost γ lastSeqM lastReplyM ∗
  "Hcids" ∷ [∗ set] cid ∈ (fin_to_set u64), ⌜int.Z cid < int.Z nextCID⌝%Z ∨ (is_eRPCClient_ghost γ cid 1)
.

Definition is_erpc_server (s:loc) γ : iProp Σ :=
  ∃ mu (cm:loc),
  "#His_srv" ∷ is_eRPCServer γ ∗
  "#Hmu" ∷ readonly (s ↦[erpc.Server :: "mu"] mu) ∗
  "#HmuInv" ∷ is_lock erpcN mu (own_erpc_server s γ)
.

Definition impl_erpc_handler_spec (f : val) (spec : eRPCSpec)
   : iProp Σ :=
  ∀ (x : spec.(espec_ty)) (reqData : list u8) req rep dummy_rep_sl dummy,
  {{{
    is_slice_small req byteT 1 reqData ∗
    rep ↦[slice.T byteT] (slice_val dummy_rep_sl) ∗
    is_slice (V:=u8) dummy_rep_sl byteT 1 dummy ∗
    spec.(espec_Pre) x reqData
  }}}
    f (slice_val req) #rep
  {{{ rep_sl q repData, RET #();
      rep ↦[slice.T byteT] (slice_val rep_sl) ∗
      is_slice_small rep_sl byteT q repData ∗
      spec.(espec_Post) x reqData repData
  }}}.

Lemma wp_erpc_Server_HandleRequest spec γ s f :
  impl_erpc_handler_spec f spec -∗
  {{{ is_erpc_server s γ }}}
    Server__HandleRequest #s f
  {{{ f', RET f'; impl_handler_spec f' (uRPCSpec_Spec $ eRPCSpec_uRPC γ spec) }}}.
Proof.
  iIntros "#Hf %Φ !# #Hs HΦ". wp_call. iModIntro.
  iApply "HΦ". clear Φ.
  iIntros (reqData Post req repptr ?? Φ) "!# Hpre HΦ". wp_lam.
  iDestruct "Hpre" as "(Hreq & Hrepptr & Hrep & Hpre)".
  iSimpl in "Hpre". iDestruct "Hpre" as ([[[γreq rid] payload] x]) "[[[-> %Hseqpos] #HreqInv] Hpost]".

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

  wp_apply (wp_and_pure ok (int.Z rid.(Req_Seq) ≤ int.Z seqno)%Z).
  { wp_pures. iPureIntro. by destruct ok. }
  { iIntros "_". wp_pures. iPureIntro. done. }

  case_bool_decide as Hif.
  - (* we hit the reply table *)
    wp_loadField.
    wp_apply (map.wp_MapGet with "HlastReplyMap").
    iIntros (reply replyOk) "[%HlookupReply HlastReplyMap]".
    wp_pures.

    destruct ok; last first.
    { exfalso. naive_solver. }
    apply map_get_true in HseqGet.
    destruct Hif as [_ HseqLe].

    (* get a copy of the is_slice for the slice we're giving in reply *)
    assert (is_Some (lastReplyMV !! rid.(Req_CID))) as [xx HlastReplyMVlookup].
    {
      assert (rid.(Req_CID) ∈ dom (gset u64) lastSeqM).
      { by eapply elem_of_dom_2. }
      assert (rid.(Req_CID) ∈ dom (gset u64) lastReplyMV).
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
    iDestruct "Hsrv_val_sl" as "[Hsrv_val_sl Hrep_val_sl]".
    iSpecialize ("HlastReply_structs" with "[Hsrv_val_sl]").
    {
      iExists _, _.
      iFrame.
      done.
    }
    wp_store.

    (* now split into stale/nonstale cases *)
    destruct (Z.lt_ge_cases (int.Z rid.(Req_Seq)) (int.Z seqno)) as [Hcase|Hcase].
    { (* Stale *)
      iMod (smaller_seqno_stale_fact _ rid seqno with "His_srv Herpc") as "HH".
      { done. }
      { done. }
      { done. }
      iDestruct "HH" as "[Hrpc #Hstale]".
      wp_loadField.
      wp_apply (release_spec with "[-HΦ Hrep_val_sl Hrepptr Hpost]").
      {
        iFrame "#∗".
        iNext.
        iExists _,_,_, _, _, _.
        iFrame.
        done.
      }
      wp_pures. iApply "HΦ". iModIntro.
      iFrame "Hrep_val_sl Hrepptr".
      iApply "Hpost". by iLeft.
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
      wp_apply (release_spec with "[-HΦ Hrep_val_sl Hrepptr Hpost]").
      {
        iFrame "#∗".
        iNext.
        iExists _,_,_, _, _, _.
        iFrame.
        done.
      }
      wp_pures. iModIntro. iApply "HΦ".
      iFrame "Hrep_val_sl Hrepptr".
      iApply "Hpost".
      iRight.
      rewrite HlastReplyMlookup.
      done.
    }
  - (* we have to call the handler *)
    assert (int.Z seqno < int.Z rid.(Req_Seq))%Z as HseqFresh.
    {
      simpl.
      destruct ok.
      {
        intuition.
        destruct (Z.le_gt_cases (int.Z rid.(Req_Seq)) (int.Z seqno)) as [Hineq|Hineq].
        { naive_solver. }
        { naive_solver. }
      }
      {
        apply map_get_false in HseqGet as [_ ->].
        simpl.
        word.
      }
    }

    (* get resources out of escrow *)
    iMod (server_takes_request with "HreqInv Herpc") as "HH".
    { done. }
    { rewrite HseqGet //. }
    iDestruct "HH" as "(Hγpre & Hpre & Hproc)".

    (* *Now* we reduce the if, which takes a step. And call the handler. *)
    wp_apply ("Hf" with "[$Hreq $Hrepptr $Hrep $Hpre]").
    iIntros (rep_sl q rep) "(Hrepptr & Hrep & Hspecpost)".

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
    { rewrite HseqGet. simpl. done. }
    iDestruct "HH" as "(#Hreceipt & Hrpc)".

    wp_loadField.
    iDestruct "Hrep" as "[Hrep1 Hrep2]".
    wp_apply (release_spec with "[-HΦ Hrep1 Hrepptr Hpost]").
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
      iApply (big_sepM2_insert_2 with "[Hrep2] HlastReply_structs").
      simpl.
      iExists _, _.
      iSplitR; first done.
      done.
    }
    wp_pures. iApply "HΦ". iFrame.
    iApply "Hpost". iModIntro. iRight. done.
Qed.

Lemma wp_erpc_MakeServer (b : bool) γ :
  {{{
       "#His_srv" ∷ is_eRPCServer γ ∗
       "HRPCserver_own" ∷ eRPCServer_own_ghost γ ∅ ∅ ∗
       "Hcids" ∷ [∗ set] cid ∈ (fin_to_set u64), is_eRPCClient_ghost γ cid 1
  }}}
    MakeServer #b
  {{{
       s, RET #s; is_erpc_server s γ
  }}}.
Proof.
Abort.

End erpc_proof.
