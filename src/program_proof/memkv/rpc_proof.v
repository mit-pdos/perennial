From Goose.github_com.mit_pdos.gokv.urpc Require Import rpc.
From iris.base_logic.lib Require Import saved_prop.
From Perennial.program_proof Require Import dist_prelude.
From Perennial.program_proof Require Import marshal_proof.
From Perennial.algebra Require Import auth_map.
From Perennial.base_logic Require Export lib.ghost_map lib.mono_nat.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

Definition rpc_spec_map {Σ} : Type :=
  gmap u64 { X: Type & ((X → list u8 → iProp Σ) * (X → list u8 → list u8 → iProp Σ))%type }.

(** Request descriptor: data describing a particular request *)
Record rpc_req_desc := ReqDesc {
  rpc_reg_rpcid  : u64;
  rpc_reg_auxtype : Type;
  rpc_reg_aux : rpc_reg_auxtype;
  rpc_reg_args : list u8;
  rpc_reg_saved : gname; (* Saved pred storing what the reply needs to satisfy *)
  rpc_reg_done : loc;
  rpc_reg_rep_ptr : loc;
}.

Class rpcregG (Σ : gFunctors) := RpcRegG {
  rpcreg_mono_natG :> mono_natG Σ;
  rpcreg_mapG :> mapG Σ u64 rpc_req_desc;
  rpcreg_escrowG :> mapG Σ u64 unit;
  rpcreg_savedG :> savedPredG Σ (list u8);
  rpcreg_specs : gmap u64 (@rpc_spec_map Σ) (* [u64] here is a host name *)
}.

Section rpc_proof.

Context `{!rpcregG Σ}.
Context `{!heapG Σ}.

(* A host-specific mapping from rpc ids on that host to pre/post conditions *)
Definition urpc_serverN : namespace := nroot.@"urpc_server".
Definition urpc_clientN : namespace := nroot.@"urpc_client".
Definition urpc_lockN : namespace := nroot.@"urpc_lock".
Definition urpc_escrowN : namespace := nroot.@"urpc_escrow".

Record client_chan_gnames := {
  ccmapping_name : gname;
  ccescrow_name : gname;
  ccextracted_name : gname;
}.

Definition client_chan_inner_msg (Γ : client_chan_gnames) (host : u64) m : iProp Σ :=
    ∃ (rpcid seqno : u64) reqData replyData X Post (x : X) γ d rep,
       "%Henc" ∷ ⌜ has_encoding (msg_data m) [EncUInt64 seqno;
                                              EncUInt64 (length replyData); EncBytes replyData] ⌝ ∗
       "#Hseqno" ∷ ptsto_ro (ccmapping_name Γ) seqno (ReqDesc rpcid X x reqData γ d rep) ∗
       "#HPost_saved" ∷ saved_pred_own γ (Post x reqData) ∗
       "#HPost" ∷ inv urpc_escrowN (Post x reqData replyData ∨ ptsto_mut (ccescrow_name Γ) seqno 1 tt).

Definition client_chan_inner (Γ : client_chan_gnames) (host: u64) : iProp Σ :=
  ∃ ms, "Hchan" ∷ host c↦ ms ∗
  "Hmessages" ∷ [∗ set] m ∈ ms, client_chan_inner_msg Γ host m.

Definition server_chan_inner_msg (host : u64) (specs : rpc_spec_map) m : iProp Σ :=
    ∃ rpcid seqno args X Pre Post (x : X) Γ γ d rep,
       "%Henc" ∷ ⌜ has_encoding (msg_data m) [EncUInt64 rpcid; EncUInt64 seqno;
                                              EncUInt64 (length args); EncBytes args] ⌝ ∗
       "%Hlookup_spec" ∷ ⌜ specs !! rpcid = Some (existT X (Pre, Post)) ⌝ ∗
       "#Hseqno" ∷ ptsto_ro (ccmapping_name Γ) seqno (ReqDesc rpcid X x args γ d rep) ∗
       "#HPre" ∷ □ (Pre x args) ∗
       "#HPost_saved" ∷ saved_pred_own γ (Post x args) ∗
       "#Hclient_chan_inv" ∷ inv urpc_clientN (client_chan_inner Γ (msg_sender m)).

Definition server_chan_inner (host: u64) : iProp Σ :=
  ∃ specs ms,
  "%Hspecs_map" ∷ ⌜ rpcreg_specs !! host = Some specs ⌝ ∗
  "Hchan" ∷ host c↦ ms ∗
  "Hmessages" ∷ [∗ set] m ∈ ms, server_chan_inner_msg host specs m.

Definition handler_is : ∀ (X:Type) (host:u64) (rpcid:u64) (Pre:X → list u8 → iProp Σ)
                          (Post:X → list u8 → list u8 → iProp Σ), iProp Σ :=
  λ X host rpcid Pre Post, (∃ (specs: rpc_spec_map),
  "%Hspecs_map_handler" ∷ ⌜ rpcreg_specs !! host = Some specs ⌝ ∗
  "%Hprepost" ∷ ⌜ specs !! rpcid = Some (existT X (Pre, Post)) ⌝ ∗
  "#Hserver_inv" ∷ inv urpc_serverN (server_chan_inner host)
)%I.

Global Instance handler_is_pers_instance X host rpcid pre post : Persistent (handler_is X host rpcid pre post).
Proof. apply _. Qed.

Definition RPCClient_lock_inner Γ  (cl : loc) (lk : loc) (host : u64) mref : iProp Σ :=
  ∃ pending reqs estoks extoks (n : u64),
            "%Hnpos" ∷ ⌜ 0 < int.Z n ⌝%Z ∗
            "%Hdom_range" ∷ ⌜ ∀ id, (0 < int.Z id < int.Z n)%Z ↔ id ∈ dom (gset u64) reqs ⌝ ∗
            "%Hdom_eq_es" ∷ ⌜ dom (gset u64) reqs = dom (gset u64) estoks ⌝ ∗
            "%Hdom_eq_ex" ∷ ⌜ dom (gset u64) reqs = dom (gset u64) extoks ⌝ ∗
            "%Hdom_pending" ∷ ⌜ dom (gset u64) pending ⊆ dom (gset u64) reqs  ⌝ ∗
            "seq" ∷ cl ↦[RPCClient :: "seq"] #n ∗
            "Hmapping_ctx" ∷ map_ctx (ccmapping_name Γ) 1 reqs ∗
            "Hescrow_ctx" ∷ map_ctx (ccescrow_name Γ) 1 estoks ∗
            "Hextracted_ctx" ∷ map_ctx (ccextracted_name Γ) 1 extoks ∗
            "Hpending_map" ∷ map.is_map mref 1 (pending, zero_val (struct.ptrT callback)) ∗
            "Hreqs" ∷ [∗ map] seqno ↦ req ∈ reqs, ∃ (Post : rpc_reg_auxtype req → list u8 → list u8 → iProp Σ),
                 "Hreg_entry" ∷  ptsto_ro (ccmapping_name Γ) seqno req ∗
                 "HPost_saved" ∷ saved_pred_own (rpc_reg_saved req) (Post (rpc_reg_aux req) (rpc_reg_args req)) ∗
                 (* (1) Reply thread has not yet processed, so it is in pending
                    and we have escrow token *)
                 ((∃ (cb : loc) (cb_cond : loc) dummy,
                    "Hpending_cb" ∷ ⌜ pending !! seqno  = Some #cb ⌝ ∗
                    "#reply" ∷ readonly (cb ↦[callback :: "reply"] #(rpc_reg_rep_ptr req)) ∗
                    "#done" ∷ readonly (cb ↦[callback :: "done"] #(rpc_reg_done req)) ∗
                    "#cond" ∷ readonly (cb ↦[callback :: "cond"] #cb_cond) ∗
                    "Hescrow" ∷ ptsto_mut (ccescrow_name Γ) seqno 1 tt ∗
                    "Hcond" ∷ is_cond cb_cond #lk ∗
                    "Hrep_ptr" ∷ (rpc_reg_rep_ptr req) ↦[slice.T byteT] dummy ∗
                    "Hdone" ∷ (rpc_reg_done req) ↦[boolT] #false) ∨
                 (* (2) Reply thread has received message, removed from pending,
                    but caller has not extracted ownership *)
                 (∃ reply rep_sl,
                    "Hpending_cb" ∷ ⌜ pending !! seqno  = None ⌝ ∗
                    "HPost" ∷ (Post (rpc_reg_aux req) (rpc_reg_args req) reply) ∗
                    "Hrep_ptr" ∷ (rpc_reg_rep_ptr req) ↦[slice.T byteT] (slice_val rep_sl) ∗
                    "Hrep_data" ∷ typed_slice.is_slice rep_sl byteT 1 reply ∗
                    "Hdone" ∷ (rpc_reg_done req) ↦[boolT] #true) ∨
                 (* (3) Caller has extracted ownership *)
                 (⌜ pending !! seqno  = None ⌝ ∗ ptsto_mut (ccextracted_name Γ) seqno 1 tt)).

Definition RPCClient_own (cl : loc) (host:u64) : iProp Σ :=
  ∃ Γ (lk : loc) r (mref : loc),
    "#Hstfields" ∷ ("mu" ∷ readonly (cl ↦[RPCClient :: "mu"] #lk) ∗
    "#send" ∷ readonly (cl ↦[RPCClient :: "send"] send_endpoint host r) ∗
    "#pending" ∷ readonly (cl ↦[RPCClient :: "pending"] #mref)) ∗
    "#Hchan" ∷ inv urpc_clientN (client_chan_inner Γ r) ∗
    "#Hlk" ∷ is_lock urpc_lockN #lk (RPCClient_lock_inner Γ cl lk host mref).

Definition RPCClient_reply_own (cl : loc) (r : chan) : iProp Σ :=
  ∃ Γ host (lk : loc) (mref : loc),
    "#Hstfields" ∷ ("mu" ∷ readonly (cl ↦[RPCClient :: "mu"] #lk) ∗
    "#pending" ∷ readonly (cl ↦[RPCClient :: "pending"] #mref)) ∗
    "#Hchan" ∷ inv urpc_clientN (client_chan_inner Γ r) ∗
    "#Hlk" ∷ is_lock urpc_lockN #lk (RPCClient_lock_inner Γ cl lk host mref).

(* TODO: move this *)
Global Instance is_map_AsMapsTo mref hd :
  AsMapsTo (map.is_map mref 1 hd) (λ q, map.is_map mref q hd).
Proof.
  split; try apply _; eauto.
  rewrite /fractional.Fractional.
  rewrite /map.is_map.
  iIntros (p q). iSplit.
  - iDestruct 1 as (mv Heq) "H".
    iDestruct (fractional.fractional_split with "H") as "(H1&H2)".
    iSplitL "H1"; iExists _; iFrame; eauto.
  - iIntros "(H1&H2)".
    iDestruct "H1" as (hd1 Heq) "H1".
    iDestruct "H2" as (hd2 Heq') "H2".
    iDestruct (heap_mapsto_agree with "[$H1 $H2]") as %Heq''. subst.
    iExists _; iSplit; first done.
    iApply (fractional.fractional_split). iFrame.
Qed.

Definition own_RPCServer (s : loc) (handlers: gmap u64 val) : iProp Σ :=
  ∃ mref def,
  "#Hhandlers_map" ∷ readonly (map.is_map mref 1 (handlers, def)) ∗
  "#handlers" ∷ readonly (s ↦[RPCServer :: "handlers"] #mref).

Definition is_rpcHandler {X:Type} (f:val) Pre Post : iProp Σ :=
  ∀ (x:X) req rep dummy_rep_sl (reqData:list u8),
  {{{
      is_slice req byteT 1 reqData ∗
      rep ↦[slice.T byteT] (slice_val dummy_rep_sl) ∗
      ▷ Pre x reqData
  }}}
    f (slice_val req) #rep
  {{{
       rep_sl (repData:list u8), RET #(); rep ↦[slice.T byteT] (slice_val rep_sl) ∗
         is_slice rep_sl byteT 1 repData ∗
         ▷ Post x reqData repData
  }}}.

Lemma wp_MakeRPCServer (handlers : gmap u64 val) (mref:loc) (def : val) k :
  {{{
       map.is_map mref 1 (handlers, def)
  }}}
    MakeRPCServer #mref @ k ; ⊤
  {{{
      (s:loc), RET #s; own_RPCServer s handlers
  }}}.
Proof.
  iIntros (Φ) "Hmap HΦ".
  wp_lam.
  iApply wp_fupd.
  wp_apply (wp_allocStruct).
  { repeat econstructor. }
  iIntros (s) "Hs".
  iDestruct (struct_fields_split with "Hs") as "Hs". iNamed "Hs".
  unshelve (iMod (readonly_alloc_1 with "handlers") as "#handlers"); [| apply _ |].
  unshelve (iMod (readonly_alloc_1 with "Hmap") as "#Hmap"); [| apply _ |].
  iApply "HΦ". iExists _, _.
  iFrame "# ∗". eauto.
Qed.

Lemma handler_is_init (host : u64) specs:
   rpcreg_specs !! host = Some specs →
   host c↦ ∅ ={⊤}=∗
   [∗ map] rpcid ↦ spec ∈ specs,
   let X := projT1 spec in
   let Pre := fst (projT2 spec) in
   let Post := snd (projT2 spec) in
   handler_is X host rpcid Pre Post.
Proof.
  iIntros (Hlookup) "Hchan".
  iMod (inv_alloc urpc_serverN _ ((server_chan_inner host)) with "[Hchan]") as "#Hinv".
  { iNext. iExists _, _. iFrame "%". iFrame.
    rewrite big_sepS_empty //. }
  iModIntro.
  iAssert (∀ specs', ⌜ specs' ⊆ specs ⌝ →
           [∗ map] rpcid↦spec ∈ specs',
             handler_is (projT1 spec) host rpcid (projT2 spec).1 (projT2 spec).2)%I as "H"; last first.
  { iApply "H". eauto. }
  iIntros (specs').
  iInduction specs' as [| id spec] "IH" using map_ind.
  { rewrite big_sepM_empty //. }
  { iIntros (?). rewrite big_sepM_insert //; iSplit; last first.
    { iApply "IH". iPureIntro.
      etransitivity; last eassumption. apply insert_subseteq; eauto. }
    iExists _. iFrame "% #".
    iPureIntro.
    apply: lookup_weaken; eauto.
    rewrite lookup_insert.
    f_equal. destruct spec => //=.
    destruct p; eauto.
  }
Qed.

Definition rpc_handler_mapping host handlers : iProp Σ :=
  ([∗ map] rpcid↦handler ∈ handlers, ∃ (X : Type) (Pre : X → list u8 → iProp Σ)
                                      (Post : X → list u8 → list u8 → iProp Σ),
      handler_is X host rpcid Pre Post ∗ is_rpcHandler handler Pre Post)%I.

Lemma non_empty_rpc_handler_mapping_inv host handlers :
  dom (gset u64) handlers ≠ ∅ →
  rpc_handler_mapping host handlers -∗
  ∃ specs,
  "%Hspecs_map_handler" ∷ ⌜ rpcreg_specs !! host = Some specs ⌝ ∗
  "#Hserver_inv" ∷ inv urpc_serverN (server_chan_inner host) ∗
  "#Hhandlers" ∷ ([∗ map] rpcid↦handler ∈ handlers, ∃ (X : Type) (Pre : X → list u8 → iProp Σ)
                                                      (Post : X → list u8 → list u8 → iProp Σ),
                                                      ⌜ specs !! rpcid = Some (existT X (Pre, Post)) ⌝ ∗
                                                      is_rpcHandler handler Pre Post).
Proof.
  iIntros (Hdom) "Hmapping".
  iInduction handlers as [| rpcid handler] "IH" using map_ind.
  { rewrite dom_empty_L in Hdom; congruence. }
  rewrite /rpc_handler_mapping big_sepM_insert //.
  iDestruct "Hmapping" as "(H&Hmapping)".
  destruct (decide (dom (gset _) m = ∅)) as [Hemp|Hemp].
  { iNamed "H". iDestruct "H" as "(Hhandler_is&His_rpcHandler)".
    iNamed "Hhandler_is". iExists _. iFrame "% #".
    rewrite big_sepM_insert //. iSplitL "His_rpcHandler".
    { iExists _, _, _. eauto. }
    apply dom_empty_inv_L in Hemp. rewrite Hemp big_sepM_empty. eauto.
  }
  iDestruct ("IH" with "[//] [$]") as (specs) "HIH".
  iNamed "HIH". iExists _; iFrame "% #".
  rewrite big_sepM_insert //. iFrame "#".
  { iNamed "H". iDestruct "H" as "(Hhandler_is&His_rpcHandler)".
    rewrite /handler_is.
    iDestruct "Hhandler_is" as (specs' Hlookup' Hprepost') "H".
    assert (specs = specs') as ->; first by congruence.
    iExists _, _, _. eauto. }
Qed.

Definition handlers_complete host (handlers : gmap u64 val) :=
  (match rpcreg_specs !! host with
   | Some specs => dom (gset _) handlers = dom (gset _) specs
   | _ => True
   end).

Lemma wp_RPCServer__readThread s host handlers mref def :
  dom (gset u64) handlers ≠ ∅ →
  handlers_complete host handlers →
  "#His_rpc_map" ∷ rpc_handler_mapping host handlers ∗
  "#Hhandlers_map" ∷ readonly (map.is_map mref 1 (handlers, def)) ∗
  "#handlers" ∷ readonly (s ↦[RPCServer :: "handlers"] #mref) -∗
  WP RPCServer__readThread #s (recv_endpoint host) {{ _, True }}.
Proof.
  iIntros (Hdom Hcomplete).
  iNamed 1.
  wp_lam. wp_pures.
  wp_apply (wp_forBreak_cond'); [ iNamedAccu |].
  iIntros "!> _".
  wp_pures.
  iDestruct (non_empty_rpc_handler_mapping_inv with "[$]") as "H"; first auto.
  iNamed "H".
  wp_apply (wp_Receive).
  iInv "Hserver_inv" as "Hchan_inner" "Hclo".
  iDestruct "Hchan_inner" as (specs' ms) "(>%Hlookup&>Hchan'&#Hchan_inner)".
  assert (specs' = specs) as ->.
  { congruence. }
  iApply (ncfupd_mask_intro _); first set_solver+.
  iIntros "Hclo'".
  iExists _. iFrame "Hchan'". iNext.
  iIntros (err m) "(Hchan&Herr)".
  iAssert (if err then True else server_chan_inner_msg host specs m)%I with "[Hchan_inner Herr]" as "Hmsg".
  { destruct err; auto.
    iDestruct "Herr" as %Hin.
    iApply (big_sepS_elem_of with "Hchan_inner"); first eassumption.
  }
  iMod ("Hclo'") as "_".
  iMod ("Hclo" with "[Hchan]") as "_".
  { iNext. iExists _, _. iFrame "% #". eauto. }
  iModIntro.
  iIntros (r) "Hsl".
  wp_pures.
  destruct err; wp_pures.
  { eauto. }
  iNamed "Hmsg".
  iDestruct (is_slice_small_acc with "Hsl") as "(Hslice&Hslice_close)".
  wp_apply (wp_new_dec with "Hslice"); first eauto.
  iIntros (?) "Hdec".
  wp_pures.

  wp_apply (wp_Dec__GetInt with "[$Hdec]").
  iIntros "Hdec".
  wp_pures.

  wp_apply (wp_Dec__GetInt with "[$Hdec]").
  iIntros "Hdec".
  wp_pures.

  wp_apply (wp_Dec__GetInt with "[$Hdec]").
  iIntros "Hdec".
  wp_pures.
  wp_apply (wp_Dec__GetBytes' with "[$Hdec $Hslice_close]").
  { admit. } (* TODO : overflow *)
  iIntros (s') "Hsl".
  wp_pures.

  wp_lam. wp_pures.
  wp_apply (wp_ref_of_zero); first done.
  iIntros (sl') "Hsl'".
  wp_pures.
  wp_loadField.
  iMod (readonly_load with "Hhandlers_map") as (?) "Hmap_read".
  wp_apply (map.wp_MapGet with "[$]").
  iIntros (v ok) "(%Hget&_)".
  rewrite /map.map_get in Hget.
  destruct (handlers !! rpcid) as [f|] eqn:Hlookup'; last first.
  { exfalso.
    rewrite /handlers_complete Hlookup in Hcomplete.
    apply not_elem_of_dom in Hlookup'.
    rewrite Hcomplete in Hlookup'.
    eapply Hlookup'. eapply @elem_of_dom; eauto.
    { apply _. }
  }
  rewrite //= in Hget. inversion Hget; subst. wp_pures.
  iDestruct (big_sepM_lookup with "Hhandlers") as "H"; eauto.
  iNamed "H". iDestruct "H" as (Hlookup_spec') "His_rpcHandler".
  rewrite Hlookup_spec in Hlookup_spec'.
  inversion Hlookup_spec'. subst.
  apply Eqdep.EqdepTheory.inj_pair2 in H1; subst.
  apply Eqdep.EqdepTheory.inj_pair2 in H2; subst.
  rewrite /is_rpcHandler.
  replace (zero_val (slice.T byteT)) with
      (slice_val {| Slice.ptr := null; Slice.sz := U64 0; Slice.cap := U64 0 |}) by auto.
  wp_apply ("His_rpcHandler" with "[$Hsl $Hsl' HPre]").
  { iDestruct "HPre" as "#HPre". iNext. iFrame "#". }
  iIntros (rep_sl repData) "(Hsl'&His_slice&HPost)".
  wp_pures.
  wp_apply (wp_LoadAt with "[$]"). iIntros "Hsl'".
  wp_apply (wp_slice_len).
  wp_pures.
  wp_apply (wp_new_enc).
  iIntros (enc) "Henc".
  wp_pures.
  wp_apply (wp_Enc__PutInt with "Henc").
  { admit. (* TODO: overflow *) }
  iIntros "Henc".
  wp_pures.
  wp_apply (wp_LoadAt with "[$]"). iIntros "Hsl'".
  wp_apply (wp_slice_len).
  wp_apply (wp_Enc__PutInt with "Henc").
  { admit. (* TODO: overflow *) }
  iIntros "Henc".
  wp_pures.
  wp_apply (wp_LoadAt with "[$]"). iIntros "Hsl'".
  iDestruct (is_slice_small_read with "His_slice") as "(His_slice&Hsl_close)".
  iDestruct (is_slice_small_sz with "His_slice") as %Hsz.
  wp_apply (wp_Enc__PutBytes with "[$Henc $His_slice]").
  { admit. } (* TODO: overflow *)
  iIntros "[Henc Hslice]".
  wp_pures.
  wp_apply (wp_Enc__Finish with "[$Henc]").
  iIntros (rep_sl_msg rep_msg_data).
  iIntros "(%Hencoding&Hlength&Hmsg_slice)".

  (* Send *)
  iDestruct (is_slice_small_read with "Hmsg_slice") as "(Hmsg_slice&_)".
  wp_apply (wp_Send with "[$Hmsg_slice]").
  { admit. } (* TODO: overflow *)
  iMod (inv_alloc urpc_escrowN _ (Post0 x args repData ∨ ptsto_mut (ccescrow_name Γ) seqno 1 tt)
          with "[HPost]") as "#HPost_escrow".
  { eauto. }
  iInv "Hclient_chan_inv" as "Hclient_chan_inner" "Hclo".
  iDestruct "Hclient_chan_inner" as (ms_rep) "(>Hchan'&#Hclient_chan_inner)".
  iApply (ncfupd_mask_intro _); first set_solver+.
  iIntros "Hclo'".
  iExists _. iFrame "Hchan'". iNext.
  iIntros "Hchan'".
  iMod "Hclo'" as "_".
  iMod ("Hclo" with "[Hchan' Hlength]").
  { iNext. iExists _. iFrame.
    destruct (decide (Message host rep_msg_data ∈ ms_rep)).
    { assert (ms_rep ∪ {[Message host rep_msg_data]} = ms_rep) as -> by set_solver. iFrame "#". }
    iApply big_sepS_union; first by set_solver.
    iFrame "#".
    iApply big_sepS_singleton.
    iExists _, _, _, _, _, _, _.
    iExists _, _, _.
    iFrame "#".
    iPureIntro. simpl. rewrite ?app_nil_l //= in Hencoding. rewrite Hsz.
    assert (U64 (Z.of_nat (int.nat (rep_sl.(Slice.sz)))) = rep_sl.(Slice.sz)) as ->.
    { word. }
    eauto.
  }
  iModIntro. iIntros "?". wp_pures; eauto.
Admitted.

Lemma wp_StartRPCServer (host : u64) (handlers : gmap u64 val) (s : loc) (n:u64) :
  dom (gset u64) handlers ≠ ∅ →
  handlers_complete host handlers →
  {{{
       own_RPCServer s handlers ∗
      [∗ map] rpcid ↦ handler ∈ handlers, (∃ X Pre Post, handler_is X host rpcid Pre Post ∗ is_rpcHandler handler Pre Post)
  }}}
    RPCServer__Serve #s #host #n
  {{{
      RET #(); True
  }}}.
Proof.
  iIntros (?? Φ) "(Hserver&#His_rpc_map) HΦ".
  wp_lam. wp_pures.
  wp_apply (wp_Listen). wp_pures.
  iNamed "Hserver".
  wp_apply (wp_ref_to).
  { repeat econstructor. }
  iIntros (i) "Hi".
  wp_pures.
  iApply (wp_forUpto (λ _, emp%I) with "[] [$Hi]"); swap 2 3.
  { word. }
  { iNext. iIntros "(?&?)". iApply "HΦ"; eauto. }
  iIntros (ival Φ') "!> (?&Hi&Hlt) HΦ'".
  wp_apply (wp_fork).
  { wp_apply (wp_RPCServer__readThread with "[$]"); eauto. }
  wp_pures. iModIntro. iApply "HΦ'"; iFrame.
Qed.

Lemma wp_RPCClient__replyThread cl r :
  RPCClient_reply_own cl r -∗
  WP RPCClient__replyThread #cl (recv_endpoint r) {{ _, True }}.
Proof.
  iIntros "H". iNamed "H".
  wp_lam. wp_pures.
  wp_apply (wp_forBreak' True%I with "[-]").
  { eauto. }
  iIntros "!> _". wp_pures.
  wp_apply (wp_Receive).
  iInv "Hchan" as "Hchan_inner" "Hclo".
  iDestruct "Hchan_inner" as (ms) "(>Hchan'&#Hchan_inner)".
  iApply (ncfupd_mask_intro _); first set_solver+.
  iIntros "Hclo'".
  iExists _. iFrame "Hchan'". iNext.
  iIntros (err m) "(Hchan'&Herr)".
  iAssert (if err then True else client_chan_inner_msg Γ r m)%I with "[Hchan_inner Herr]" as "Hmsg".
  { destruct err; auto.
    iDestruct "Herr" as %Hin.
    iApply (big_sepS_elem_of with "Hchan_inner"); first eassumption.
  }
  iMod "Hclo'". iMod ("Hclo" with "[Hchan']").
  { iNext. iExists _. iFrame. eauto. }
  iModIntro. iIntros (s) "Hs".
  wp_pures. wp_if_destruct.
  { iModIntro. iLeft. eauto. }
  wp_pures.
  iNamed "Hmsg".
  iDestruct (typed_slice.is_slice_small_acc with "Hs") as "[Hsl Hsl_close]".
  wp_apply (wp_new_dec with "[$Hsl]").
  { done. }
  iIntros (?) "Hdec".
  wp_pures.

  wp_apply (wp_Dec__GetInt with "[$Hdec]").
  iIntros "Hdec".
  wp_pures.

  wp_apply (wp_Dec__GetInt with "[$Hdec]").
  iIntros "Hdec".
  wp_pures.
  wp_apply (wp_Dec__GetBytes' with "[$Hdec $Hsl_close]").
  { admit. } (* TODO : overflow *)
  iIntros (?) "Hsl".
  wp_pures.
  iNamed "Hstfields".
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "(Hlked&Hlock_inner)".
  iNamed "Hlock_inner".
  wp_pures.
  wp_loadField.
  wp_apply (map.wp_MapGet with "[$]").
  iIntros (v ok) "(%Hget&Hpending_map)".
  wp_pures.
  wp_if_destruct; last first.
  { wp_pures. wp_loadField. wp_apply (release_spec with "[-]").
    { iFrame "# ∗". iNext. iExists _, _, _, _, _. iFrame.
      eauto. }
    wp_pures. eauto.
  }
  wp_pures. wp_loadField. wp_apply (map.wp_MapDelete with "[$]").
  iIntros "Hpending_map". wp_pures.
  iDestruct (map_ro_valid with "Hmapping_ctx [$]") as %Hlookup_reg.
  iDestruct (big_sepM_delete with "Hreqs") as "(H&Hclo)"; first eauto.
  iEval (simpl) in "H".
  iFreeze "Hclo".
  iRename "HPost_saved" into "Hsaved".
  iNamed "H".
  iDestruct "H" as "[Hcase1|[Hcase2|Hcase3]]".
  { iNamed "Hcase1".
    iDestruct "Hpending_cb" as %Hpending_cb.
    apply map.map_get_true in Hget.
    rewrite Hget in Hpending_cb. inversion Hpending_cb as [Heq].
    wp_loadField.
    wp_apply (wp_StoreAt with "[Hrep_ptr]").
    { apply slice_val_ty. }
    { iFrame. }
    iIntros "Hrep_ptr". wp_pures.
    wp_loadField.
    wp_apply (wp_StoreAt with "[Hdone]").
    { econstructor. econstructor. }
    { iFrame. }
    iIntros "Hdone". wp_pures. wp_loadField.
    wp_apply (wp_condSignal with "[$]").
    iApply fupd_wp.
    iInv "HPost" as "HPost_inner" "Hclo''".
    iDestruct "HPost_inner" as "[HPost_val|>Hescrow']"; last first.
    { iDestruct (ptsto_valid_2 with "Hescrow [$]") as %Hval. rewrite //= in Hval. }
    iMod ("Hclo''" with "[Hescrow]").
    { iRight. eauto. }
    iModIntro. wp_pures.
    wp_loadField.
    wp_apply (release_spec with "[-]"); last first.
    { wp_pures. eauto. }
    iFrame "Hlk Hlked". iNext. iExists (delete seqno pending) , _, _, _, _.
    iFrame. iFrame "%".
    iSplit.
    { iPureIntro. rewrite dom_delete_L. set_solver. }
    iApply big_sepM_delete; first eassumption.
    iSplitR "Hclo"; last first.
    { iThaw "Hclo". iApply (big_sepM_mono with "Hclo").
      iIntros (?? Hlookup) "H". iNamed "H".
      iExists _; iFrame.  iDestruct "H" as "[Hcase1|[Hcase2|Hcase3]]".
      { iNamed "Hcase1". iLeft. iExists _, _, _. iFrame "# ∗".
        iDestruct "Hpending_cb" as %Hpending_cb'. iPureIntro.
        destruct (decide (seqno = k)).
        { subst. rewrite lookup_delete in Hlookup; congruence. }
        rewrite lookup_delete_ne //=. }
      { iNamed "Hcase2". iRight. iLeft. iExists _, _. iFrame "# ∗".
        iDestruct "Hpending_cb" as %Hpending_cb'. iPureIntro.
        apply lookup_delete_None; auto.
      }
      { iDestruct "Hcase3" as "(%&H)". iRight. iRight. iFrame. iPureIntro.
        apply lookup_delete_None; auto.
      }
    }
    iExists _. iFrame "#".  iRight. iLeft.
    iExists _, _.
    iFrame "HPost_val". simpl. iFrame "Hrep_ptr Hdone".
    iSplit.
    { iPureIntro. apply lookup_delete_None; auto. }
    iFrame.
  }
  { iNamed "Hcase2". iDestruct "Hcase2" as "(%Hlookup&_)".
    exfalso. apply map.map_get_true in Hget. congruence. }
  { iDestruct "Hcase3" as "(%Hlookup&_)".
    exfalso. apply map.map_get_true in Hget. congruence. }
Admitted.

Lemma wp_MakeRPCClient (host:u64):
  {{{
       True
  }}}
    MakeRPCClient #host
  {{{
       (cl_ptr:loc), RET #cl_ptr; RPCClient_own cl_ptr host
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_lam.
  wp_apply (wp_Connect).
  iIntros (err r) "Hr".
  destruct err.
  { admit. (* TODO FIXME: RPCClient should check this error, or panic *) }
  wp_pures.

  replace (ref (InjLV #null))%E with (NewMap (struct.ptrT callback)) by naive_solver.
  wp_apply (wp_new_free_lock). iIntros (lk) "Hfree".
  wp_pures.
  wp_apply (map.wp_NewMap).
  iIntros (mref) "Hmref".

  wp_apply (wp_allocStruct).
  { enough (val_ty (send_endpoint host r) Sender) by naive_solver.
    econstructor.
  }
  iIntros (cl) "Hcl".
  iNamed "Hcl".
  iDestruct (struct_fields_split with "Hcl") as "Hcl". iNamed "Hcl".
  wp_pures.
  (* TODO: why do I have to unshelve this, when in other cases it appears to get picked up automatically *)
  unshelve (iMod (readonly_alloc_1 with "mu") as "#mu"); [| apply _ |].
  unshelve (iMod (readonly_alloc_1 with "send") as "#send"); [| apply _ |].
  unshelve (iMod (readonly_alloc_1 with "pending") as "#pending"); [| apply _ |].

  iMod (map_init (∅ : gmap u64 rpc_req_desc)) as (γccmapping) "Hmapping_ctx".
  iMod (map_init (∅ : gmap u64 unit)) as (γccescrow) "Hescrow_ctx".
  iMod (map_init (∅ : gmap u64 unit)) as (γccextracted) "Hextracted_ctx".
  set (Γ := {| ccmapping_name := γccmapping; ccescrow_name := γccescrow;
               ccextracted_name := γccextracted |}).
  iMod (alloc_lock urpc_lockN _ _ (RPCClient_lock_inner Γ cl lk host mref) with
            "Hfree [Hmapping_ctx Hescrow_ctx Hextracted_ctx seq Hmref]") as "#Hlock".
  { iNext. iExists ∅, ∅, ∅, ∅, _. iFrame.
    rewrite ?dom_empty_L.
    iSplit; first done.
    iSplit.
    { iPureIntro. split; last by set_solver. word. }
    iSplit; first done.
    iSplit; first done.
    rewrite big_sepM_empty //.
  }
  iMod (inv_alloc urpc_clientN _ (client_chan_inner Γ r) with "[Hr]") as "#Hchan_inv".
  { iNext. iExists ∅. iFrame. rewrite big_sepS_empty //. }
  wp_bind (Fork _).
  iApply wp_fork.
  { iNext. wp_pures. iApply wp_RPCClient__replyThread. iExists _, _, _, _. iFrame "#". }
  iNext. wp_pures. iModIntro. iApply "HΦ".
  iExists _, _, _, _. iFrame "#".
Admitted.

Lemma wp_RPCClient__Call {X:Type} (x:X) (cl_ptr:loc) (rpcid:u64) (host:u64) req rep_ptr
      dummy_sl_val (reqData:list u8) Pre Post :
  {{{
      is_slice req byteT 1 reqData ∗
      rep_ptr ↦[slice.T byteT] dummy_sl_val ∗
      handler_is X host rpcid Pre Post ∗
      RPCClient_own cl_ptr host ∗
      □(▷ Pre x reqData)
  }}}
    RPCClient__Call #cl_ptr #rpcid (slice_val req) #rep_ptr
  {{{
       (b:bool) rep_sl (repData:list u8), RET #b;
       rep_ptr ↦[slice.T byteT] (slice_val rep_sl) ∗
       RPCClient_own cl_ptr host ∗
       typed_slice.is_slice req byteT 1 reqData ∗
       typed_slice.is_slice rep_sl byteT 1 repData ∗
       (⌜b = true⌝ ∨ ⌜b = false⌝ ∗ (▷ Post x reqData repData))
  }}}.
Proof.
  iIntros (Φ) "H HΦ".
  wp_lam.
  wp_pures.
  iDestruct "H" as "(Hslice&Hrep_ptr&Hhandler&Hclient&#HPre)".
  iNamed "Hclient". iNamed "Hstfields".
  replace (#false) with (zero_val boolT) by auto.
  wp_apply (wp_ref_of_zero); first done.
  iIntros (cb_done) "cb_done".
  wp_loadField.
  wp_bind (lock.newCond _).
  wp_apply (wp_newCond with "[$]").
  iIntros (cb_cond) "#cond".
  wp_apply (wp_allocStruct).
  { naive_solver. }
  wp_pures.
  iIntros (cb) "Hcb".
  wp_pures.
  iRename "cond" into "cond'".
  iDestruct (struct_fields_split with "Hcb") as "Hcb". iNamed "Hcb".
  unshelve (iMod (readonly_alloc_1 with "reply") as "#reply"); [| apply _ |].
  unshelve (iMod (readonly_alloc_1 with "done") as "#done"); [| apply _ |].
  unshelve (iMod (readonly_alloc_1 with "cond") as "#cond"); [| apply _ |].
  wp_loadField.
  wp_apply (wp_StoreAt with "[$]"); first eauto.
  iIntros "done'".
  wp_pures.
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "(Hlked&Hlock_inner)".
  iNamed "Hlock_inner".
  wp_pures.
  wp_loadField. wp_pures.
  wp_loadField. wp_storeField.
  wp_loadField.
  wp_apply (map.wp_MapInsert with "[$]").
  iIntros "Hpending_map".
  wp_pures.
  wp_loadField.
  iMod (saved_pred_alloc (Post x reqData)) as (γ) "#Hsaved".
  assert (reqs !! n = None).
  { apply not_elem_of_dom. rewrite -Hdom_range. lia. }
  iMod (map_alloc_ro n (ReqDesc rpcid X x reqData γ cb_done rep_ptr)
          with "Hmapping_ctx") as "(Hmapping_ctx&#Hreg)"; auto.
  iMod (map_alloc n tt with "Hescrow_ctx") as "(Hescrow_ctx&Hescrow)".
  { apply not_elem_of_dom. rewrite -Hdom_eq_es -Hdom_range. lia. }
  iMod (map_alloc n tt with "Hextracted_ctx") as "(Hextracted_ctx&Hextracted)".
  { apply not_elem_of_dom. rewrite -Hdom_eq_ex -Hdom_range. lia. }
  wp_apply (release_spec with "[-Hslice Hhandler HΦ Hextracted]").
  { iFrame "Hlk". iFrame "Hlked". iNext. iExists _, _, _, _, _.
    iFrame. rewrite ?dom_insert_L.
    assert (int.Z (word.add n 1) = int.Z n + 1)%Z as ->.
    { (* XXX: not true because of overflow, so there's a potential bug here, albeit irrelevant *) admit. }
    iSplit.
    { iPureIntro. word. }
    iSplit.
    { iPureIntro. intros. set_unfold. split.
      * intros Hrange.
        assert (0 < int.Z id < int.Z n ∨ int.Z id = int.Z n)%Z.
        { word. }
        { naive_solver word. }
      * intros [Heq|Hin].
        { subst. word. }
        { apply Hdom_range in Hin. word. } }
    iSplit; first (iPureIntro; congruence).
    iSplit; first (iPureIntro; congruence).
    iSplit; first (iPureIntro; set_solver).
    rewrite big_sepM_insert; last first.
    { apply not_elem_of_dom. rewrite -Hdom_range. lia. }
    iEval (rewrite /named).
    iSplitR "Hreqs"; last first.
    { iApply (big_sepM_mono with "Hreqs").
      iIntros (k req' Hlookup). iDestruct 1 as (Post') "H".
      iExists Post'.
      assert (n ≠ k).
      { intros Heq. congruence. }
      setoid_rewrite lookup_insert_ne; eauto.
    }
    iExists Post.
    iFrame "Hreg Hsaved".
    iLeft. iExists _, _, _. iFrame "# ∗".
    iPureIntro. rewrite lookup_insert //. }
  wp_pures.
  wp_apply (wp_slice_len).
  wp_pures.
  wp_apply (wp_new_enc).
  iIntros (enc) "Henc".
  wp_pures.
  wp_apply (wp_Enc__PutInt with "Henc").
  { admit. (* TODO: overflow *) }
  iIntros "Henc".
  wp_pures.
  wp_apply (wp_Enc__PutInt with "Henc").
  { admit. (* TODO: overflow *) }
  iIntros "Henc".
  wp_pures.
  wp_apply (wp_slice_len).
  wp_apply (wp_Enc__PutInt with "Henc").
  { admit. (* TODO: overflow *) }
  iIntros "Henc".
  wp_pures.
  iDestruct (is_slice_small_read with "Hslice") as "(Hslice&Hslice_close)".
  iDestruct (is_slice_small_sz with "Hslice") as %Hsz.
  wp_apply (wp_Enc__PutBytes with "[$Henc $Hslice]").
  { admit. } (* TODO: overflow *)
  iIntros "[Henc Hslice]".
  wp_pures.
  wp_apply (wp_Enc__Finish with "[$Henc]").
  iIntros (rep_sl repData).
  iIntros "(%Hhas_encoding & % & Hrep_sl)".
  wp_pures.
  wp_loadField.
  iDestruct (is_slice_to_small with "Hrep_sl") as "Hrep_sl".
  iNamed "Hhandler".
  wp_apply (wp_Send with "[$]").
  { admit. } (* TODO: overflow *)
  iInv "Hserver_inv" as "Hserver_inner" "Hclo".
  iDestruct "Hserver_inner" as (specs' ms) "(>%Hlookup&>Hchan'&H)".
  assert (specs' = specs) as ->.
  { congruence. }
  iApply (ncfupd_mask_intro _); first set_solver+.
  iIntros "Hclo'".
  iExists _. iFrame "Hchan'". iNext.
  iIntros "Hchan'". iNamed "H".
  iMod ("Hclo'") as "_".
  iMod ("Hclo" with "[Hmessages Hchan']") as "_".
  { iNext. iExists specs, _. iFrame.
    iSplit; first done.
    destruct (decide (Message r repData ∈ ms)).
    { assert (ms ∪ {[Message r repData]} = ms) as -> by set_solver. iFrame. }
    iApply big_sepS_union; first by set_solver.
    iFrame "Hmessages".
    iApply big_sepS_singleton.
    iExists _, _, _, _, _, _, _.
    iExists _, _, _, _.
    iFrame "#". iSplit; eauto.
    iPureIntro. simpl. rewrite ?app_nil_l //= in Hhas_encoding. rewrite Hsz.
    assert (U64 (Z.of_nat (int.nat (req.(Slice.sz)))) = req.(Slice.sz)) as ->.
    { word. }
    eauto.
  }
  iModIntro. iIntros "Hsl_rep".
  wp_pures.
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "Hi".
  wp_pures.
  wp_apply (wp_forBreak_cond' with "[-]").
  { iNamedAccu. }
  iModIntro. iNamed 1.
  wp_pures.
  iDestruct "Hi" as "(Hi&Hlock_inner)".
  iNamed "Hlock_inner".
  iDestruct (map_ro_valid with "Hmapping_ctx [$]") as %Hlookup_reg.
  iDestruct (big_sepM_lookup_acc with "Hreqs") as "(H&Hclo)"; first eauto.
  iEval (simpl) in "H".
  iFreeze "Hclo".
  iNamed "H".
  iDestruct "H" as "[Hcase1|[Hcase2|Hcase3]]".
  { iNamed "Hcase1". wp_loadField.
    iDestruct "Hcase1" as "(#?&#?&#?&Hrest)". iNamed "Hrest".
    wp_apply (wp_LoadAt with "[$]"). iIntros "Hdone".
    wp_pures. iThaw "Hclo".
    iDestruct ("Hclo" with "[Hdone Hcond Hescrow Hpending_cb Hrep_ptr]") as "H".
    { simpl. iExists _. iFrame "Hreg". iFrame "Hsaved". iFrame "#". iLeft. iExists _, _, _. iFrame "# ∗". }
    wp_loadField.
    wp_apply (wp_condWait with "[$cond' $Hlk $Hi H HPost_saved
                 Hpending_map Hmapping_ctx Hescrow_ctx Hextracted_ctx seq]").
    { iExists _, _, _, _, _. iFrame. eauto. }
    iIntros "Hi". wp_pures. iModIntro.
    iLeft. iSplit; first eauto. iFrame "HΦ". iFrame "Hslice_close". iFrame. }
  { iNamed "Hcase2". wp_loadField.
    wp_apply (wp_LoadAt with "[$]"). iIntros "Hdone".
    iDestruct (saved_pred_agree _ _ _ reply with "HPost_saved Hsaved") as "#Hequiv".
    wp_pures. iRight. iModIntro. iSplit; first done.
    wp_pures. wp_loadField.
    iThaw "Hclo".
    iDestruct ("Hclo" with "[Hdone Hextracted Hpending_cb]") as "H".
    { simpl. iExists _. iFrame "Hreg". iFrame "Hsaved". iFrame "#". iRight. iRight.
      iSplit; eauto. }
    wp_apply (release_spec with "[$Hlk $Hi H HPost_saved
                 Hpending_map Hmapping_ctx Hescrow_ctx Hextracted_ctx seq]").
    { iExists _, _, _, _, _. iFrame. eauto. }
    wp_pures. iModIntro.
    iRewrite ("Hequiv") in "HPost".
    iApply ("HΦ" $! false _ reply).
    iFrame "Hrep_ptr Hrep_data".
    iSplitL "".
    { iExists _, _, _, _. iFrame "#". }
    iSplitL "Hslice Hslice_close".
    { iApply "Hslice_close". eauto. }
    iRight. iFrame. eauto.
  }
  { iDestruct "Hcase3" as "(?&Hex)".
    iDestruct (ptsto_valid_2 with "Hex [$]") as %Hval.
    exfalso. rewrite //= in Hval.
  }
Admitted.

End rpc_proof.
