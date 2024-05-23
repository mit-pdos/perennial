From Perennial.Helpers Require Import ModArith.
From Goose.github_com.mit_pdos.gokv Require Import urpc.
From iris.algebra Require Import gset.
From iris.base_logic.lib Require Import saved_prop.
From Perennial.program_proof Require Import grove_prelude std_proof.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.algebra Require Import auth_map.
From Perennial.base_logic Require Import lib.ghost_map lib.mono_nat lib.saved_spec.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

(** Request descriptor: data describing a particular request *)
Record urpc_req_desc := ReqDesc {
  urpc_reg_rpcid  : u64;
  urpc_reg_args : list u8;
  urpc_reg_saved : gname; (* Saved pred storing what the reply needs to satisfy *)
  urpc_reg_done : loc;
  urpc_reg_rep_ptr : loc;
}.

Class urpcregG (Σ : gFunctors) := URpcRegG {
  urpcreg_mono_natG :> mono_natG Σ;
  urpcreg_mapG :> mapG Σ u64 urpc_req_desc;
  urpcreg_escrowG :> mapG Σ u64 unit;
  urpcreg_saved_gname_mapG :> mapG Σ u64 gname;
  urpcreg_saved_urpc_specG :> savedSpecG Σ (list u8) (list u8);
  urpcreg_savedG :> savedPredG Σ (list u8);
  urpcreg_domG :> inG Σ (agreeR (gsetO u64));
}.

Definition urpcregΣ :=
  #[mono_natΣ; mapΣ u64 urpc_req_desc; mapΣ u64 unit; mapΣ u64 gname; savedSpecΣ (list u8) (list u8); savedPredΣ (list u8);
   GFunctor (agreeR (gsetO u64))].

Global Instance subG_urpcregG {Σ} :
  subG urpcregΣ Σ → urpcregG Σ.
Proof. solve_inG. Qed.

Section urpc_global_defs.

Context `{!urpcregG Σ}.
Context `{HPRE: !gooseGlobalGS Σ}.

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

Record server_chan_gnames := {
  scmap_name : gname;
  scset_name : gname;
}.

Definition reply_chan_inner_msg (Γ : client_chan_gnames) m : iProp Σ :=
    ∃ (rpcid seqno : u64) reqData replyData Post γ d rep,
       "%Hlen_reply" ∷ ⌜ length replyData = uint.nat (length replyData) ⌝ ∗
       "%Henc" ∷ ⌜ msg_data m = u64_le seqno ++ replyData ⌝ ∗
       "#Hseqno" ∷ ptsto_ro (ccmapping_name Γ) seqno (ReqDesc rpcid reqData γ d rep) ∗
       "#HPost_saved" ∷ saved_pred_own γ DfracDiscarded (Post) ∗
       "#HPost" ∷ inv urpc_escrowN (Post replyData ∨ ptsto_mut (ccescrow_name Γ) seqno 1 tt).

Definition reply_chan_inner (Γ : client_chan_gnames) (c: chan) : iProp Σ :=
  ∃ ms, "Hchan" ∷ c c↦ ms ∗
  "Hmessages" ∷ [∗ set] m ∈ ms, reply_chan_inner_msg Γ m.

Implicit Type Spec : savedSpecO Σ (list u8) (list u8).

(* Crucially, this is persistent: note the □Spec *)
Definition server_chan_inner_msg Γsrv m : iProp Σ :=
    ∃ rpcid seqno args Spec Post Γ γ1 γ2 d rep rpcdom,
       "%Hlen_args" ∷ ⌜ length args = uint.nat (W64 (Z.of_nat (length args))) ⌝ ∗
       "#Hdom1" ∷ own (scset_name Γsrv) (to_agree (rpcdom)) ∗
       "%Hdom2" ∷ ⌜ rpcid ∈ rpcdom ⌝ ∗
       "%Henc" ∷ ⌜ msg_data m = u64_le rpcid ++ u64_le seqno ++ args  ⌝ ∗
       "#Hseqno" ∷ ptsto_ro (ccmapping_name Γ) seqno (ReqDesc rpcid args γ1 d rep) ∗
       "#Hspec_name" ∷ ptsto_ro (scmap_name Γsrv) rpcid γ2 ∗
       "#Hspec_saved" ∷ saved_spec_own γ2 Spec ∗
       "#HPre" ∷ □ Spec args Post ∗
       "#HPost_saved" ∷ saved_pred_own γ1 DfracDiscarded (Post) ∗
       "#Hclient_chan_inv" ∷ inv urpc_clientN (reply_chan_inner Γ (msg_sender m)).

Definition server_chan_inner (c: chan) γmap : iProp Σ :=
  ∃ ms,
  "Hchan" ∷ c c↦ ms ∗
  "Hmessages" ∷ [∗ set] m ∈ ms, server_chan_inner_msg γmap m.

(** The given [rpcid] on the given [host] has the given [Spec], where [Spec] is
    a predicate-transformer (similar to WP). *)
Definition is_urpc_spec_pred Γsrv (host:chan) (rpcid:u64) Spec : iProp Σ :=
  (∃ γ rpcdom,
   "#Hdom1" ∷ own (scset_name Γsrv) (to_agree (rpcdom)) ∗
   "%Hdom2" ∷ ⌜ rpcid ∈ rpcdom ⌝ ∗
  "#Hspec_name" ∷ ptsto_ro (scmap_name Γsrv) rpcid γ ∗
  "#Hspec_saved" ∷ saved_spec_own γ Spec ∗
  "#Hserver_inv" ∷ inv urpc_serverN (server_chan_inner host Γsrv)
)%I.

Global Instance is_urpc_spec_pred_pers γ host rpcid Spec :
  Persistent (is_urpc_spec_pred γ host rpcid Spec).
Proof. apply _. Qed.

Global Instance is_urpc_spec_pred_contractive γ host rpcid :
  Contractive (is_urpc_spec_pred γ host rpcid).
Proof. solve_contractive. Qed.

Definition is_urpc_dom Γsrv (d: gset u64) :=
  own (scset_name Γsrv) (to_agree d).

End urpc_global_defs.

Section urpc_proof.

Context `{hG: !heapGS Σ}.
Context `{hReg: !urpcregG Σ}.

(** This function [f] implements the given handler spec. *)
Definition is_urpc_handler_pred (f:val)
    (Spec : list u8 → (list u8 → iProp Σ) → iProp Σ)
   : iProp Σ :=
  ∀ (reqData:list u8) Post req rep,
  {{{
    own_slice_small req byteT (DfracOwn 1) reqData ∗
    rep ↦[slice.T byteT] (slice_val Slice.nil) ∗
    Spec reqData Post
  }}}
    f (slice_val req) #rep
  {{{ rep_sl q repData, RET #();
      rep ↦[slice.T byteT] (slice_val rep_sl) ∗
      own_slice_small rep_sl byteT q repData ∗
      Post repData
  }}}.

Definition Client_lock_inner Γ  (cl : loc) (lk : loc) mref : iProp Σ :=
  ∃ pending reqs (estoks extoks : gmap u64 unit) (n : u64),
            "%Hnpos" ∷ ⌜ 0 < uint.Z n ⌝%Z ∗
            "%Hdom_range" ∷ ⌜ ∀ id, (0 < uint.Z id < uint.Z n)%Z ↔ id ∈ dom reqs ⌝ ∗
            "%Hdom_eq_es" ∷ ⌜ dom reqs = dom estoks ⌝ ∗
            "%Hdom_eq_ex" ∷ ⌜ dom reqs = dom extoks ⌝ ∗
            "%Hdom_pending" ∷ ⌜ dom pending ⊆ dom reqs  ⌝ ∗
            "seq" ∷ cl ↦[Client :: "seq"] #n ∗
            "Hmapping_ctx" ∷ map_ctx (ccmapping_name Γ) 1 reqs ∗
            "Hescrow_ctx" ∷ map_ctx (ccescrow_name Γ) 1 estoks ∗
            "Hextracted_ctx" ∷ map_ctx (ccextracted_name Γ) 1 extoks ∗
            "Hpending_map" ∷ map.own_map mref (DfracOwn 1) (pending, zero_val ptrT) ∗
            "Hreqs" ∷ [∗ map] seqno ↦ req ∈ reqs,
                 ∃ (Post : list u8 → iProp Σ),
                 "Hreg_entry" ∷  ptsto_ro (ccmapping_name Γ) seqno req ∗
                 "HPost_saved" ∷ saved_pred_own (urpc_reg_saved req) DfracDiscarded (Post) ∗
                 (* (1) Reply thread has not yet processed, so it is in pending
                    and we have escrow token *)
                 ((∃ (cb : loc) (cb_cond : loc) dummy (aborted : bool),
                    "%Hpending_cb" ∷ ⌜ pending !! seqno  = Some #cb ⌝ ∗
                    "#reply" ∷ readonly (cb ↦[Callback :: "reply"] #(urpc_reg_rep_ptr req)) ∗
                    "#state" ∷ readonly (cb ↦[Callback :: "state"] #(urpc_reg_done req)) ∗
                    "#cond" ∷ readonly (cb ↦[Callback :: "cond"] #cb_cond) ∗
                    "Hescrow" ∷ ptsto_mut (ccescrow_name Γ) seqno 1 tt ∗
                    "#Hcond" ∷ is_cond cb_cond #lk ∗
                    "Hrep_ptr" ∷ (urpc_reg_rep_ptr req) ↦[slice.T byteT] dummy ∗
                    "Hstate" ∷ (urpc_reg_done req) ↦[uint64T] #(LitInt $ if aborted then 2 else 0)) ∨
                 (* (2) Reply thread has received message, removed from pending,
                    but caller has not extracted ownership *)
                 (∃ reply rep_sl,
                    "%Hpending_cb" ∷ ⌜ pending !! seqno  = None ⌝ ∗
                    "HPost" ∷ (Post reply) ∗
                    "Hrep_ptr" ∷ (urpc_reg_rep_ptr req) ↦[slice.T byteT] (slice_val rep_sl) ∗
                    "Hrep_data" ∷ own_slice_small rep_sl byteT (DfracOwn 1) reply ∗
                    "Hstate" ∷ (urpc_reg_done req) ↦[uint64T] #1) ∨
                 (* (3) Caller has extracted ownership *)
                 (⌜ pending !! seqno  = None ⌝ ∗ ptsto_mut (ccextracted_name Γ) seqno 1 tt)).

Definition is_uRPCClient (cl : loc) (srv : chan) : iProp Σ :=
  ∃ Γ (lk : loc) client (mref : loc),
    "#Hstfields" ∷ ("mu" ∷ readonly (cl ↦[Client :: "mu"] #lk) ∗
    "#conn" ∷ readonly (cl ↦[Client :: "conn"] connection_socket client srv) ∗
    "#pending" ∷ readonly (cl ↦[Client :: "pending"] #mref)) ∗
    "#Hchan" ∷ inv urpc_clientN (reply_chan_inner Γ client) ∗
    "#Hlk" ∷ is_lock urpc_lockN #lk (Client_lock_inner Γ cl lk mref).

Global Instance is_uRPCClient_pers cl srv :
  Persistent (is_uRPCClient cl srv).
Proof. apply _. Qed.

Definition Client_reply_own (cl : loc) : iProp Σ :=
  ∃ Γ (lk : loc) client srv (mref : loc),
    "#Hstfields" ∷ ("mu" ∷ readonly (cl ↦[Client :: "mu"] #lk) ∗
    "#conn" ∷ readonly (cl ↦[Client :: "conn"] connection_socket client srv) ∗
    "#pending" ∷ readonly (cl ↦[Client :: "pending"] #mref)) ∗
    "#Hchan" ∷ inv urpc_clientN (reply_chan_inner Γ client) ∗
    "#Hlk" ∷ is_lock urpc_lockN #lk (Client_lock_inner Γ cl lk mref).

(* TODO: move this *)
Global Instance own_map_AsMapsTo mref (hd:gmap u64 val * val) :
  AsMapsTo (map.own_map mref (DfracOwn 1) hd) (λ q, map.own_map mref (DfracOwn q) hd).
Proof.
  split; try apply _; eauto.
  rewrite /fractional.Fractional.
  rewrite /map.own_map.
  iIntros (p q). iSplit.
  - iDestruct 1 as (mv Heq) "H".
    iDestruct "H" as "(H1&H2)".
    iSplitL "H1"; iExists _; iFrame; eauto.
  - iIntros "(H1&H2)".
    iDestruct "H1" as (hd1 Heq) "H1".
    iDestruct "H2" as (hd2 Heq') "H2".
    iDestruct (heap_pointsto_agree with "[$H1 $H2]") as %Heq''. subst.
    iExists _; iSplit; first done.
    by iSplitL "H1".
Qed.

Definition own_Server (s : loc) (handlers: gmap u64 val) : iProp Σ :=
  ∃ mref def,
  "#Hhandlers_map" ∷ readonly (map.own_map mref (DfracOwn 1) (handlers, def)) ∗
  "#handlers" ∷ readonly (s ↦[Server :: "handlers"] #mref).

Lemma wp_MakeServer (handlers : gmap u64 val) (mref:loc) (def : val) :
  {{{
       map.own_map mref (DfracOwn 1) (handlers, def)
  }}}
    MakeServer #mref @ ⊤
  {{{
      (s:loc), RET #s; own_Server s handlers
  }}}.
Proof.
  iIntros (Φ) "Hmap HΦ".
  wp_lam.
  iApply wp_fupd.
  wp_apply (wp_allocStruct); first val_ty.
  iIntros (s) "Hs".
  iDestruct (struct_fields_split with "Hs") as "Hs". iNamed "Hs".
  unshelve (iMod (readonly_alloc_1 with "handlers") as "#handlers"); [| apply _ |].
  unshelve (iMod (readonly_alloc_1 with "Hmap") as "#Hmap"); [| apply _ |].
  iApply "HΦ". iExists _, _.
  iFrame "∗#". eauto.
Qed.

Definition urpc_handler_mapping (γ : server_chan_gnames) (host : u64) (handlers : gmap u64 val) : iProp Σ :=
  ([∗ map] rpcid↦handler ∈ handlers, ∃ Spec,
      is_urpc_spec_pred γ host rpcid Spec ∗
      is_urpc_handler_pred handler Spec)%I.

Lemma non_empty_urpc_handler_mapping_inv γ host handlers :
  dom handlers ≠ ∅ →
  urpc_handler_mapping γ host handlers -∗
  "#Hserver_inv" ∷ inv urpc_serverN (server_chan_inner host γ) ∗
  "#Hhandlers" ∷ ([∗ map] rpcid↦handler ∈ handlers, ∃ Spec γs,
                          ptsto_ro (scmap_name γ) rpcid γs ∗
                          saved_spec_own γs Spec ∗
                          is_urpc_handler_pred handler Spec)%I.
Proof.
  iIntros (Hdom) "Hmapping".
  iInduction handlers as [| rpcid handler] "IH" using map_ind.
  { rewrite dom_empty_L in Hdom; congruence. }
  rewrite /urpc_handler_mapping big_sepM_insert //.
  iDestruct "Hmapping" as "(H&Hmapping)".
  destruct (decide (dom m = ∅)) as [Hemp|Hemp].
  { iNamed "H". iDestruct "H" as "(His_urpc_spec_pred&His_urpcHandler)".
    iNamed "His_urpc_spec_pred". iFrame "% #".
    rewrite big_sepM_insert //. iSplitL "His_urpcHandler".
    { iExists Spec, _.
      iFrame "∗#". }
    apply dom_empty_iff_L in Hemp. rewrite Hemp big_sepM_empty. eauto.
  }
  iDestruct ("IH" with "[//] [$]") as "HIH".
  iNamed "HIH". iFrame "% #".
  rewrite big_sepM_insert //. iFrame "#".
  { iNamed "H". iDestruct "H" as "(His_urpc_spec_pred&His_urpcHandler)".
    rewrite /is_urpc_spec_pred.
    iDestruct "His_urpc_spec_pred" as (g0 rpcdom) "H".
    iDestruct "H" as "(#Hdom1&%Hdom2&#Hspec_name&#Hspec_saved&H)".
    iExists _, _.  iFrame "∗#".
  }
Qed.

Definition handlers_complete Γ (handlers : gmap u64 val) :=
  (is_urpc_dom Γ (dom handlers)).

Lemma wp_Server__readThread γ s host client handlers mref def :
  dom handlers ≠ ∅ →
  "#Hcomplete" ∷ handlers_complete γ handlers ∗
  "#His_rpc_map" ∷ urpc_handler_mapping γ host handlers ∗
  "#Hhandlers_map" ∷ readonly (map.own_map mref (DfracOwn 1) (handlers, def)) ∗
  "#handlers" ∷ readonly (s ↦[Server :: "handlers"] #mref) -∗
  WP Server__readThread #s (connection_socket host client) {{ _, True }}.
Proof.
  iIntros (Hdom).
  iNamed 1.
  wp_lam. wp_pures.
  wp_apply (wp_forBreak_cond'); [ iNamedAccu |].
  iIntros "!> _".
  wp_pures.
  iDestruct (non_empty_urpc_handler_mapping_inv with "[$]") as "H"; first auto.
  iNamed "H".
  wp_apply (wp_Receive).
  iInv "Hserver_inv" as "Hchan_inner" "Hclo".
  iDestruct "Hchan_inner" as (ms) "(>Hchan'&#Hchan_inner)".
  iApply (ncfupd_mask_intro _); first set_solver+.
  iIntros "Hclo'".
  iExists _.
  iFrame "Hchan'".
  iIntros (err m) "(Hchan&Herr)".
  iAssert (if err then True else ▷ server_chan_inner_msg γ (Message client m))%I with "[Hchan_inner Herr]" as "Hmsg".
  { destruct err; auto.
    iDestruct "Herr" as %Hin. iNext.
    iApply (big_sepS_elem_of with "Hchan_inner"); first eassumption.
  }
  iMod ("Hclo'") as "_".
  iMod ("Hclo" with "[Hchan]") as "_".
  { iNext. iExists _. iFrame "% #". eauto.  }
  iModIntro.
  iIntros (r) "Hsl".
  wp_pures.
  destruct err; wp_pures.
  { iRight. iModIntro. iSplit; first done. wp_pures. eauto. }
  iNamed "Hmsg".

  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
  cbn in Henc. subst m.
  wp_apply (wp_ReadInt with "Hsl"). clear r.
  iIntros (r) "Hsl".
  wp_apply (wp_ReadInt with "Hsl"). clear r.
  iIntros (r) "Hsl".
  wp_pures.

  wp_apply (wp_fork with "[-]"); last first.
  {
    wp_pures.
    iLeft.
    done.
  }
  iNext.

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
  {
    iDestruct (own_valid_2 with "Hcomplete Hdom1") as %Hval.
    exfalso.
    apply to_agree_op_inv_L in Hval.
    apply not_elem_of_dom in Hlookup'.
    congruence.
  }
  rewrite //= in Hget. inversion Hget; subst.
  iDestruct (big_sepM_lookup with "Hhandlers") as "H"; eauto.
  iNamed "H". iDestruct "H" as "(#Hsname&#Hsaved&#His_urpcHandler)".
  iDestruct (ptsto_ro_agree with "Hspec_name Hsname") as %->.

  iDestruct (saved_spec_agree _ _ _ args Post with "Hspec_saved Hsaved")
    as "#Hequiv".
  wp_pures.

  rewrite /is_urpc_handler_pred.
  rewrite zero_slice_val.
  wp_apply ("His_urpcHandler" with "[$Hsl $Hsl']").
  {
    instantiate (1:=Post).
    iRewrite -"Hequiv". iFrame "#".
  }

  iIntros (rep_sl rep_q repData) "(Hsl' & Hown_slice & HPost)".
  iDestruct (own_slice_small_sz with "Hown_slice") as %Hsz.
  wp_pures.
  wp_apply (wp_LoadAt with "[$]"). iIntros "Hsl'".
  wp_apply (wp_slice_len).

  wp_apply (wp_NewSliceWithCap (V:=u8)).
  { apply encoding.unsigned_64_nonneg. (* FIXME why does [word] not solve this? *) }
  iIntros (ptr) "Hmsg".
  rewrite replicate_0.
  wp_apply (wp_WriteInt with "Hmsg"). clear ptr.
  iIntros (msg_sl) "Hmsg".
  wp_load.
  wp_apply (wp_WriteBytes with "[$Hmsg $Hown_slice]"). clear msg_sl.
  iIntros (msg_sl) "[Hmsg_slice _]".
  rewrite -!app_assoc app_nil_l.

  (* Send *)
  iDestruct (own_slice_small_read with "Hmsg_slice") as "(Hmsg_slice&_)".
  wp_apply (wp_Send with "[$Hmsg_slice]").
  iMod (inv_alloc urpc_escrowN _ (Post repData ∨ ptsto_mut (ccescrow_name Γ) seqno 1 tt)
          with "[HPost]") as "#HPost_escrow".
  { eauto. }
  iInv "Hclient_chan_inv" as "Hclient_chan_inner" "Hclo".
  iDestruct "Hclient_chan_inner" as (ms_rep) "(>Hchan'&#Hclient_chan_inner)".
  iApply (ncfupd_mask_intro _); first set_solver+.
  iIntros "Hclo'".
  iExists _. iFrame "Hchan'".
  iIntros (msg_sent) "Hchan'".
  iMod "Hclo'" as "_".
  iMod ("Hclo" with "[Hchan']").
  { iNext. iExists _.
    iFrame.
    destruct msg_sent; last first.
    { iFrame "#". }
    iEval (rewrite [ms_rep ∪ _]comm_L).
    iApply big_sepS_insert_2; last done.
    iExists _, _, _, _, _, _, _, _.
    iFrame "#".
    iPureIntro. cbn. split; last done.
    word.
  }
  iModIntro. iIntros (err) "[%?]". wp_pures; eauto.
Qed.

Lemma wp_StartServer_pred γ (host : u64) (handlers : gmap u64 val) (s : loc) :
  dom handlers ≠ ∅ →
  {{{
      handlers_complete γ handlers ∗
      own_Server s handlers ∗
      [∗ map] rpcid ↦ handler ∈ handlers,
      (∃ Spec, is_urpc_spec_pred γ host rpcid Spec ∗ is_urpc_handler_pred handler Spec)
  }}}
    Server__Serve #s #host
  {{{
      RET #(); True
  }}}.
Proof.
  iIntros (? Φ) "(#Hcomplete&Hserver&#His_rpc_map) HΦ".
  wp_lam. wp_pures.
  wp_apply (wp_Listen). wp_pures.
  iNamed "Hserver".
  wp_apply (wp_fork).
  2:{ wp_pures. by iApply "HΦ". }

  wp_apply (wp_forBreak_cond'); [ iNamedAccu |].
  iIntros "!# _". wp_pures.
  wp_apply (wp_Accept).
  iIntros (client) "_". wp_pures.
  wp_apply (wp_fork).
  { wp_apply (wp_Server__readThread with "[]"); eauto. }
  wp_pures. iModIntro. by iLeft.
Qed.

Lemma wp_Client__replyThread cl :
  Client_reply_own cl -∗
  WP Client__replyThread #cl {{ _, True }}.
Proof.
  iIntros "H". iNamed "H". iNamed "Hstfields".
  wp_lam. wp_pures.
  wp_apply (wp_forBreak' True%I with "[-]").
  { eauto. }
  iIntros "!> _". wp_pures.
  wp_loadField.
  wp_apply (wp_Receive).
  iInv "Hchan" as "Hchan_inner" "Hclo".
  iDestruct "Hchan_inner" as (ms) "(>Hchan'&#Hchan_inner)".
  iApply (ncfupd_mask_intro _); first set_solver+.
  iIntros "Hclo'".
  iExists _. iFrame "Hchan'".
  iIntros (err m) "(Hchan'&Herr)".
  iAssert (if err then True else ▷ reply_chan_inner_msg Γ (Message srv m))%I with "[Hchan_inner Herr]" as "Hmsg".
  { destruct err; auto.
    iDestruct "Herr" as %Hin. iNext.
    iApply (big_sepS_elem_of with "Hchan_inner"); first eassumption.
  }
  iMod "Hclo'" as "_". iMod ("Hclo" with "[Hchan']") as "_".
  { iNext. iExists _. iFrame. eauto. }
  iModIntro. iIntros (s) "Hs".
  wp_pures.
  destruct err.
  {
    simpl; wp_pures.

    (* Loop (MapIter) to wake up all waiting clients *)
    wp_loadField.
    wp_apply (acquire_spec with "[$]").
    iIntros "(Hlked&Hlock_inner)".
    iNamed "Hlock_inner".

    wp_loadField.
    wp_apply (map.wp_MapIter with "Hpending_map Hreqs").
    { instantiate (1:=λ k v, ⌜pending !! k = Some v⌝%I).
      iApply big_sepM_intro. by auto. }
    { (* Loop body *)
      iIntros (k v Φ) "!# [Hreqs %Hm] HΦ".
      wp_pures. (* First step to strip ▷, then freeze. *)
      iFreeze "HΦ".
      assert (is_Some (reqs !! k)) as [req Hreq].
      { apply elem_of_dom, Hdom_pending, elem_of_dom. eauto. }
      iDestruct (big_sepM_lookup_acc _ _ k req with "Hreqs") as "[Hreq Hreqs]"; first done.
      iNamed "Hreq".
      iDestruct "Hreq" as "[Hreq|[Hreq|[% _]]]"; last first.
      { exfalso. by destruct (pending !! k). }
      { iNamed "Hreq". exfalso. by destruct (pending !! k). }
      iNamed "Hreq".
      rewrite Hpending_cb in Hm.
      injection Hm as [= <-].
      wp_loadField.
      wp_store.
      wp_loadField.
      wp_apply (wp_condSignal with "Hcond").
      iDestruct ("Hreqs" with "[-HΦ]") as "Hreqs".
      { iExists _. iFrame "Hreg_entry HPost_saved". iLeft. iExists _, _, _, true. by iFrame "∗#". }
      iClear "Hcond". iThaw "HΦ". iApply "HΦ".
      iFrame "Hreqs".
      instantiate (1:=λ k v, ⌜True⌝%I). done.
    }
    iIntros "[Hmap [Hreqs _]]".
    wp_loadField.
    wp_apply (release_spec with "[-]").
    { iFrame "Hlked Hlk". iNext. iExists _, _, _, _, _. iFrame. eauto. }
    wp_pures. iRight. iModIntro. iSplit; first done. wp_pures. eauto.
  }
  wp_pures.
  iNamed "Hmsg".
  iDestruct (typed_slice.own_slice_to_small with "Hs") as "Hsl".
  cbn in Henc. subst m.
  wp_apply (wp_ReadInt with "Hsl"). clear s.
  iIntros (s) "Hsl".
  wp_pures.

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
    { iFrame "∗#". iNext. iExists _, _, _, _, _. iFrame.
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
    apply map.map_get_true in Hget.
    rewrite Hget in Hpending_cb. inversion Hpending_cb as [Heq].
    wp_loadField.
    wp_apply (wp_StoreAt with "[Hrep_ptr]").
    { apply slice_val_ty. }
    { iFrame. }
    iIntros "Hrep_ptr". wp_pures.
    wp_loadField.
    wp_apply (wp_StoreAt with "[Hstate]").
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
      iExists _. iFrame "Hreg_entry HPost_saved". iDestruct "H" as "[Hcase1|[Hcase2|Hcase3]]".
      { iNamed "Hcase1". iLeft. iExists _, _, _, aborted0. iFrame "∗#".
        iPureIntro.
        destruct (decide (seqno = k)).
        { subst. rewrite lookup_delete in Hlookup; congruence. }
        rewrite lookup_delete_ne //=. }
      { iNamed "Hcase2". iRight. iLeft. iExists _, _. iFrame "∗#".
        iPureIntro.
        apply lookup_delete_None; auto.
      }
      { iDestruct "Hcase3" as "(%&H)". iRight. iRight. iFrame. iPureIntro.
        apply lookup_delete_None; auto.
      }
    }
    iExists _. iFrame "Hsaved". iFrame "#". iRight. iLeft.
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
Qed.

Lemma wp_TryMakeClient (srv:u64):
  {{{
       True
  }}}
    TryMakeClient #srv
  {{{
       (err:u64) (cl_ptr:loc), RET (#err, #cl_ptr);
        if (decide (err = 0)) then
          is_uRPCClient cl_ptr srv
        else
          True
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_lam.
  wp_apply (wp_Connect).
  iIntros (err client) "Hr".
  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (?) "Hnil".
  wp_pures.
  wp_if_destruct.
  {
    wp_pures.
    wp_load.
    wp_pures.
    iModIntro.
    by iApply "HΦ".
  }

  wp_apply (wp_new_free_lock). iIntros (lk) "Hfree".
  wp_pures.
  wp_apply (map.wp_NewMap).
  iIntros (mref) "Hmref".

  wp_apply (wp_allocStruct); first val_ty.
  iIntros (cl) "Hcl".
  iNamed "Hcl".
  iDestruct (struct_fields_split with "Hcl") as "Hcl". iNamed "Hcl".
  wp_pures.
  (* TODO: why do I have to unshelve this, when in other cases it appears to get picked up automatically *)
  unshelve (iMod (readonly_alloc_1 with "mu") as "#mu"); [| apply _ |].
  unshelve (iMod (readonly_alloc_1 with "conn") as "#conn"); [| apply _ |].
  unshelve (iMod (readonly_alloc_1 with "pending") as "#pending"); [| apply _ |].

  iMod (map_init (∅ : gmap u64 urpc_req_desc)) as (γccmapping) "Hmapping_ctx".
  iMod (map_init (∅ : gmap u64 unit)) as (γccescrow) "Hescrow_ctx".
  iMod (map_init (∅ : gmap u64 unit)) as (γccextracted) "Hextracted_ctx".
  set (Γ := {| ccmapping_name := γccmapping; ccescrow_name := γccescrow;
               ccextracted_name := γccextracted |}).
  iMod (alloc_lock urpc_lockN _ _ (Client_lock_inner Γ cl lk mref) with
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
  iMod (inv_alloc urpc_clientN _ (reply_chan_inner Γ client) with "[Hr]") as "#Hchan_inv".
  { iNext. iExists ∅. iFrame. rewrite big_sepS_empty //. }
  wp_bind (Fork _).
  iApply wp_fork.
  { iNext. wp_pures. iApply wp_Client__replyThread. repeat iExists _.
    iSplit. 1:iFrame "mu conn pending".
    iSplit; done. }
  iNext. wp_pures. iModIntro. iApply "HΦ".
  iExists _, _, _, _. iSplit; first by iFrame "#". iSplit; done.
Qed.


Lemma wp_MakeClient (srv:u64):
  {{{
       True
  }}}
    MakeClient #srv
  {{{
       (cl_ptr:loc), RET #cl_ptr; is_uRPCClient cl_ptr srv
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_lam.
  wp_apply (wp_TryMakeClient).
  iIntros (err client) "Hr".
  wp_pures.
  wp_apply wp_If_optional.
  {
    iIntros (?) "H HΦ".
    instantiate (1:=True%I).
    wp_pures.
    iModIntro.
    iApply "HΦ".
    done.
  }
  { done. }
  iIntros "_".
  wp_apply (wp_Assume).
  iIntros (Herr).
  apply bool_decide_eq_true in Herr.
  replace (err) with (W64 0) by naive_solver.
  destruct (decide _); last first.
  { exfalso. done. }
  wp_pures.
  iApply "HΦ".
  by iFrame.
Qed.

Inductive call_err := CallErrTimeout | CallErrDisconnect.
Definition call_errno (err : option call_err) : Z :=
  match err with
  | None => 0
  | Some CallErrTimeout => 1
  | Some CallErrDisconnect => 2
  end.

Definition own_uRPC_Callback (cl_ptr cb_ptr : loc) Post : iProp Σ :=
  ∃ n Γ γ rpcid reqData cb_cond (rep_ptr cb_state lk mref : loc),
  "#mu" ∷ readonly (cl_ptr ↦[Client :: "mu"] #lk) ∗
  "#Hlk" ∷ is_lock urpc_lockN #lk (Client_lock_inner Γ cl_ptr lk mref) ∗
  "#cond'" ∷ is_cond cb_cond #lk ∗
  "#reply" ∷ readonly (cb_ptr ↦[Callback :: "reply"] #rep_ptr) ∗
  "#state" ∷ readonly (cb_ptr ↦[Callback :: "state"] #cb_state) ∗
  "#cond" ∷ readonly (cb_ptr ↦[Callback :: "cond"] #cb_cond) ∗
  "#Hsaved" ∷ saved_pred_own γ DfracDiscarded Post ∗
  "#Hreg" ∷ n [[Γ.(ccmapping_name)]]↦ro {|
                                         urpc_reg_rpcid := rpcid;
                                         urpc_reg_args := reqData;
                                         urpc_reg_saved := γ;
                                         urpc_reg_done := cb_state;
                                         urpc_reg_rep_ptr := rep_ptr
                                       |} ∗
  "Hextracted" ∷ n [[Γ.(ccextracted_name)]]↦ ().

Lemma wp_Client__CallStart_pred γsmap (cl_ptr:loc) (rpcid:u64) (host:u64) req
      (reqData:list u8) Spec Post q :
  is_urpc_spec_pred γsmap host rpcid Spec -∗
  {{{
      own_slice_small req byteT q reqData ∗
      is_uRPCClient cl_ptr host ∗
      □(▷ Spec reqData Post)
  }}}
    Client__CallStart #cl_ptr #rpcid (slice_val req)
  {{{
       (err : option call_err) (cb_ptr : loc), RET (#cb_ptr, #(call_errno err));
       own_slice_small req byteT q reqData ∗
       (if err is Some _ then True else own_uRPC_Callback cl_ptr cb_ptr Post)
  }}}.
Proof.
  iIntros "#Hhandler !#" (Φ) "H HΦ".
  wp_lam.
  wp_pures.
  iDestruct "H" as "(Hslice&Hclient&#HSpec)".
  iNamed "Hclient". iNamed "Hstfields".

  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep_ptr) "Hrep_ptr".
  wp_pures.

  wp_apply (wp_ref_of_zero); first done.
  iIntros (cb_state) "cb_state".
  wp_loadField.
  wp_bind (lock.newCond _).
  wp_apply (wp_newCond with "[$]").
  iIntros (cb_cond) "#cond".
  wp_apply (wp_allocStruct); first val_ty.
  wp_pures.
  iIntros (cb) "Hcb".
  wp_pures.
  iRename "cond" into "cond'".
  iDestruct (struct_fields_split with "Hcb") as "Hcb". iNamed "Hcb".
  unshelve (iMod (readonly_alloc_1 with "reply") as "#reply"); [| apply _ |].
  unshelve (iMod (readonly_alloc_1 with "state") as "#state"); [| apply _ |].
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
  wp_loadField.

  wp_loadField.
  wp_apply wp_SumAssumeNoOverflow.
  iIntros (Hoverflow1).
  wp_storeField.

  wp_loadField.
  wp_apply (map.wp_MapInsert with "[$]").
  iIntros "Hpending_map".
  wp_pures.
  wp_loadField.
  iMod (saved_pred_alloc (Post)) as (γ) "#Hsaved".
  { apply dfrac_valid_discarded. }
  assert (reqs !! n = None).
  { apply not_elem_of_dom. rewrite -Hdom_range. lia. }
  iMod (map_alloc_ro n (ReqDesc rpcid reqData γ cb_state rep_ptr)
          with "Hmapping_ctx") as "(Hmapping_ctx&#Hreg)"; auto.
  iMod (map_alloc n tt with "Hescrow_ctx") as "(Hescrow_ctx&Hescrow)".
  { apply not_elem_of_dom. rewrite -Hdom_eq_es -Hdom_range. lia. }
  iMod (map_alloc n tt with "Hextracted_ctx") as "(Hextracted_ctx&Hextracted)".
  { apply not_elem_of_dom. rewrite -Hdom_eq_ex -Hdom_range. lia. }
  wp_apply (release_spec with "[-Hslice Hhandler HΦ Hextracted]").
  { iFrame "Hlk". iFrame "Hlked". iNext. iExists _, _, _, _, _.
    iFrame. rewrite ?dom_insert_L.
    replace (uint.Z (word.add n 1)) with (uint.Z n + 1)%Z by word.
    iSplit.
    { iPureIntro. word. }
    iSplit.
    { iPureIntro. intros. set_unfold. split.
      * intros Hrange.
        assert (0 < uint.Z id < uint.Z n ∨ uint.Z id = uint.Z n)%Z.
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
    iLeft. iExists _, _, _, false. iFrame "∗#".
    iPureIntro. rewrite lookup_insert //. }
  wp_pures.
  wp_apply (wp_slice_len).
  wp_apply (wp_NewSliceWithCap (V:=u8)).
  { apply encoding.unsigned_64_nonneg. (* FIXME why does [word] not solve this? *) }
  iIntros (ptr) "Hmsg".
  rewrite replicate_0.
  wp_apply (wp_WriteInt with "Hmsg"). clear ptr.
  iIntros (msg_sl) "Hmsg".
  wp_apply (wp_WriteInt with "Hmsg"). clear msg_sl.
  iIntros (msg_sl) "Hmsg".
  wp_apply (wp_WriteBytes with "[$Hmsg $Hslice]"). clear msg_sl.
  iIntros (req_sl) "[Hreq_sl Hslice]".
  rewrite -!app_assoc app_nil_l.

  wp_loadField.
  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_sl".
  iNamed "Hhandler".
  wp_apply (wp_Send with "[$]").
  iInv "Hserver_inv" as "Hserver_inner" "Hclo".
  iDestruct "Hserver_inner" as (ms) "(>Hchan'&Hmessages)".
  iApply (ncfupd_mask_intro _); first set_solver+.
  iIntros "Hclo'".
  iExists _. iFrame "Hchan'".
  iIntros (msg_sent) "Hchan'". rewrite /named.
  iMod ("Hclo'") as "_".
  iDestruct (own_slice_small_sz with "Hslice") as %Hsz.
  iMod ("Hclo" with "[Hmessages Hchan']") as "_".
  { iNext. iExists _.
    iFrame.
    destruct msg_sent; last by iFrame.
    rewrite [ms ∪ _]comm_L.
    iApply (big_sepS_insert_2 with "[] Hmessages").
    iExists _, _, _, _, _, _, _.
    iExists _, _, _, _.
    iFrame "Hreg".
    assert (W64 (Z.of_nat (uint.nat (req.(Slice.sz)))) = req.(Slice.sz)) as Heqlen.
    { word. }
    iFrame "#". iSplit; last by eauto.
    iPureIntro. word.
  }
  iModIntro. iIntros (err) "[%Herr _]".
  destruct err; wp_pures.
  { wp_apply wp_allocStruct; first val_ty. iIntros (cb_ptr) "_". wp_pures.
    iApply ("HΦ" $! (Some CallErrDisconnect) cb_ptr).
    iFrame "Hslice". done. }
  iApply ("HΦ" $! None cb).
  iFrame "Hslice". iModIntro.
  do 5 iExists _.
  eauto 20 with iFrame.
Qed.

Lemma wp_Client__CallComplete_pred (cl_ptr cb_ptr:loc) rep_out_ptr
      (timeout_ms : u64) dummy_sl_val Post :
  {{{
      rep_out_ptr ↦[slice.T byteT] dummy_sl_val ∗
      own_uRPC_Callback cl_ptr cb_ptr Post
  }}}
    Client__CallComplete #cl_ptr #cb_ptr #rep_out_ptr #timeout_ms
  {{{
       (err : option call_err), RET #(call_errno err);
       (if err is Some _ then rep_out_ptr ↦[slice.T byteT] dummy_sl_val else
        ∃ rep_sl (repData:list u8),
          rep_out_ptr ↦[slice.T byteT] (slice_val rep_sl) ∗
          own_slice_small rep_sl byteT (DfracOwn 1) repData ∗
          (Post repData))
  }}}.
Proof.
  iIntros (Φ) "[Hrep_out_ptr Hcb] HΦ".
  iNamed "Hcb".
  wp_call.

  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hi Hlockinv]".
  wp_pures.
  wp_loadField.
  wp_bind (if: _ then _ else _)%E.
  iAssert (∃ (x: u64), cb_state ↦[uint64T] #x ∗ n [[Γ.(ccextracted_name)]]↦ () ∗
                        (cb_state ↦[uint64T] #x -∗ Client_lock_inner Γ cl_ptr lk mref))%I
          with "[Hlockinv Hextracted]" as "H".
  { iNamed "Hlockinv".
    iDestruct (map_ro_valid with "Hmapping_ctx [$]") as %Hlookup_reg.
    iDestruct (big_sepM_lookup_acc with "Hreqs") as "(H&Hclo)"; first eauto.
    iEval (simpl) in "H".
    iFreeze "Hclo".
    iNamed "H".
    iDestruct "H" as "[Hcase1|[Hcase2|Hcase3]]".
    { iNamed "Hcase1".
      iDestruct "Hcase1" as "(#?&#?&#?&Hrest)". iNamed "Hrest".
      iExists _. iFrame.
      iIntros "H". iFrame "∗ # %".
      iThaw "Hclo". iApply "Hclo".
      { simpl. iExists _. iFrame "Hsaved Hreg". iLeft. iExists _, _, _. iFrame "∗#". eauto. }
    }
    { iNamed "Hcase2". iExists _. iFrame.
      iIntros "H". iFrame "∗ # %".
      iThaw "Hclo". iApply "Hclo".
      { simpl. iExists _. iFrame "HPost_saved Hreg". iRight.
        iLeft. iExists _, _. iFrame "∗#". eauto. }
    }
    { iDestruct "Hcase3" as "(?&Hex)".
      iDestruct (ptsto_valid_2 with "Hex [$]") as %Hval.
      exfalso. rewrite //= in Hval.
    }
  }

  iDestruct "H" as (b) "(Hdone&Hextracted&Hdone_clo)".
  wp_apply (wp_LoadAt with "[$]"). iIntros "Hdone".
  iDestruct ("Hdone_clo" with "[$]") as "Hlockinv".
  wp_apply (wp_If_join_evar' (lock.locked #lk ∗
                                  Client_lock_inner Γ cl_ptr lk mref)%I
   with "[Hi Hlockinv]").
  { case_bool_decide; wp_pures.
    - wp_loadField. wp_apply (wp_condWaitTimeout with "[$cond' $Hi $Hlk $Hlockinv]").
      iIntros "(Hi&Hlockinv)". wp_pures.
      iFrame. eauto.
    - iFrame. eauto. }

  iIntros "[Hi Hlockinv]".
  wp_pures. wp_loadField.
  iNamed "Hlockinv".
  iDestruct (map_ro_valid with "Hmapping_ctx [$]") as %Hlookup_reg.
  iDestruct (big_sepM_lookup_acc with "Hreqs") as "(H&Hclo)"; first eauto.
  iEval (simpl) in "H".
  iFreeze "Hclo".
  iNamed "H".
  iDestruct "H" as "[Hcase1|[Hcase2|Hcase3]]".
  { iNamed "Hcase1". 
    iDestruct "Hcase1" as "(#?&#?&#?&Hrest)". iNamed "Hrest".
    wp_apply (wp_LoadAt with "[$]"). iIntros "Hdone".
    wp_pures.
    iThaw "Hclo".
    iDestruct ("Hclo" with "[Hdone Hcond Hescrow Hrep_ptr]") as "H".
    { simpl. iExists _. iFrame "Hsaved Hreg". iLeft. iExists _, _, _. iFrame "∗#". eauto. }
    rewrite bool_decide_false.
    2: by destruct aborted.
    wp_loadField.
    wp_apply (release_spec with "[$Hlk $Hi H HPost_saved
                 Hpending_map Hmapping_ctx Hescrow_ctx Hextracted_ctx seq]").
    { iExists _, _, _, _, _. iFrame. eauto. }
    wp_pures.
    destruct aborted; wp_pures; iModIntro.
    1: iApply ("HΦ" $! (Some CallErrDisconnect)).
    2: iApply ("HΦ" $! (Some CallErrTimeout)).
    all: done.
  }
  { iNamed "Hcase2".
    wp_apply (wp_LoadAt with "[$]"). iIntros "Hdone".
    iDestruct (saved_pred_agree _ _ _ _ _ reply with "HPost_saved Hsaved") as "#Hequiv".
    wp_pures.
    wp_loadField.
    wp_apply (wp_LoadAt with "[$Hrep_ptr]"). iIntros "Hrep_ptr".
    wp_apply (wp_StoreAt with "[$Hrep_out_ptr]").
    { naive_solver. }
    iIntros "Hrep_out_ptr".
    wp_pures.

    iThaw "Hclo".
    iDestruct ("Hclo" with "[Hdone Hextracted]") as "H".
    { simpl. iExists _. iFrame "Hsaved Hreg". iRight. iRight.
      iSplit; eauto. }
    wp_loadField.
    wp_apply (release_spec with "[$Hlk $Hi H HPost_saved
                 Hpending_map Hmapping_ctx Hescrow_ctx Hextracted_ctx seq]").
    { iExists _, _, _, _, _. iFrame. eauto. }
    wp_pures.
    iModIntro.
    iRewrite ("Hequiv") in "HPost".
    iApply ("HΦ" $! None).
    iExists _, reply.
    iFrame.
  }
  { iDestruct "Hcase3" as "(?&Hex)".
    iDestruct (ptsto_valid_2 with "Hex [$]") as %Hval.
    exfalso. rewrite //= in Hval.
  }
Qed.

Lemma wp_Client__Call_pred γsmap (cl_ptr:loc) (rpcid:u64) (host:u64) req rep_out_ptr
      (timeout_ms : u64) dummy_sl_val (reqData:list u8) Spec Post q :
  {{{
      "Hslice" ∷ own_slice_small req byteT q reqData ∗
      "Hrep_out_ptr" ∷ rep_out_ptr ↦[slice.T byteT] dummy_sl_val ∗
      "#Hclient" ∷ is_uRPCClient cl_ptr host ∗
      "#Hhandler" ∷ is_urpc_spec_pred γsmap host rpcid Spec ∗
      "#HSpec" ∷ □(▷ Spec reqData Post)
  }}}
    Client__Call #cl_ptr #rpcid (slice_val req) #rep_out_ptr #timeout_ms
  {{{
       (err : option call_err), RET #(call_errno err);
       own_slice_small req byteT q reqData ∗
       (if err is Some _ then rep_out_ptr ↦[slice.T byteT] dummy_sl_val else
        ∃ rep_sl (repData:list u8),
          rep_out_ptr ↦[slice.T byteT] (slice_val rep_sl) ∗
          own_slice_small rep_sl byteT (DfracOwn 1) repData ∗
          (Post repData))
  }}}.
Proof.
  iIntros (Φ) "H HΦ".
  iNamed "H".
  wp_call.
  wp_apply (wp_Client__CallStart_pred with "Hhandler [$Hslice $Hclient $HSpec]").
  iIntros (err cb_ptr) "[Hslice Hcb]".
  destruct err as [err|]; wp_pures.
  { destruct err; wp_pures.
    2: iApply ("HΦ" $! (Some CallErrDisconnect)).
    1: iApply ("HΦ" $! (Some CallErrTimeout)).
    all: eauto with iFrame. }
  wp_apply (wp_Client__CallComplete_pred with "[$Hrep_out_ptr $Hcb]").
  iIntros ([err|]) "Hcomplete".
  { iApply ("HΦ" $! (Some err)). eauto with iFrame. }
  iApply ("HΦ" $! None). eauto with iFrame.
Qed.

(** With this spec, there's no need to specify an "intermediate" postcondition,
   but the Φ shows up in a magic wand under □, so you may need to use
   wp_frame_wand in order to get resources (such as "HΦ") across the □. *)
Lemma wp_Client__Call2 γsmap (cl_ptr:loc) (rpcid:u64) (host:u64) req rep_out_ptr
      (timeout_ms : u64) dummy_sl_val (reqData:list u8) Spec Φ q :
  is_uRPCClient cl_ptr host -∗
  is_urpc_spec_pred γsmap host rpcid Spec -∗
  own_slice_small req byteT q reqData -∗
  rep_out_ptr ↦[slice.T byteT] dummy_sl_val -∗
  □(▷ Spec reqData (λ reply,
       own_slice_small req byteT q reqData -∗
        ∀ rep_sl,
          rep_out_ptr ↦[slice.T byteT] (slice_val rep_sl) -∗
          own_slice_small rep_sl byteT (DfracOwn 1) reply -∗
          Φ #0)
  ) ∧
  (
   ∀ (err:u64), ⌜err ≠ 0⌝ →
                own_slice_small req byteT q reqData -∗
                rep_out_ptr ↦[slice.T byteT] dummy_sl_val -∗ Φ #err
  ) -∗
  WP Client__Call #cl_ptr #rpcid (slice_val req) #rep_out_ptr #timeout_ms {{ Φ }}.
Proof.
  iIntros "#His_cl #Hhandler Hreq_sl Hrep [#Hspec Hfail]".
  wp_apply (wp_Client__Call_pred with "[Hhandler His_cl Hreq_sl Hrep]").
  {
    iFrame.
    iFrame "His_cl".
    iSplitL.
    { (* FIXME: iFrame "#" doesn't work without clearing the name. *)
      iApply to_named.
      iFrame "#".
    }
    iFrame "#".
  }
  iIntros (err) "Hpost".
  iDestruct "Hpost" as "(Hreq&Hrep)".
  destruct err.
  {
    iApply ("Hfail" with "[%] Hreq Hrep").
    by destruct c.
  }
  simpl.
  iDestruct "Hrep" as (??) "(Hrep & Hrep_sl & HΦ)".
  iApply ("HΦ" with "Hreq Hrep Hrep_sl").
Qed.

Global Instance is_urpc_handler_pred_pers f Spec : Persistent (is_urpc_handler_pred f Spec).
Proof. apply _. Qed.

Global Typeclasses Opaque is_urpc_handler_pred.
Global Typeclasses Opaque is_urpc_spec_pred.

End urpc_proof.


Section urpc_global_defs.

Context `{!urpcregG Σ}.
Context `{HPRE: !gooseGlobalGS Σ}.

Implicit Type (l:list (u64 * savedSpecO Σ (list u8) (list u8))).
Fixpoint is_urpc_spec_pred_list γ host l :=
  match l with
  | [] => True%I
  | x :: l =>
    (is_urpc_spec_pred γ host x.1 x.2 ∗ is_urpc_spec_pred_list γ host l)%I
  end.

Fixpoint dom_spec_list l : gset u64 :=
  match l with
  | [] => ∅
  | x :: l => {[ x.1 ]} ∪ dom_spec_list l
  end.

Fixpoint spec_list_wf l : Prop :=
  match l with
  | [] => True
  | x :: l =>
    (x.1 ∉ dom_spec_list l) ∧ spec_list_wf l
  end.

Lemma alloc_is_urpc_list_pred (host : chan) specs (Hwf: spec_list_wf specs) :
   host c↦ ∅ ={⊤}=∗ ∃ γ,
   is_urpc_dom γ (dom_spec_list specs) ∗
   is_urpc_spec_pred_list γ host specs.
Proof.
  iIntros "Hchan".
  iMod (map_init (∅ : gmap u64 gname)) as (γmap) "Hmap_ctx".
  iMod (own_alloc (to_agree (dom_spec_list specs : gsetO u64))) as (γdom) "#Hdom".
  { econstructor. }
  set (Γsrv := {| scmap_name := γmap; scset_name := γdom |}).
  iMod (inv_alloc urpc_serverN _ ((server_chan_inner host Γsrv)) with "[Hchan]") as "#Hinv".
  { iNext. iExists _. iFrame.
    rewrite big_sepS_empty //. }
  iExists Γsrv.
  iAssert (∀ specs', ⌜ spec_list_wf specs' ⌝ ∗ ⌜ dom_spec_list specs' ⊆  dom_spec_list specs ⌝ →
           |==> ∃ gnames : gmap u64 gname, ⌜ dom gnames = dom_spec_list specs' ⌝ ∗
           map_ctx (scmap_name Γsrv) 1 gnames ∗
           is_urpc_spec_pred_list Γsrv host specs')%I with "[Hmap_ctx]" as "H"; last first.
  { iMod ("H" with "[]") as (?) "(_&_&$)"; eauto. }
  iIntros (specs').
  iInduction specs' as [| hd spec] "IH".
  { iIntros (?). iModIntro. iExists ∅. iFrame.
    rewrite ?dom_empty_L //. }
  { iIntros ((Hwf'&Hdom')).
    iMod ("IH" with "[$] []") as (gnames Hdom) "(Hmap_ctx&Hmap)".
    { iPureIntro. split.
      - destruct Hwf' as (_&?); eauto.
      - etransitivity; last eassumption. set_solver. }
    iMod (saved_spec_alloc hd.2) as (γsave) "#Hsaved".
    iMod (map_alloc_ro (hd.1) γsave
            with "Hmap_ctx") as "(Hmap_ctx&#Hsaved_name)"; auto.
    { apply not_elem_of_dom. destruct (Hwf') as (?&?). rewrite Hdom. eauto. }
    iExists _; iFrame. iModIntro.
    iSplit.
    { iPureIntro. rewrite ?dom_insert_L Hdom. set_solver. }
    iExists _, _. iFrame "#".
    { iPureIntro. simpl in Hdom'. set_solver. }
  }
Qed.

End urpc_global_defs.
