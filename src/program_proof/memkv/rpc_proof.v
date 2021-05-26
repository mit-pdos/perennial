From Perennial.Helpers Require Import ModArith.
From Goose.github_com.mit_pdos.gokv.urpc Require Import rpc.
From iris.base_logic.lib Require Import saved_prop.
From Perennial.goose_lang Require Import adequacy.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof Require Import marshal_proof.
From Perennial.algebra Require Import auth_map.
From Perennial.base_logic Require Import lib.ghost_map lib.mono_nat.
From Perennial.goose_lang Require Import dist_lifting.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

(** Request descriptor: data describing a particular request *)
Record rpc_req_desc := ReqDesc {
  rpc_reg_rpcid  : u64;
  rpc_reg_args : list u8;
  rpc_reg_saved : gname; (* Saved pred storing what the reply needs to satisfy *)
  rpc_reg_done : loc;
  rpc_reg_rep_ptr : loc;
}.

Class rpcregG (Σ : gFunctors) := RpcRegG {
  rpcreg_mono_natG :> mono_natG Σ;
  rpcreg_mapG :> mapG Σ u64 rpc_req_desc;
  rpcreg_escrowG :> mapG Σ u64 unit;
  rpcreg_saved_gname_mapG :> mapG Σ u64 gname;
  rpcreg_saved_handler_specG :> savedPredG Σ (heap_local_names * gname * val);
  rpcreg_savedG :> savedPredG Σ (list u8);
  rpcreg_domG :> inG Σ (agreeR (leibnizO (gset u64)));
}.

Definition rpcregΣ :=
  #[mono_natΣ; mapΣ u64 rpc_req_desc; mapΣ u64 unit; mapΣ u64 gname; savedPredΣ (heap_local_names * gname * val); savedPredΣ (list u8);
   GFunctor (agreeR (leibnizO (gset u64)))].

Global Instance subG_rpcregG {Σ} :
  subG (rpcregΣ) Σ → rpcregG Σ.
Proof. solve_inG. Qed.

Section rpc_global_defs.

Context `{!rpcregG Σ}.
Context `{HPRE: !heap_globalG Σ}.

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

Definition is_rpcHandler {X:Type} (names : heap_local_names) (cname : gname) (f:val) Pre Post : iProp Σ :=
  let hG := heap_globalG_heapG _ {| crash_inG := _; crash_name := cname |} names in
  ∀ (x:X) req rep dummy_rep_sl dummy (reqData:list u8),
  {{{
      is_slice req byteT 1 reqData ∗
      rep ↦[slice.T byteT] (slice_val dummy_rep_sl) ∗
      is_slice (V:=u8) dummy_rep_sl byteT 1 dummy ∗
      ▷ Pre x reqData
  }}}
    f (slice_val req) #rep
  {{{
       rep_sl (repData:list u8), RET #(); rep ↦[slice.T byteT] (slice_val rep_sl) ∗
         is_slice rep_sl byteT 1 repData ∗
         ▷ Post x reqData repData
  }}}.

Definition reply_chan_inner_msg (Γ : client_chan_gnames) m : iProp Σ :=
    ∃ (rpcid seqno : u64) reqData replyData X Post (x : X) γ d rep,
       "%Hlen_reply" ∷ ⌜ length replyData = int.nat (length replyData) ⌝ ∗
       "%Henc" ∷ ⌜ has_encoding (msg_data m) [EncUInt64 seqno;
                                              EncUInt64 (length replyData); EncBytes replyData] ⌝ ∗
       "#Hseqno" ∷ ptsto_ro (ccmapping_name Γ) seqno (ReqDesc rpcid reqData γ d rep) ∗
       "#HPost_saved" ∷ saved_pred_own γ (Post x reqData) ∗
       "#HPost" ∷ inv urpc_escrowN (Post x reqData replyData ∨ ptsto_mut (ccescrow_name Γ) seqno 1 tt).

Let gn := heap_globalG_names.
Let gpG := (heap_preG_ffi).
Instance global_groveG : groveG Σ := @grove_update_pre _ gpG gn.

Definition reply_chan_inner (Γ : client_chan_gnames) (c: chan) : iProp Σ :=
  ∃ ms, "Hchan" ∷ c c↦ ms ∗
  "Hmessages" ∷ [∗ set] m ∈ ms, reply_chan_inner_msg Γ m.

Definition server_chan_inner_msg Γsrv m : iProp Σ :=
    ∃ rpcid seqno args X Pre Post (x : X) Γ γ1 γ2 d rep rpcdom,
       "%Hlen_args" ∷ ⌜ length args = int.nat (U64 (Z.of_nat (length args))) ⌝ ∗
       "#Hdom1" ∷ own (scset_name Γsrv) (to_agree (rpcdom)) ∗
       "%Hdom2" ∷ ⌜ rpcid ∈ rpcdom ⌝ ∗
       "%Henc" ∷ ⌜ has_encoding (msg_data m) [EncUInt64 rpcid; EncUInt64 seqno;
                                              EncUInt64 (length args); EncBytes args] ⌝ ∗
       "#Hseqno" ∷ ptsto_ro (ccmapping_name Γ) seqno (ReqDesc rpcid args γ1 d rep) ∗
       "#Hspec_name" ∷ ptsto_ro (scmap_name Γsrv) rpcid γ2 ∗
       "#Hspec_saved" ∷ saved_pred_own γ2 (λ (n : heap_local_names * gname * val),
                                           is_rpcHandler n.1.1 n.1.2 n.2 Pre Post) ∗
       "#HPre" ∷ □ (Pre x args) ∗
       "#HPost_saved" ∷ saved_pred_own γ1 (Post x args) ∗
       "#Hclient_chan_inv" ∷ inv urpc_clientN (reply_chan_inner Γ (msg_sender m)).

Definition server_chan_inner (c: chan) γmap : iProp Σ :=
  ∃ ms,
  "Hchan" ∷ c c↦ ms ∗
  "Hmessages" ∷ [∗ set] m ∈ ms, server_chan_inner_msg γmap m.

Definition handler_is Γsrv : ∀ (X:Type) (host:chan) (rpcid:u64) (Pre:X → list u8 → iProp Σ)
                          (Post:X → list u8 → list u8 → iProp Σ), iProp Σ :=
  λ X host rpcid Pre Post, (∃ γ rpcdom,
   "#Hdom1" ∷ own (scset_name Γsrv) (to_agree (rpcdom)) ∗
   "%Hdom2" ∷ ⌜ rpcid ∈ rpcdom ⌝ ∗
  "#Hspec_name" ∷ ptsto_ro (scmap_name Γsrv) rpcid γ ∗
  "#Hspec_saved" ∷ saved_pred_own γ (λ (n : heap_local_names * gname * val),
                                      is_rpcHandler n.1.1 n.1.2 n.2 Pre Post) ∗
  "#Hserver_inv" ∷ inv urpc_serverN (server_chan_inner host Γsrv)
)%I.

Global Instance handler_is_pers_instance γ X host rpcid pre post :
  Persistent (handler_is γ X host rpcid pre post).
Proof. apply _. Qed.

Definition handlers_dom Γsrv (d: gset u64) :=
  own (scset_name Γsrv) (to_agree (d : leibnizO (gset u64))).

Record RPCSpec :=
  { spec_rpcid : u64;
     spec_ty : Type;
     spec_Pre : spec_ty → list u8 → iProp Σ;
     spec_Post : spec_ty → list u8 → list u8 → iProp Σ }.

Definition has_handler Γsrv (host:u64) (spec : RPCSpec) :=
  handler_is Γsrv _ host spec.(spec_rpcid) spec.(spec_Pre) spec.(spec_Post).

(* We define a custom type for a list of RPC specs in order to state lemmas
   about initializing a collection of handler_is facts. Unfortunately, using the
   standard list type leads to a universe error if the spec_ty field contains an
   iProp Σ, which turns out to be rather common. *)

Inductive RPCSpecList : Type :=
| spec_nil : RPCSpecList
| spec_cons (x: RPCSpec) (l: RPCSpecList) : RPCSpecList.

Fixpoint dom_RPCSpecList (l:  RPCSpecList) : gset u64 :=
  match l with
  | spec_nil => ∅
  | spec_cons x l => {[ spec_rpcid x ]} ∪ dom_RPCSpecList l
  end.

Fixpoint handler_RPCSpecList γ host (l : RPCSpecList) :=
  match l with
  | spec_nil => True%I
  | spec_cons x l =>
    (handler_is γ (spec_ty x) host (spec_rpcid x) (spec_Pre x) (spec_Post x) ∗
                handler_RPCSpecList γ host l)%I
  end.

Fixpoint RPCSpecList_wf (l : RPCSpecList) : Prop :=
  match l with
  | spec_nil => True
  | spec_cons x l =>
    (spec_rpcid x ∉ dom_RPCSpecList l) ∧ RPCSpecList_wf l
  end.

Lemma handler_is_init_list (host : chan) (specs: RPCSpecList) (Hwf: RPCSpecList_wf specs) :
   host c↦ ∅ ={⊤}=∗ ∃ γ,
   handlers_dom γ (dom_RPCSpecList specs) ∗
   handler_RPCSpecList γ host specs.
Proof.
  iIntros "Hchan".
  iMod (map_init (∅ : gmap u64 gname)) as (γmap) "Hmap_ctx".
  iMod (own_alloc (to_agree (dom_RPCSpecList specs : leibnizO (gset u64)))) as (γdom) "#Hdom".
  { econstructor. }
  set (Γsrv := {| scmap_name := γmap; scset_name := γdom |}).
  iMod (inv_alloc urpc_serverN _ ((server_chan_inner host Γsrv)) with "[Hchan]") as "#Hinv".
  { iNext. iExists _. iFrame.
    rewrite big_sepS_empty //. }
  iExists Γsrv.
  iAssert (∀ specs', ⌜ RPCSpecList_wf specs' ⌝ ∗ ⌜ dom_RPCSpecList specs' ⊆  dom_RPCSpecList specs ⌝ →
           |==> ∃ gnames : gmap u64 gname, ⌜ dom (gset _) gnames = dom_RPCSpecList specs' ⌝ ∗
           map_ctx (scmap_name Γsrv) 1 gnames ∗
           handler_RPCSpecList Γsrv host specs')%I with "[Hmap_ctx]" as "H"; last first.
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
    iMod (saved_pred_alloc (λ n, is_rpcHandler n.1.1 n.1.2 n.2
                                               (spec_Pre hd) (spec_Post hd))) as (γsave) "#Hsaved".
    iMod (map_alloc_ro (spec_rpcid hd) γsave
            with "Hmap_ctx") as "(Hmap_ctx&#Hsaved_name)"; auto.
    { apply not_elem_of_dom. destruct (Hwf') as (?&?). rewrite Hdom. eauto. }
    iExists _; iFrame. iModIntro.
    iSplit.
    { iPureIntro. rewrite ?dom_insert_L Hdom. set_solver. }
    iExists _, _. iFrame "#".
    { iPureIntro. simpl in Hdom'. set_solver. }
  }
Qed.

Lemma is_rpcHandler_proper' hn gn' handler X Pre Pre' Post Post' :
 □ (∀ (x : X) (l1 : list u8), Pre x l1 ≡ Pre' x l1) -∗
 □ (∀ (x : X) (l1 : list u8) (l2 : list u8),
       Post x l1 l2 ≡ Post' x l1 l2) -∗
 is_rpcHandler hn gn' handler Pre Post -∗
 is_rpcHandler hn gn' handler Pre' Post'.
Proof.
  iIntros "#Hequiv_pre #Hequiv_post #His".
  rewrite /is_rpcHandler.
  iIntros. iIntros (Φc) "!# H HΦc".
  wp_apply ("His" with "[H]").
  { iDestruct "H" as "($&$&$&Hpre)". iNext.
    iRewrite -("Hequiv_pre" $! x reqData) in "Hpre".
    iExact "Hpre".
  }
  iIntros (??) "H". iApply "HΦc".
  iDestruct "H" as "($&$&Hpre)". iNext.
    iRewrite ("Hequiv_post" $! x reqData repData) in "Hpre".
    iExact "Hpre".
Qed.


End rpc_global_defs.

Section rpc_proof.

Context `{hG: !heapGS Σ}.
Context `{hReg: !rpcregG Σ}.

Definition is_rpcHandler' {X:Type} (f:val) Pre Post : iProp Σ :=
  ∀ (x:X) req rep dummy_rep_sl dummy (reqData:list u8),
  {{{
      is_slice req byteT 1 reqData ∗
      rep ↦[slice.T byteT] (slice_val dummy_rep_sl) ∗
      is_slice (V:=u8) dummy_rep_sl byteT 1 dummy ∗
      ▷ Pre x reqData
  }}}
    f (slice_val req) #rep
  {{{
       rep_sl (repData:list u8), RET #(); rep ↦[slice.T byteT] (slice_val rep_sl) ∗
         is_slice rep_sl byteT 1 repData ∗
         ▷ Post x reqData repData
  }}}.

Definition RPCClient_lock_inner Γ  (cl : loc) (lk : loc) mref : iProp Σ :=
  ∃ pending reqs (estoks extoks : gmap u64 unit) (n : u64),
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
            "Hreqs" ∷ [∗ map] seqno ↦ req ∈ reqs,
                 ∃ X (Post : X → list u8 → list u8 → iProp Σ) x,
                 "Hreg_entry" ∷  ptsto_ro (ccmapping_name Γ) seqno req ∗
                 "HPost_saved" ∷ saved_pred_own (rpc_reg_saved req) (Post x (rpc_reg_args req)) ∗
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
                    "HPost" ∷ (Post x (rpc_reg_args req) reply) ∗
                    "Hrep_ptr" ∷ (rpc_reg_rep_ptr req) ↦[slice.T byteT] (slice_val rep_sl) ∗
                    "Hrep_data" ∷ typed_slice.is_slice rep_sl byteT 1 reply ∗
                    "Hdone" ∷ (rpc_reg_done req) ↦[boolT] #true) ∨
                 (* (3) Caller has extracted ownership *)
                 (⌜ pending !! seqno  = None ⌝ ∗ ptsto_mut (ccextracted_name Γ) seqno 1 tt)).


Instance heapG_to_preG Σ' : heapGS Σ' → heapGpreS Σ'.
Proof.
  destruct 1.
  destruct heapG_invG.
  destruct heapG_crashG.
  destruct heapG_ffiG.
  destruct groveG_gen_heapG.
  destruct heapG_na_heapG.
  destruct heapG_traceG.
  econstructor; econstructor; apply _.
Defined.

Global Instance heapG_heap_globalG : heap_globalG Σ.
Proof using hG.
  econstructor.
  - apply _.
  - apply (heap_ffi_global_names (heap_get_names _ _)).
  - apply (heap_credit_names (heap_get_names _ _)).
  - eapply inv_get_names. apply _.
Defined.

Definition RPCClient_own (cl : loc) (srv : chan) : iProp Σ :=
  ∃ Γ (lk : loc) client (mref : loc),
    "#Hstfields" ∷ ("mu" ∷ readonly (cl ↦[RPCClient :: "mu"] #lk) ∗
    "#conn" ∷ readonly (cl ↦[RPCClient :: "conn"] connection_socket client srv) ∗
    "#pending" ∷ readonly (cl ↦[RPCClient :: "pending"] #mref)) ∗
    "#Hchan" ∷ inv urpc_clientN (reply_chan_inner Γ client) ∗
    "#Hlk" ∷ is_lock urpc_lockN #lk (RPCClient_lock_inner Γ cl lk mref).

Definition RPCClient_reply_own (cl : loc) : iProp Σ :=
  ∃ Γ (lk : loc) client srv (mref : loc),
    "#Hstfields" ∷ ("mu" ∷ readonly (cl ↦[RPCClient :: "mu"] #lk) ∗
    "#conn" ∷ readonly (cl ↦[RPCClient :: "conn"] connection_socket client srv) ∗
    "#pending" ∷ readonly (cl ↦[RPCClient :: "pending"] #mref)) ∗
    "#Hchan" ∷ inv urpc_clientN (reply_chan_inner Γ client) ∗
    "#Hlk" ∷ is_lock urpc_lockN #lk (RPCClient_lock_inner Γ cl lk mref).

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

Definition rpc_handler_mapping (γ : server_chan_gnames) (host : u64) (handlers : gmap u64 val) : iProp Σ :=
  ([∗ map] rpcid↦handler ∈ handlers, ∃ (X : Type) Pre Post,
      handler_is γ X host rpcid Pre Post ∗
      is_rpcHandler' handler Pre Post)%I.

(* BLACK MAGIC *)
Lemma is_rpcHandler_convert X handler Pre Post :
  is_rpcHandler (X := X) (heap_get_local_names Σ _) (crash_name) handler Pre Post ≡
  is_rpcHandler' handler Pre Post.
Proof.
  rewrite /is_rpcHandler/is_rpcHandler'.
  assert ((@heap_globalG_heapG grove_op grove_model grove_semantics grove_interp grove_interp_adequacy Σ
              heapG_heap_globalG
              {|
                crash_inG :=
                  heapG_heap_globalG
                  .(@heap_globalG_preG grove_op grove_model grove_semantics grove_interp grove_interp_adequacy Σ)
                  .(@heap_preG_crash grove_op grove_model grove_semantics grove_interp grove_interp_adequacy Σ)
                  .(@crash_inPreG Σ);
                crash_name :=
                  (@heapG_irisG grove_op grove_model grove_semantics grove_interp Σ hG)
                  .(@iris_crashG (@goose_lang grove_op grove_model grove_semantics) Σ).(
                  @crash_name Σ)
              |} (@heap_get_local_names grove_op grove_model grove_interp Σ hG) = hG)) as ->.
  { rewrite //=/heap_globalG_heapG/heap_update_pre//= /heap_globalG_invG.
    rewrite /inv_update_pre/heap_preG_iris/heapG_to_preG//=.
    rewrite /heapG_to_preG.
    destruct hG => //=.
    destruct heapG_invG eqn:Heq.
    destruct heapG_crashG.
    destruct heapG_ffiG.
    destruct groveG_gen_heapG.
    destruct heapG_na_heapG.
    destruct heapG_traceG.
    destruct heapG_creditG.
    f_equal. rewrite /inv_inPreG.
    f_equal. destruct inv_inG0 => //=.
  }
  eauto.
Qed.

Lemma global_groveG_inv_conv :
  @heap_globalG_invG grove_op grove_model grove_semantics grove_interp grove_interp_adequacy Σ heapG_heap_globalG =
  (@heapG_irisG grove_op grove_model grove_semantics grove_interp Σ hG)
  .(@iris_invG (@goose_lang grove_op grove_model grove_semantics) Σ).
Proof.
  { rewrite //=/heap_globalG_heapG/heap_update_pre//= /heap_globalG_invG.
    rewrite /inv_update_pre/heap_preG_iris/heapG_to_preG//=.
    rewrite /heapG_to_preG.
    destruct hG => //=.
    destruct heapG_invG eqn:Heq.
    destruct heapG_crashG.
    destruct heapG_ffiG.
    destruct groveG_gen_heapG.
    destruct heapG_na_heapG.
    destruct heapG_traceG.
    f_equal. rewrite /inv_inPreG.
    f_equal. destruct inv_inG0 => //=.
  }
Qed.

Lemma global_groveG_inv_conv':
  dist_weakestpre.grove_invG = iris_invG.
Proof. eauto using global_groveG_inv_conv. Qed.

Lemma non_empty_rpc_handler_mapping_inv γ host handlers :
  dom (gset u64) handlers ≠ ∅ →
  rpc_handler_mapping γ host handlers -∗
  "#Hserver_inv" ∷ inv urpc_serverN (server_chan_inner host γ) ∗
  "#Hhandlers" ∷ ([∗ map] rpcid↦handler ∈ handlers, ∃ (X : Type) Pre Post γs,
                                                      ptsto_ro (scmap_name γ) rpcid γs ∗
                                                      saved_pred_own γs (λ (n : heap_local_names * gname * val),
                                                         is_rpcHandler n.1.1 n.1.2 n.2 Pre Post) ∗
                                                      is_rpcHandler' (X := X) handler Pre Post)%I.
Proof.
  iIntros (Hdom) "Hmapping".
  iInduction handlers as [| rpcid handler] "IH" using map_ind.
  { rewrite dom_empty_L in Hdom; congruence. }
  rewrite /rpc_handler_mapping big_sepM_insert //.
  iDestruct "Hmapping" as "(H&Hmapping)".
  destruct (decide (dom (gset _) m = ∅)) as [Hemp|Hemp].
  { iNamed "H". iDestruct "H" as "(Hhandler_is&His_rpcHandler)".
    iNamed "Hhandler_is". iFrame "% #".
    rewrite global_groveG_inv_conv'. iFrame "#".
    rewrite big_sepM_insert //. iSplitL "His_rpcHandler".
    { iExists _, Pre, Post, _. iSplit; first eauto.
      iFrame "# ∗". }
    apply dom_empty_inv_L in Hemp. rewrite Hemp big_sepM_empty. eauto.
  }
  iDestruct ("IH" with "[//] [$]") as "HIH".
  iNamed "HIH". iFrame "% #".
  rewrite big_sepM_insert //. iFrame "#".
  { iNamed "H". iDestruct "H" as "(Hhandler_is&His_rpcHandler)".
    rewrite /handler_is.
    iDestruct "Hhandler_is" as (g0 rpcdom) "H".
    iDestruct "H" as "(#Hdom1&%Hdom2&#Hspec_name&#Hspec_saved&H)".
    iExists _, _, _, _.  iFrame "# ∗".
  }
Qed.

Definition handlers_complete Γ (handlers : gmap u64 val) :=
  (handlers_dom Γ (dom (gset _) handlers)).

Lemma global_groveG_conv :
  (@global_groveG Σ heapG_heap_globalG).(@groveG_gen_heapG Σ) =
  (@grove_ffi.heapG_groveG Σ hG).(@groveG_gen_heapG Σ).
Proof.
    rewrite /grove_ffi.heapG_groveG//=.
    rewrite /heapG_to_preG//=.
    destruct hG => //=.
    destruct heapG_invG => //=.
    destruct heapG_crashG => //=.
    destruct heapG_ffiG => //=.
    destruct groveG_gen_heapG => //=.
    destruct heapG_na_heapG => //=.
    destruct heapG_traceG => //=.
Qed.

Lemma wp_RPCServer__readThread γ s host client handlers mref def :
  dom (gset u64) handlers ≠ ∅ →
  "#Hcomplete" ∷ handlers_complete γ handlers ∗
  "#His_rpc_map" ∷ rpc_handler_mapping γ host handlers ∗
  "#Hhandlers_map" ∷ readonly (map.is_map mref 1 (handlers, def)) ∗
  "#handlers" ∷ readonly (s ↦[RPCServer :: "handlers"] #mref) -∗
  WP RPCServer__readThread #s (connection_socket host client) {{ _, True }}.
Proof.
  iIntros (Hdom).
  iNamed 1.
  wp_lam. wp_pures.
  wp_apply (wp_forBreak_cond'); [ iNamedAccu |].
  iIntros "!> _".
  wp_pures.
  iDestruct (non_empty_rpc_handler_mapping_inv with "[$]") as "H"; first auto.
  iNamed "H".
  wp_apply (wp_Receive).
  iInv "Hserver_inv" as "Hchan_inner" "Hclo".
  iDestruct "Hchan_inner" as (ms) "(>Hchan'&#Hchan_inner)".
  iApply (ncfupd_mask_intro _); first set_solver+.
  iIntros "Hclo'".
  iExists _.
  rewrite global_groveG_conv.
  iFrame "Hchan'".
  iNext.
  iIntros (err m) "(Hchan&Herr)".
  iAssert (if err then True else server_chan_inner_msg γ (Message client m))%I with "[Hchan_inner Herr]" as "Hmsg".
  { destruct err; auto.
    iDestruct "Herr" as %Hin.
    iApply (big_sepS_elem_of with "Hchan_inner"); first eassumption.
  }
  iMod ("Hclo'") as "_".
  iMod ("Hclo" with "[Hchan]") as "_".
  { iNext. iExists _. iFrame "% #". eauto. rewrite global_groveG_conv. eauto. }
  iModIntro.
  iIntros (r) "Hsl".
  wp_pures.
  destruct err as [err|]; wp_pures.
  { destruct err; simpl; wp_pures; eauto. }
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
  { word. }
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
  {
    iDestruct (own_valid_2 with "Hcomplete Hdom1") as %Hval.
    exfalso.
    apply to_agree_op_inv_L in Hval.
    apply not_elem_of_dom in Hlookup'.
    congruence.
  }
  rewrite //= in Hget. inversion Hget; subst.
  iDestruct (big_sepM_lookup with "Hhandlers") as "H"; eauto.
  iNamed "H". iDestruct "H" as "(#Hsname&#Hsaved&#His_rpcHandler)".
  iDestruct (ptsto_ro_agree with "Hspec_name Hsname") as %->.
  iDestruct (saved_pred_agree _ _ _ (heap_get_local_names Σ hG, crash_name, v) with "Hspec_saved Hsaved")
    as "#Hequiv".
  wp_pures.
  iEval (simpl) in "Hequiv".
  assert ((@heapG_irisG grove_op grove_model grove_semantics grove_interp Σ hG)
           .(@iris_crashG (@goose_lang grove_op grove_model grove_semantics) Σ).(
           @crash_name Σ)
           = hG.(@heapG_crashG grove_op grove_model grove_interp Σ).(@crash_name Σ)) as Heq.
  { rewrite //=. }
  rewrite -Heq.
  rewrite ?(is_rpcHandler_convert).
  iRewrite -"Hequiv" in "His_rpcHandler". iClear "Hequiv".
  rewrite /is_rpcHandler.
  replace (zero_val (slice.T byteT)) with
      (slice_val {| Slice.ptr := null; Slice.sz := U64 0; Slice.cap := U64 0 |}) by auto.
  wp_apply ("His_rpcHandler" with "[$Hsl $Hsl' HPre]").
  { iSplitL "".
    { iApply @is_slice_zero. }
    { iDestruct "HPre" as "#HPre". iNext. iFrame "#". }
  }
  iIntros (rep_sl repData) "(Hsl'&His_slice&HPost)".
  wp_pures.
  wp_apply (wp_LoadAt with "[$]"). iIntros "Hsl'".
  wp_apply (wp_slice_len).
  wp_pures.
  wp_apply (wp_LoadAt with "[$]"). iIntros "Hsl'".
  wp_apply (wp_slice_len).
  wp_apply (wp_Assume).
  iIntros (Hoverflow).
  apply bool_decide_eq_true_1 in Hoverflow.
  wp_pures.
  wp_apply (wp_LoadAt with "[$]"). iIntros "Hsl'".
  wp_apply (wp_slice_len).
  wp_apply (wp_new_enc).
  iIntros (enc) "Henc".
  wp_pures.
  assert (int.Z (word.add (word.add 8 8) rep_sl.(Slice.sz)) =
                 int.Z (rep_sl.(Slice.sz)) + 16)%Z as Hoverflow3.
  {
    apply sum_nooverflow_r in Hoverflow.
    rewrite Hoverflow.
    change (int.Z (word.add 8 8))%Z with 16%Z. lia.
  }
  wp_apply (wp_Enc__PutInt with "Henc").
  { word. }
  iIntros "Henc".
  wp_pures.
  wp_apply (wp_LoadAt with "[$]"). iIntros "Hsl'".
  wp_apply (wp_slice_len).
  wp_apply (wp_Enc__PutInt with "Henc").
  { word. }
  iIntros "Henc".
  wp_pures.
  wp_apply (wp_LoadAt with "[$]"). iIntros "Hsl'".
  iDestruct (is_slice_small_read with "His_slice") as "(His_slice&Hsl_close)".
  iDestruct (is_slice_small_sz with "His_slice") as %Hsz.
  wp_apply (wp_Enc__PutBytes with "[$Henc $His_slice]").
  { word. }
  iIntros "[Henc Hslice]".
  wp_pures.
  wp_apply (wp_Enc__Finish with "[$Henc]").
  iIntros (rep_sl_msg rep_msg_data).
  iIntros "(%Hencoding&Hlength&Hmsg_slice)".

  (* Send *)
  iDestruct (is_slice_small_read with "Hmsg_slice") as "(Hmsg_slice&_)".
  wp_apply (wp_Send with "[$Hmsg_slice]").
  iMod (inv_alloc urpc_escrowN _ (Post x args repData ∨ ptsto_mut (ccescrow_name Γ) seqno 1 tt)
          with "[HPost]") as "#HPost_escrow".
  { eauto. }
  rewrite global_groveG_inv_conv'.
  iInv "Hclient_chan_inv" as "Hclient_chan_inner" "Hclo".
  iDestruct "Hclient_chan_inner" as (ms_rep) "(>Hchan'&#Hclient_chan_inner)".
  iApply (ncfupd_mask_intro _); first set_solver+.
  iIntros "Hclo'".
  iExists _. rewrite global_groveG_conv. iFrame "Hchan'". iNext.
  iIntros (msg_sent) "Hchan'".
  iMod "Hclo'" as "_".
  rewrite ?global_groveG_conv.
  iMod ("Hclo" with "[Hchan' Hlength]").
  { iNext. iExists _.
    rewrite ?global_groveG_conv.
    iFrame.
    destruct msg_sent; last first.
    { iFrame "#". }
    destruct (decide (Message host rep_msg_data ∈ ms_rep)).
    { assert (ms_rep ∪ {[Message host rep_msg_data]} = ms_rep) as -> by set_solver. iFrame "#". }
    iApply big_sepS_union; first by set_solver.
    iFrame "#".
    iApply big_sepS_singleton.
    iExists _, _, _, _, _, _, _.
    iExists _, _, _.
    rewrite global_groveG_inv_conv'.
    iFrame "#".
    iPureIntro. simpl. rewrite ?app_nil_l //= in Hencoding. rewrite Hsz.
    assert (U64 (Z.of_nat (int.nat (rep_sl.(Slice.sz)))) = rep_sl.(Slice.sz)) as ->.
    { word. }
    eauto.
  }
  iModIntro. iIntros (err) "[%?]". wp_pures; eauto.
Qed.

Lemma wp_StartRPCServer γ (host : u64) (handlers : gmap u64 val) (s : loc) (n:u64) :
  dom (gset u64) handlers ≠ ∅ →
  {{{
      handlers_complete γ handlers ∗
      own_RPCServer s handlers ∗
      [∗ map] rpcid ↦ handler ∈ handlers,
      (∃ X Pre Post, handler_is γ X host rpcid Pre Post ∗ is_rpcHandler' handler Pre Post)
  }}}
    RPCServer__Serve #s #host #n
  {{{
      RET #(); True
  }}}.
Proof.
  iIntros (? Φ) "(#Hcomplete&Hserver&#His_rpc_map) HΦ".
  wp_lam. wp_pures.
  wp_apply (wp_Listen). wp_pures.
  iNamed "Hserver".
  wp_apply (wp_fork).
  2:{ by iApply "HΦ". }

  wp_apply (wp_forBreak_cond'); [ iNamedAccu |].
  iIntros "!# _". wp_pures.
  wp_apply (wp_Accept).
  iIntros (client) "_". wp_pures.
  wp_apply (wp_fork).
  { wp_apply (wp_RPCServer__readThread with "[]"); eauto. }
  wp_pures. iModIntro. by iLeft.
Qed.

Lemma wp_RPCClient__replyThread cl :
  RPCClient_reply_own cl -∗
  WP RPCClient__replyThread #cl {{ _, True }}.
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
  iExists _. rewrite global_groveG_conv. iFrame "Hchan'". iNext.
  iIntros (err m) "(Hchan'&Herr)".
  iAssert (if err then True else reply_chan_inner_msg Γ (Message srv m))%I with "[Hchan_inner Herr]" as "Hmsg".
  { destruct err; auto.
    iDestruct "Herr" as %Hin.
    iApply (big_sepS_elem_of with "Hchan_inner"); first eassumption.
  }
  iMod "Hclo'". iMod ("Hclo" with "[Hchan']").
  { iNext. iExists _. rewrite global_groveG_conv. iFrame. eauto.  }
  iModIntro. iIntros (s) "Hs".
  wp_pures.
  destruct err as [err|].
  { destruct err; simpl; wp_pures; eauto. }
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
  { word. }
  iIntros (?) "Hsl".
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
    rewrite global_groveG_inv_conv'.
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
      iExists _, _, _; iFrame.  iDestruct "H" as "[Hcase1|[Hcase2|Hcase3]]".
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
    iExists _, _, _. iFrame "#".  iRight. iLeft.
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

Lemma wp_MakeRPCClient (srv:u64):
  {{{
       True
  }}}
    MakeRPCClient #srv
  {{{
       (cl_ptr:loc), RET #cl_ptr; RPCClient_own cl_ptr srv
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_lam.
  wp_apply (wp_Connect).
  iIntros (err client) "Hr".
  wp_pures.
  wp_apply (wp_Assume).
  iIntros (Herr). destruct err; first by (simpl in Herr; first congruence).

  replace (ref (InjLV #null))%E with (NewMap (struct.ptrT callback)) by naive_solver.
  wp_apply (wp_new_free_lock). iIntros (lk) "Hfree".
  wp_pures.
  wp_apply (map.wp_NewMap).
  iIntros (mref) "Hmref".

  wp_apply (wp_allocStruct).
  { enough (val_ty (connection_socket client srv) Connection) by naive_solver.
    econstructor.
  }
  iIntros (cl) "Hcl".
  iNamed "Hcl".
  iDestruct (struct_fields_split with "Hcl") as "Hcl". iNamed "Hcl".
  wp_pures.
  (* TODO: why do I have to unshelve this, when in other cases it appears to get picked up automatically *)
  unshelve (iMod (readonly_alloc_1 with "mu") as "#mu"); [| apply _ |].
  unshelve (iMod (readonly_alloc_1 with "conn") as "#conn"); [| apply _ |].
  unshelve (iMod (readonly_alloc_1 with "pending") as "#pending"); [| apply _ |].

  iMod (map_init (∅ : gmap u64 rpc_req_desc)) as (γccmapping) "Hmapping_ctx".
  iMod (map_init (∅ : gmap u64 unit)) as (γccescrow) "Hescrow_ctx".
  iMod (map_init (∅ : gmap u64 unit)) as (γccextracted) "Hextracted_ctx".
  set (Γ := {| ccmapping_name := γccmapping; ccescrow_name := γccescrow;
               ccextracted_name := γccextracted |}).
  iMod (alloc_lock urpc_lockN _ _ (RPCClient_lock_inner Γ cl lk mref) with
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
  { iNext. iExists ∅. rewrite global_groveG_conv. iFrame. rewrite big_sepS_empty //. }
  wp_bind (Fork _).
  iApply wp_fork.
  { iNext. wp_pures. iApply wp_RPCClient__replyThread. repeat iExists _.
    rewrite ?global_groveG_conv.
    iFrame "#". }
  iNext. wp_pures. iModIntro. iApply "HΦ".
  iExists _, _, _, _. iFrame "#".
Qed.

Lemma wp_RPCClient__Call {X:Type} (x:X) γsmap (cl_ptr:loc) (rpcid:u64) (host:u64) req rep_out_ptr
      dummy_sl_val (reqData:list u8) Pre Post :
  {{{
      is_slice req byteT 1 reqData ∗
      rep_out_ptr ↦[slice.T byteT] dummy_sl_val ∗
      handler_is γsmap X host rpcid Pre Post ∗
      RPCClient_own cl_ptr host ∗
      □(▷ Pre x reqData)
  }}}
    RPCClient__Call #cl_ptr #rpcid (slice_val req) #rep_out_ptr
  {{{
       (b:bool), RET #b;
       RPCClient_own cl_ptr host ∗
       typed_slice.is_slice req byteT 1 reqData ∗
       (⌜b = true⌝ ∗ rep_out_ptr ↦[slice.T byteT] dummy_sl_val ∨
        ∃ rep_sl (repData:list u8), ⌜b = false⌝ ∗
          rep_out_ptr ↦[slice.T byteT] (slice_val rep_sl) ∗
          typed_slice.is_slice rep_sl byteT 1 repData ∗
          (▷ Post x reqData repData))
  }}}.
Proof.
  iIntros (Φ) "H HΦ".
  wp_lam.
  wp_pures.
  iDestruct "H" as "(Hslice&Hrep_out_ptr&Hhandler&Hclient&#HPre)".
  iNamed "Hclient". iNamed "Hstfields".

  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep_ptr) "Hrep_ptr".
  wp_pures.

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
  wp_loadField.
  wp_loadField.
  wp_apply (wp_Assume).
  iIntros (Hoverflow1).
  wp_pures.
  wp_loadField.
  wp_storeField.
  wp_loadField.
  wp_apply (map.wp_MapInsert with "[$]").
  iIntros "Hpending_map".
  wp_pures.
  wp_loadField.
  iMod (saved_pred_alloc (Post x reqData)) as (γ) "#Hsaved".
  assert (reqs !! n = None).
  { apply not_elem_of_dom. rewrite -Hdom_range. lia. }
  iMod (map_alloc_ro n (ReqDesc rpcid reqData γ cb_done rep_ptr)
          with "Hmapping_ctx") as "(Hmapping_ctx&#Hreg)"; auto.
  iMod (map_alloc n tt with "Hescrow_ctx") as "(Hescrow_ctx&Hescrow)".
  { apply not_elem_of_dom. rewrite -Hdom_eq_es -Hdom_range. lia. }
  iMod (map_alloc n tt with "Hextracted_ctx") as "(Hextracted_ctx&Hextracted)".
  { apply not_elem_of_dom. rewrite -Hdom_eq_ex -Hdom_range. lia. }
  wp_apply (release_spec with "[-Hslice Hhandler HΦ Hextracted Hrep_out_ptr]").
  { iFrame "Hlk". iFrame "Hlked". iNext. iExists _, _, _, _, _.
    iFrame. rewrite ?dom_insert_L.
    assert (int.Z (word.add n 1) = int.Z n + 1)%Z as ->.
    { apply bool_decide_eq_true_1 in Hoverflow1. word. }
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
    iExists _, Post, _.
    iFrame "Hreg Hsaved".
    iLeft. iExists _, _, _. iFrame "# ∗".
    iPureIntro. rewrite lookup_insert //. }
  wp_pures.
  wp_apply (wp_slice_len).
  wp_pures.
  wp_apply (wp_slice_len).
  wp_apply (wp_Assume).
  iIntros (Hoverflow2).
  apply bool_decide_eq_true_1 in Hoverflow2.
  wp_pures.
  wp_apply (wp_slice_len).
  wp_apply (wp_new_enc).
  iIntros (enc) "Henc".
  wp_pures.
  assert (int.Z (word.add (word.add (word.add 8 8) 8) req.(Slice.sz)) =
                 int.Z (req.(Slice.sz)) + 24)%Z as Hoverflow3.
  {
    apply sum_nooverflow_r in Hoverflow2.
    rewrite Hoverflow2.
    change (int.Z $ word.add (word.add 8 8) 8)%Z with 24%Z. lia. }
  wp_apply (wp_Enc__PutInt with "Henc").
  { word. }
  iIntros "Henc".
  wp_pures.
  wp_apply (wp_Enc__PutInt with "Henc").
  { word. }
  iIntros "Henc".
  wp_pures.
  wp_apply (wp_slice_len).
  wp_apply (wp_Enc__PutInt with "Henc").
  { word. }
  iIntros "Henc".
  wp_pures.
  iDestruct (is_slice_small_read with "Hslice") as "(Hslice&Hslice_close)".
  iDestruct (is_slice_small_sz with "Hslice") as %Hsz.
  wp_apply (wp_Enc__PutBytes with "[$Henc $Hslice]").
  { word. }
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
  rewrite global_groveG_inv_conv'.
  iInv "Hserver_inv" as "Hserver_inner" "Hclo".
  iDestruct "Hserver_inner" as (ms) "(>Hchan'&H)".
  iApply (ncfupd_mask_intro _); first set_solver+.
  iIntros "Hclo'".
  iExists _. rewrite global_groveG_conv.  iFrame "Hchan'". iNext.
  iIntros (msg_sent) "Hchan'". iNamed "H".
  iMod ("Hclo'") as "_".
  iMod ("Hclo" with "[Hmessages Hchan']") as "_".
  { iNext. iExists _.
    rewrite global_groveG_conv.
    iFrame.
    destruct msg_sent; last by iFrame.
    destruct (decide (Message client repData ∈ ms)).
    { assert (ms ∪ {[Message client repData]} = ms) as -> by set_solver. iFrame. }
    iApply big_sepS_union; first by set_solver.
    iFrame "Hmessages".
    iApply big_sepS_singleton.
    iExists _, _, _, _, _, _, _.
    iExists _, _, _, _, _, _.
    iFrame "Hreg".
    rewrite global_groveG_inv_conv'.
    assert (U64 (Z.of_nat (int.nat (req.(Slice.sz)))) = req.(Slice.sz)) as Heqlen.
    { word. }
    iFrame "#". iSplit; eauto.
    { iPureIntro. simpl. rewrite ?app_nil_l //= in Hhas_encoding. rewrite Hsz. word. }
    iSplit; eauto.
    { iPureIntro. simpl. rewrite ?app_nil_l //= in Hhas_encoding. rewrite Hsz Heqlen. eauto. }
  }
  iModIntro. iIntros (err) "[%Herr Hsl_rep]".
  destruct err; wp_pures.
  { iApply "HΦ".
    iDestruct ("Hslice_close" with "Hslice") as "$".
    iModIntro.
    iSplitR "Hrep_out_ptr".
    - iExists _, _, _, _. by iFrame "#".
    - iLeft. by iFrame. }
  destruct msg_sent; last done. clear Herr.
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "[Hi Hlockinv]".
  wp_pures.
  wp_loadField.
  wp_bind (if: _ then _ else _)%E.
  iAssert (∃ (b: bool), cb_done ↦[boolT] #b ∗ n [[Γ.(ccextracted_name)]]↦ () ∗
                        (cb_done ↦[boolT] #b -∗ RPCClient_lock_inner Γ cl_ptr lk mref))%I
          with "[Hlockinv Hextracted]" as "H".
  { iNamed "Hlockinv".
    iDestruct (map_ro_valid with "Hmapping_ctx [$]") as %Hlookup_reg.
    iDestruct (big_sepM_lookup_acc with "Hreqs") as "(H&Hclo)"; first eauto.
  iEval (simpl) in "H".
  iFreeze "Hclo".
  iNamed "H".
  iDestruct "H" as "[Hcase1|[Hcase2|Hcase3]]".
  { iNamed "Hcase1".
    iDestruct "Hcase1" as "(#?&#?&#?&Hrest)". iNamed "Hrest". iExists _. iFrame.
    iIntros "H". iExists _, _, _, _, _. iFrame "∗ # %".
    iThaw "Hclo". iApply "Hclo".
    { simpl. iExists _, _, _. iFrame "Hreg". iFrame "Hsaved". iFrame "#". iLeft. iExists _, _, _. iFrame "# ∗". }
  }
  { iNamed "Hcase2". iExists _. iFrame.
    iIntros "H".  iExists _, _, _, _, _. iFrame "∗ # %".
    iThaw "Hclo". iApply "Hclo".
    { simpl. iExists _, _, _. iFrame "Hreg". iFrame "HPost_saved". iRight.
      iLeft. iExists _, _. iFrame "# ∗". }
  }
  { iDestruct "Hcase3" as "(?&Hex)".
    iDestruct (ptsto_valid_2 with "Hex [$]") as %Hval.
    exfalso. rewrite //= in Hval.
  }
  }

  iDestruct "H" as (b) "(Hdone&Hextracted&Hdone_clo)".
  wp_apply (wp_LoadAt with "[$]"). iIntros "Hdone".
  iDestruct ("Hdone_clo" with "[$]") as "Hlockinv".
  wp_apply (wp_If_join_evar _ _ _ (λ _, lock.locked #lk ∗
                                  RPCClient_lock_inner Γ cl_ptr lk mref)%I
   with "[Hi Hlockinv]").
  { iIntros (b' Heq). destruct b; wp_pures.
    - iFrame. eauto.
    - wp_loadField. wp_apply (wp_condWaitTimeout with "[$cond' $Hi $Hlk $Hlockinv]").
      iIntros "(Hi&Hlockinv)". wp_pures.
      iFrame. eauto. }

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
    iDestruct ("Hclo" with "[Hdone Hcond Hescrow Hpending_cb Hrep_ptr]") as "H".
    { simpl. iExists _, _, _. iFrame "Hreg". iFrame "Hsaved". iFrame "#". iLeft. iExists _, _, _. iFrame "# ∗". }
    wp_loadField.
    wp_apply (release_spec with "[$Hlk $Hi H HPost_saved
                 Hpending_map Hmapping_ctx Hescrow_ctx Hextracted_ctx seq]").
    { iExists _, _, _, _, _. iFrame. eauto. }
    wp_pures. iModIntro.
    iApply "HΦ".
    iDestruct ("Hslice_close" with "Hslice") as "$".
    iSplitR "Hrep_out_ptr"; last by eauto.
    iExists _, _, _, _. by iFrame "∗#".
  }
  { iNamed "Hcase2".
    wp_apply (wp_LoadAt with "[$]"). iIntros "Hdone".
    iDestruct (saved_pred_agree _ _ _ reply with "HPost_saved Hsaved") as "#Hequiv".
    wp_pures.
    wp_apply (wp_LoadAt with "[$Hrep_ptr]"). iIntros "Hrep_ptr".
    wp_apply (wp_StoreAt with "[$Hrep_out_ptr]").
    { naive_solver. }
    iIntros "Hrep_out_ptr".
    wp_pures.

    iThaw "Hclo".
    iDestruct ("Hclo" with "[Hdone Hextracted Hpending_cb]") as "H".
    { simpl. iExists _, _, _. iFrame "Hreg". iFrame "Hsaved". iFrame "#". iRight. iRight.
      iSplit; eauto. }
    wp_loadField.
    wp_apply (release_spec with "[$Hlk $Hi H HPost_saved
                 Hpending_map Hmapping_ctx Hescrow_ctx Hextracted_ctx seq]").
    { iExists _, _, _, _, _. iFrame. eauto. }
    wp_pures.
    iModIntro.
    iRewrite ("Hequiv") in "HPost".
    iApply "HΦ".
    iSplitR.
    { iExists _, _, _, _. iFrame "#". }
    iSplitL "Hslice Hslice_close".
    { iApply "Hslice_close". eauto. }
    iRight. iExists _, reply.
    iFrame. eauto.
  }
  { iDestruct "Hcase3" as "(?&Hex)".
    iDestruct (ptsto_valid_2 with "Hex [$]") as %Hval.
    exfalso. rewrite //= in Hval.
  }
Qed.

End rpc_proof.
