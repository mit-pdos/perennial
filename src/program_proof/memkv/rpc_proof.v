From Goose.github_com.mit_pdos.gokv.urpc Require Import rpc.
From iris.base_logic.lib Require Import saved_prop.
From Perennial.program_proof Require Import dist_prelude.
From Perennial.program_proof Require Import marshal_proof.
From Perennial.algebra Require Import auth_map.
From Perennial.base_logic Require Export lib.ghost_map lib.mono_nat.

Record rpc_reg_entry := RegEntry {
  rpc_reg_rpcid  : u64;
  rpc_reg_auxtype : Type;
  rpc_reg_aux : rpc_reg_auxtype;
  rpc_reg_args : list u8;
  rpc_reg_saved : gname;
}.

Class rpcregG (Σ : gFunctors) := RpcRegG {
  rpcreg_mono_natG :> mono_natG Σ;
  rpcreg_mapG :> mapG Σ u64 rpc_reg_entry;
  rpcreg_escrowG :> mapG Σ u64 unit;
  rpcreg_savedG :> savedPredG Σ (list u8);
}.

Section rpc_proof.

Existing Instances message_eq_decision message_countable.

Context `{!rpcregG Σ}.
Context `{!heapG Σ}.

(* A host-specific mapping from rpc ids on that host to pre/post conditions *)
Definition rpc_spec_map : Type :=
  gmap u64 { X: Type & ((X → list u8 → iProp Σ) * (X → list u8 → list u8 → iProp Σ))%type }.

Definition urpc_serverN : namespace := nroot.@"urpc_server".
Definition urpc_clientN : namespace := nroot.@"urpc_client".
Definition urpc_lockN : namespace := nroot.@"urpc_lock".

Record client_chan_gnames := {
  ccmapping_name : gname;
  ccescrow_name : gname;
  ccextracted_name : gname;
}.

Definition client_chan_inner (Γ : client_chan_gnames) (host: u64) : iProp Σ :=
  ∃ ms, "Hchan" ∷ host c↦ ms ∗
  "Hmessages" ∷ [∗ set] m ∈ ms,
    ∃ (rpcid seqno : u64) reqData replyData X Post (x : X) γ,
       "%Henc" ∷ ⌜ has_encoding (msg_data m) [EncUInt64 seqno;
                                              EncUInt64 (length replyData); EncBytes replyData] ⌝ ∗
       "#Hseqno" ∷ ptsto_ro (ccmapping_name Γ) seqno (RegEntry rpcid X x reqData γ) ∗
       "HPost_saved" ∷ saved_pred_own γ (Post x reqData) ∗
       "HPost" ∷ (Post x reqData replyData ∨ ptsto_mut (ccescrow_name Γ) seqno 1 tt)
.

Definition server_chan_inner (host: u64) (specs : rpc_spec_map) : iProp Σ :=
  ∃ ms, "Hchan" ∷ host c↦ ms ∗
  "Hmessages" ∷ [∗ set] m ∈ ms,
    ∃ rpcid seqno args X Pre Post (x : X) Γ γ,
       "%Henc" ∷ ⌜ has_encoding (msg_data m) [EncUInt64 rpcid; EncUInt64 seqno;
                                              EncUInt64 (length args); EncBytes args] ⌝ ∗
       "%Hlookup_spec" ∷ ⌜ specs !! rpcid = Some (existT X (Pre, Post)) ⌝ ∗
       "#Hseqno" ∷ ptsto_ro (ccmapping_name Γ) seqno (RegEntry rpcid X x args γ) ∗
       "HPre" ∷ □ (Pre x args) ∗
       "HPost_saved" ∷ saved_pred_own γ (Post x args) ∗
       "Hclient_chan_inv" ∷ inv urpc_clientN (client_chan_inner Γ (msg_sender m))
.

Definition handler_is : ∀ (X:Type) (host:u64) (rpcid:u64) (Pre:X → list u8 → iProp Σ)
                          (Post:X → list u8 → list u8 → iProp Σ), iProp Σ :=
  λ X host rpcid Pre Post, (∃ (specs: rpc_spec_map),
  "%Hprepost" ∷ ⌜ specs !! rpcid = Some (existT X (Pre, Post)) ⌝ ∗
  "%Hserver_inv" ∷ inv urpc_serverN (server_chan_inner host specs)
)%I.

Global Instance handler_is_pers_instance X host rpcid pre post : Persistent (handler_is X host rpcid pre post).
Proof. apply _. Qed.

Definition RPCClient_lock_inner Γ (cl : loc) (host : u64) mref : iProp Σ :=
  ∃ pending reqs estoks extoks (n : u64),
            "%Hdom_range" ∷ ⌜ ∀ id, (0 < int.Z id < int.Z n)%Z ↔ id ∈ dom (gset u64) reqs ⌝ ∗
            "%Hdom_eq" ∷ ⌜ dom (gset u64) reqs = dom (gset u64) estoks ∧
                                    dom (gset u64) reqs = dom (gset u64) extoks ⌝ ∗
            "%Hdom_pending" ∷ ⌜ dom (gset u64) pending ⊆ dom (gset u64) reqs  ⌝ ∗
            "seq" ∷ cl ↦[RPCClient :: "seq"] #n ∗
            "Hmapping_ctx" ∷ map_ctx (ccmapping_name Γ) 1 reqs ∗
            "Hescrow_ctx" ∷ map_ctx (ccescrow_name Γ) 1 estoks ∗
            "Hescrow_ctx" ∷ map_ctx (ccextracted_name Γ) 1 extoks ∗
            "Hpending_map" ∷ map.is_map mref (pending, zero_val (struct.ptrT callback)) ∗
            "Hreqs" ∷ [∗ map] seqno ↦ req ∈ reqs, ∃ (Post : rpc_reg_auxtype req → list u8 → list u8 → iProp Σ),
                 "Hreg_entry" ∷  ptsto_ro (ccmapping_name Γ) seqno req ∗
                 "HPost_saved" ∷ saved_pred_own (rpc_reg_saved req) (Post (rpc_reg_aux req) (rpc_reg_args req)) ∗
                 (* (1) Reply thread has not yet processed, so it is in pending
                    and we have escrow token *)
                 (∃ cb, ⌜ pending !! seqno  = Some cb ⌝ ∗ ptsto_mut (ccescrow_name Γ) seqno 1 tt ∗
                          (* TODO: cb ownership *) True) ∨
                 (* (2) Reply thread has received message, removed from pending,
                    but caller has not extracted ownership *)
                 (∃ reply (cb : unit), ⌜ pending !! seqno  = None ⌝ ∗ (* TODO: cb ownership *) True ∗
                               (Post (rpc_reg_aux req) (rpc_reg_args req) reply)) ∨
                 (* (3) Caller has extracted ownership *)
                 (⌜ pending !! seqno  = None ⌝ ∗ ptsto_mut (ccextracted_name Γ) seqno 1 tt).

Definition RPCClient_own (cl : loc) (host:u64) : iProp Σ :=
  ∃ Γ lk r (mref : loc),
    "#Hstfields" ∷ ("mu" ∷ readonly (cl ↦[RPCClient :: "mu"] #lk) ∗
    "#send" ∷ readonly (cl ↦[RPCClient :: "send"] send_endpoint host r) ∗
    "#pending" ∷ readonly (cl ↦[RPCClient :: "pending"] #mref)) ∗
    "#Hchan" ∷ inv urpc_clientN (client_chan_inner Γ r) ∗
    "#Hlk" ∷ is_lock urpc_lockN #lk (RPCClient_lock_inner Γ cl host mref).

Definition RPCClient_reply_own (cl : loc) (r : chan) : iProp Σ :=
  ∃ Γ host lk (mref : loc),
    "#Hstfields" ∷ ("mu" ∷ readonly (cl ↦[RPCClient :: "mu"] #lk) ∗
    "#pending" ∷ readonly (cl ↦[RPCClient :: "pending"] #mref)) ∗
    "#Hchan" ∷ inv urpc_clientN (client_chan_inner Γ r) ∗
    "#Hlk" ∷ is_lock urpc_lockN #lk (RPCClient_lock_inner Γ cl host mref).

Lemma wp_RPCClient__replyThread cl r :
  RPCClient_reply_own cl r -∗
  WP RPCClient__replyThread #cl (recv_endpoint r) {{ _, True }}.
Proof. Admitted.

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
  (* XXX: I think this is going to have to be untyped since callback contains a slice in it *)
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

  iMod (map_init (∅ : gmap u64 rpc_reg_entry)) as (γccmapping) "Hmapping_ctx".
  iMod (map_init (∅ : gmap u64 unit)) as (γccescrow) "Hescrow_ctx".
  iMod (map_init (∅ : gmap u64 unit)) as (γccextracted) "Hextracted_ctx".
  set (Γ := {| ccmapping_name := γccmapping; ccescrow_name := γccescrow;
               ccextracted_name := γccextracted |}).
  iMod (alloc_lock urpc_lockN _ _ (RPCClient_lock_inner Γ cl host mref) with
            "Hfree [Hmapping_ctx Hescrow_ctx Hextracted_ctx seq Hmref]") as "#Hlock".
  { iNext. iExists ∅, ∅, ∅, ∅, _. iFrame.
    rewrite ?dom_empty_L.
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

End rpc_proof.
