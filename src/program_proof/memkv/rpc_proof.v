From Goose.github_com.mit_pdos.gokv.urpc Require Import rpc.
From Perennial.program_proof Require Import dist_prelude.
From Perennial.program_proof Require Import marshal_proof.
From Perennial.algebra Require Import auth_map.
From Perennial.base_logic Require Export lib.ghost_map lib.mono_nat.

Class rpcregG (Σ : gFunctors) := RpcRegG {
  rpcreg_mono_natG :> mono_natG Σ;
  (* mapping from seqno to rpcid and x argument of Pre/Post, and arguments of rpc  *)
  rpcreg_mapG :> mapG Σ u64 (u64 * { X : Type & X } * list u8);
  rpcreg_escrowG :> mapG Σ u64 unit;
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
  ccmnat_name : gname;
  ccmapping_name : gname;
  ccescrow_name : gname;
  ccextracted_name : gname;
}.

Definition client_chan_inner (Γ : client_chan_gnames) (host: u64) (specs : rpc_spec_map) : iProp Σ :=
  ∃ ms, "Hchan" ∷ host c↦ ms ∗
  "Hmessages" ∷ [∗ set] m ∈ ms,
    ∃ (rpcid seqno : u64) reqData replyData X Pre Post (x : X),
       "%Henc" ∷ ⌜ has_encoding (msg_data m) [EncUInt64 seqno;
                                              EncUInt64 (length replyData); EncBytes replyData] ⌝ ∗
       "%Hlookup_spec" ∷ ⌜ specs !! rpcid = Some (existT X (Pre, Post)) ⌝ ∗
       "#Hseqno" ∷ ptsto_ro (ccmapping_name Γ) seqno (rpcid, existT X x, reqData) ∗
       "HPost" ∷ (Post x reqData replyData ∨ ptsto_mut (ccescrow_name Γ) seqno 1 tt)
.

Definition server_chan_inner (host: u64) (specs : rpc_spec_map) : iProp Σ :=
  ∃ ms, "Hchan" ∷ host c↦ ms ∗
  "Hmessages" ∷ [∗ set] m ∈ ms,
    ∃ rpcid seqno args X Pre Post (x : X) Γ,
       "%Henc" ∷ ⌜ has_encoding (msg_data m) [EncUInt64 rpcid; EncUInt64 seqno;
                                              EncUInt64 (length args); EncBytes args] ⌝ ∗
       "%Hlookup_spec" ∷ ⌜ specs !! rpcid = Some (existT X (Pre, Post)) ⌝ ∗
       "#Hseqno" ∷ ptsto_ro (ccmapping_name Γ) seqno (rpcid, existT X x, args) ∗
       "HPre" ∷ □ (Pre x args) ∗
       "Hclient_chan_inv" ∷ inv urpc_clientN (client_chan_inner Γ (msg_sender m) specs)
.


Definition handler_is : ∀ (X:Type) (host:u64) (rpcid:u64) (Pre:X → list u8 → iProp Σ)
                          (Post:X → list u8 → list u8 → iProp Σ), iProp Σ :=
  λ X host rpcid Pre Post, (∃ (specs: rpc_spec_map),
  "%Hprepost" ∷ ⌜ specs !! rpcid = Some (existT X (Pre, Post)) ⌝ ∗
  "%Hserver_inv" ∷ inv urpc_serverN (server_chan_inner host specs)
)%I.

Global Instance handler_is_pers_instance X host rpcid pre post : Persistent (handler_is X host rpcid pre post).
Proof. apply _. Qed.

(* TODO: either need to revert back to having a fixed global map of (host id, rpcid -> pre/post),
   or this needs to use saved preds to have the linkage between the RPC Pre/Post and what's stored here.

   The tricky bit here is that the axiomatized spec would require that RPCClient_lock_inner be initialized
   without even knowing what the rpc_spec_map is: the precondition is just true, only actual calls have
   handler_is assumptions *)
Definition RPCClient_lock_inner Γ (cl : loc) (host : u64) mref : iProp Σ :=
  ∃ pending reqs estoks extoks (n : u64),
            "%Hdom_range" ∷ ⌜ ∀ id, (int.Z id ≤ int.Z n)%Z ↔ id ∈ dom (gset u64) reqs ⌝ ∗
            "%Hdom_eq" ∷ ⌜ dom (gset u64) reqs = dom (gset u64) estoks ∧
                                    dom (gset u64) reqs = dom (gset u64) extoks ⌝ ∗
            "%Hdom_pending" ∷ ⌜ dom (gset u64) pending ⊆ dom (gset u64) reqs  ⌝ ∗
            "seq" ∷ cl ↦[RPCClient :: "seq"] #n ∗
            "Hmapping_ctx" ∷ map_ctx (ccmapping_name Γ) 1 reqs ∗
            "Hescrow_ctx" ∷ map_ctx (ccescrow_name Γ) 1 estoks ∗
            "Hescrow_ctx" ∷ map_ctx (ccextracted_name Γ) 1 extoks ∗
            "Hpending_map" ∷ map.is_map mref (pending, zero_val (struct.ptrT callback)) ∗
            "Hreqs" ∷ [∗ map] seqno ↦ req ∈ reqs, ptsto_ro (ccmapping_name Γ) seqno req ∗
                 let rpcid := fst req in
          (*       let X := projT1 (snd req) in
                 let x : X := projT2 (snd req) in *)
                 (* Each request is in one of 3 states: *)
                 (* (1) Reply thread has not yet processed, so it is in pending
                    and we have escrow token *)
                 (∃ cb, ⌜ pending !! seqno  = Some cb ⌝ ∗ ptsto_mut (ccescrow_name Γ) seqno 1 tt ∗
                          (* TODO: cb ownership *) True) ∨
                 (* (2) Reply thread has received message, removed from pending,
                    but caller has not extracted ownership *)
                 (∃ cb : unit, ⌜ pending !! seqno  = None ⌝ ∗ (* TODO: cb ownership *) True ) ∨
                 (* (3) Caller has extracted ownership *)
                 (⌜ pending !! seqno  = None ⌝ ∗ ptsto_mut (ccextracted_name Γ) seqno 1 tt).

Definition RPCClient_own (cl : loc) (host:u64) : iProp Σ :=
  ∃ Γ lk r (mref : loc),
    "Hstfields" ∷ ("mu" ∷ readonly (cl ↦[RPCClient :: "mu"] #lk) ∗
    "send" ∷ readonly (cl ↦[RPCClient :: "send"] send_endpoint host r) ∗
    "pending" ∷ readonly (cl ↦[RPCClient :: "pending"] #mref)) ∗
    "Hlk" ∷ is_lock urpc_lockN #lk (RPCClient_lock_inner Γ cl host mref).

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
Abort.

End rpc_proof.
