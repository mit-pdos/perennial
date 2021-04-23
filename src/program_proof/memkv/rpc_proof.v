From Goose.github_com.mit_pdos.gokv.urpc Require Import rpc.
From Perennial.program_proof Require Import dist_prelude.
From Perennial.program_proof Require Import marshal_proof.

Class rpcregG (Σ : gFunctors) := RpcRegG {
  rpcreg_map : gmap (u64*u64) { X: Type & ((X → list u8 → iProp Σ) * (X → list u8 → list u8 → iProp Σ))%type };
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

(* TODO: needs some gname parameter *)
Definition client_chan_inner (host: u64) (specs : rpc_spec_map) : iProp Σ := True.

Definition server_chan_inner (host: u64) (specs : rpc_spec_map) : iProp Σ :=
  ∃ ms, "Hchan" ∷ host c↦ ms ∗
  "Hmessages" ∷ [∗ set] m ∈ ms,
    ∃ rpcid seqno args X Pre Post (x : X),
       "%Henc" ∷ ⌜ has_encoding (msg_data m) [EncUInt64 rpcid; EncUInt64 seqno;
                                              EncUInt64 (length args); EncBytes args] ⌝ ∗
       "%Hlookup_spec" ∷ ⌜ specs !! rpcid = Some (existT X (Pre, Post)) ⌝ ∗
       "HPre" ∷ □ (Pre x args) ∗
       "Hclient_chan_inv" ∷ inv urpc_clientN (client_chan_inner (msg_sender m) specs)
       (* TODO: need some ghost state which probably gets linked with client_chan_inner *)
.


Definition handler_is : ∀ (X:Type) (host:u64) (rpcid:u64) (Pre:X → list u8 → iProp Σ)
                          (Post:X → list u8 → list u8 → iProp Σ), iProp Σ :=
  λ X host rpcid Pre Post,
  "%Hprepost" ∷ ⌜ rpcreg_map !! (host, rpcid) = Some (existT X (Pre, Post)) ⌝%I.

Global Instance handler_is_pers_instance X host rpcid pre post : Persistent (handler_is X host rpcid pre post).
Proof. apply _. Qed.


Definition RPCClient_own (cl_ptr : loc) (host:u64) : iProp Σ := True%I.

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
                              (*
    "Hstfields" ∷ ("mu" ∷ readonly (cl ↦[RPCClient :: "mu"] #lk ∗
     "send" ∷ readonly (cl ↦[RPCClient :: "send"] send_endpoint host r
     "pending" ∷ readonly (cl ↦[RPCClient :: "pending"] #mref

     -- "seq" ∷ readonly (cl ↦[RPCClient :: "seq"] #n
                               *)
Abort.

End rpc_proof.
