From New.proof.go_etcd_io.etcd.client.v3_proof Require Import base op definitions.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.
Context `{!clientv3G Σ}.
Context `{!etcdserverpb.GlobalAddrs}.
Implicit Types (γ : clientv3_names).

(* #[global]
Instance bot : Bottom (option KeyValue.t) := None. *)

Axiom is_etcd_lease : ∀ γ (l : clientv3.LeaseID.t), iProp Σ.

Axiom is_etcd_lease_pers : ∀ γ l, Persistent (is_etcd_lease γ l).
Global Existing Instance is_etcd_lease_pers.

Axiom is_Client : ∀ (cl : loc) γ, iProp Σ.

Definition is_Client_pub (cl : loc) γ : iProp Σ :=
  ∃ (kv : interface.t),
  "KV" ∷ cl ↦s[clientv3.Client :: "KV"]□ kv
.

Axiom is_Client_to_pub : ∀ (cl : loc) γ, is_Client cl γ -∗ is_Client_pub cl γ.

Axiom is_Client_pers : ∀ client γ, Persistent (is_Client client γ).
Global Existing Instance is_Client_pers.

Axiom N : namespace.

(* Only specifying Do Get for now. *)
Axiom wp_Client__Do_Get : ∀ key client γ (ctx : context.Context.t) (op : clientv3.Op.t),
  ∀ Φ,
  (is_Client client γ ∗
   is_Op op (Op.Get (RangeRequest.default <| RangeRequest.key := key |>))) -∗
  (* FIXME: wrong because a lease could delete the value. *)
  (|={⊤∖↑N,∅}=> ∃ dq val, key etcd[γ]↦{dq} val ∗
                        (key etcd[γ]↦{dq} val ={∅,⊤∖↑N}=∗ Φ #())) -∗
  (* TODO: return value. *)
  WP client @ clientv3 @ "Client" @ "Do" #ctx #op {{ Φ }}.

Axiom wp_Client__GetLogger :
  ∀ (client : loc) γ,
  {{{ is_Client client γ }}}
    client @ clientv3 @ "Client'ptr" @ "GetLogger" #()
  {{{ (lg : loc), RET #lg; True }}}.

Axiom wp_Client__Ctx :
  ∀ (client : loc) γ,
  {{{ is_Client client γ }}}
    client @ clientv3 @ "Client'ptr" @ "Ctx" #()
  {{{ ctx s, RET #ctx; is_Context ctx s }}}.

Axiom wp_Client__Grant :
  ∀ client γ (ctx : context.Context.t) (ttl : w64),
  {{{ is_Client client γ }}}
    client @ clientv3 @ "Client'ptr" @ "Grant" #ctx #ttl
  {{{
      resp_ptr (resp : clientv3.LeaseGrantResponse.t) (err : error.t),
        RET (#resp_ptr, #err);
        resp_ptr ↦ resp ∗
        if decide (err = interface.nil) then
          is_etcd_lease γ resp.(clientv3.LeaseGrantResponse.ID')
        else True
  }}}.

Axiom wp_Client__KeepAlive :
  ∀ client γ (ctx : context.Context.t) id,
  (* The precondition requires that this is only called on a `Grant`ed lease. *)
  {{{ is_Client client γ ∗ is_etcd_lease γ id }}}
    client @ clientv3 @ "Client'ptr" @ "KeepAlive" #ctx #id
  {{{
      (kch : chan.t) (err : error.t),
        RET (#kch, #err);
        if decide (err = interface.nil) then
          is_chan () kch ∗
          (* Persistent ability to do receives, including when [kch] is closed;
             could wrap this in a definition *)
          □(|={⊤,∅}=> ∃ (s : chanstate.t ()),
              own_chan kch s ∗
              (own_chan kch (set chanstate.received S s) ∨ own_chan kch s ={∅,⊤}=∗ True)
            )
        else True
  }}}.

End wps.
