Require Import New.code.go_etcd_io.etcd.client.v3.concurrency.
Require Import New.generatedproof.go_etcd_io.etcd.client.v3.concurrency.
Require Import New.proof.proof_prelude.
Require Import New.proof.go_etcd_io.etcd.client.v3.
From New.proof Require Import context sync.

Section proof.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.

(* TODO: these should be in another file ultimately. *)
Section client_axioms.

Definition has_KeepAlive (i : interface.t) : iProp Σ :=
  ∀ (ctx : context.Context.t) (id : clientv3.LeaseID.t),
  {{{ True }}}
    interface.get #i #"KeepAlive"
  {{{
      (resp : chan.t) (err : error.t),
        RET (#resp, #err);
        True
  }}}.

Axiom is_Client : ∀ (client : loc), iProp Σ.
Axiom is_Client_pers : ∀ client, Persistent (is_Client client).

Global Existing Instance is_Client_pers.

Axiom wp_Client__GetLogger :
  ∀ (client : loc),
  {{{ is_Client client }}}
    method_call #clientv3 #"Client'ptr" #"GetLogger" #client #()
  {{{ (lg : loc), RET #lg; True }}}.

Axiom wp_Client__Ctx :
  ∀ (client : loc),
  {{{ is_Client client }}}
    method_call #clientv3 #"Client'ptr" #"Ctx" #client #()
  {{{ (ctx : context.Context.t), RET #ctx; True }}}.

Axiom wp_Client__Grant :
  ∀ client (ctx : context.Context.t) (ttl : w64),
  {{{ is_Client client }}}
    method_call #clientv3 #"Client'ptr" #"Grant"
      #client #ctx #ttl
  {{{
      resp_ptr (resp : clientv3.LeaseGrantResponse.t) (err : error.t),
        RET (#resp_ptr, #err);
        resp_ptr ↦ resp
  }}}.

End client_axioms.

Context `{!concurrency.GlobalAddrs}.
Context `{!goGlobalsGS Σ}.

(* FIXME: move these *)
Program Instance : IsPkgInit math :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

Program Instance : IsPkgInit zapcore :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

Program Instance : IsPkgInit zap :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

Program Instance : IsPkgInit time :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

Program Instance : IsPkgInit strings :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

Program Instance : IsPkgInit fmt :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

Program Instance : IsPkgInit errors :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

#[global]
Program Instance : IsPkgInit concurrency :=
  ltac2:(build_pkg_init ()).
Final Obligation. Proof. apply _. Qed.

Definition is_Session (s : loc) : iProp Σ :=
  True.

Lemma wp_NewSession (client : loc) :
  {{{
        is_pkg_init concurrency ∗
        "#His_client" ∷ is_Client client
  }}}
    func_call #concurrency #"NewSession" #client #slice.nil
  {{{ s err, RET (#s, #err);
      if decide (err = interface.nil) then
        True
      else
        is_Session s
  }}}.
Proof.
  wp_start as "Hpre". iNamed "Hpre".
  wp_alloc opts_ptr as "Hopts".
  wp_pures.
  wp_alloc client_ptr as "Hclient_ptr".
  wp_pures.
  wp_alloc lg_ptr as "Hlg_ptr".
  wp_pures. wp_load.
  wp_apply (wp_Client__GetLogger with "[$]").
  iIntros (?) "_".
  wp_pures. wp_store. wp_pures.
  wp_alloc ops_ptr as "Hops_ptr".
  wp_pures. wp_load.
  wp_apply (wp_Client__Ctx with "[$]").
  iIntros (?) "_".
  wp_pures.
  wp_alloc ops as "Hops".
  wp_pures. wp_store. wp_pures.
  wp_alloc opt_ptr as "Hopt_ptr".
  wp_pures. wp_load. wp_pures.

  (* only consider nil options *)
  wp_apply wp_slice_for_range.
  { instantiate (1:=[] : list concurrency.SessionOption.t ). instantiate (1:=DfracOwn 1).
    Unshelve. all: try apply _.
    iApply own_slice_nil. }
  simpl.
  iIntros "_".

  wp_pures.
  wp_alloc id_ptr as "Hid_ptr".
  wp_pures. wp_load. wp_pures. wp_load. wp_pures. wp_store. wp_pures. wp_load.

  (* id == clientv3.NoLease, so call `Grant` *)
  wp_pures.
  wp_alloc err_ptr as "Herr_ptr".
  wp_pures.
  wp_alloc resp_ptr as "Hresp_ptr".
  wp_pures. wp_load. wp_pures. wp_load. wp_pures. wp_load. wp_pures. wp_load. wp_pures. wp_load.
  wp_apply (wp_Client__Grant with "[$]").
  iIntros "* Hresp".
  wp_pures. wp_store. wp_pures. wp_store. wp_pures. wp_load. wp_pures.
  destruct bool_decide eqn:Herr.
  2:{ (* got an error; early return *)
    wp_pures.
    wp_load.
    wp_pures.
    iApply "HΦ".
    rewrite bool_decide_eq_false in Herr.
    rewrite decide_False //.
  }
  (* no error from Grant() call *)
  wp_pures. wp_load. wp_pures. wp_load. wp_pures. wp_store. wp_pures.
  wp_alloc cancel_ptr as "Hcancel_ptr".
  wp_pures.
  wp_alloc ctx_ptr as "Hctx_ptr".
  wp_pures. wp_load. wp_pures. wp_load. wp_pures.

  (* XXX: eventually, this spec will require context.is_initialized *)
  wp_apply (wp_WithCancel nroot with "[]").
  iIntros "* [#Hctx #Hctx_done_inv]".
  wp_pures. wp_store. wp_pures. wp_store. wp_pures.
  iClear "Herr_ptr". clear err_ptr.
  wp_alloc err_ptr as "Herr_ptr". wp_pures.
  wp_alloc keepAlive_ptr as "HkeepAlive_ptr". wp_pures.
  wp_load. wp_pures. wp_load. wp_pures. wp_load.
Admitted.

End proof.
