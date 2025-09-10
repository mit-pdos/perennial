Require Export New.code.go_etcd_io.etcd.server.v3.etcdserver.
Require Export New.generatedproof.go_etcd_io.etcd.server.v3.etcdserver.
Require Export New.proof.proof_prelude.
From New.proof Require Import context log fmt go_etcd_io.etcd.pkg.v3.idutil
  go_etcd_io.etcd.api.v3.etcdserverpb.

Class etcdserverG Σ :=
  {
    #[global] etcdserver_contextG :: contextG Σ;
  }.
Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!etcdserverG Σ}.

#[global] Instance : IsPkgInit proto := define_is_pkg_init True%I.
#[global] Instance : IsPkgInit traceutil := define_is_pkg_init True%I.
#[global] Instance : IsPkgInit apply.apply := define_is_pkg_init True%I.
#[global] Instance : IsPkgInit v3.auth.auth := define_is_pkg_init True%I.
#[global] Instance : IsPkgInit wait := define_is_pkg_init True%I.
#[global] Instance : IsPkgInit prometheus := define_is_pkg_init True%I.
#[global] Instance : IsPkgInit errors.errors := define_is_pkg_init True%I.
#[global] Instance : IsPkgInit config := define_is_pkg_init True%I.

#[global] Instance : IsPkgInit etcdserver := define_is_pkg_init True%I.

Lemma wp_EtcdServer__Put (s : loc) (ctx : context.Context.t) (r : loc) :
  {{{ is_pkg_init etcdserver }}}
    s @ (ptrT.id etcdserver.EtcdServer.id) @ "Put" #ctx #r
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto.
  wp_bind.
  (* Need to translate traceutil.StartTimeKey. so struct literal can be allocated *)
Abort.

Axiom EtcdServer_names : Type.
Implicit Type γ : EtcdServer_names.

Axiom is_EtcdServer : ∀ (s : loc) γ, iProp Σ.
Axiom own_ID : ∀ γ (i : w64), iProp Σ.
Axiom is_EtcdServer_access : ∀ s γ,
  is_EtcdServer s γ -∗
  ∃ (reqIDGen : loc) (max : w64),
    "#reqIDGen" ∷ s ↦s[etcdserver.EtcdServer :: "reqIDGen"]□ reqIDGen ∗
    "#HreqIDGen" ∷ is_Generator reqIDGen (own_ID γ) ∗
    "#Cfg_MaxRequestBytes" ∷
      (struct.field_ref_f config.ServerConfig "MaxRequestBytes"
         (struct.field_ref_f etcdserver.EtcdServer "Cfg" s)) ↦□ max ∗
    "_" ∷ True.

Axiom is_EtcdServer_pers : ∀ s γ, Persistent (is_EtcdServer s γ).
Existing Instance is_EtcdServer_pers.

Axiom wp_EtcdServer__getAppliedIndex : ∀ s γ,
  {{{ is_pkg_init etcdserver ∗ is_EtcdServer s γ }}}
    s @ (ptrT.id etcdserver.EtcdServer.id) @ "getAppliedIndex" #()
  {{{ (a : w64), RET #a; True }}}.

Axiom wp_EtcdServer__getCommittedIndex : ∀ s γ,
  {{{ is_pkg_init etcdserver ∗ is_EtcdServer s γ }}}
    s @ (ptrT.id etcdserver.EtcdServer.id) @ "getCommittedIndex" #()
  {{{ (a : w64), RET #a; True }}}.

Definition is_SimpleRequest r : iProp Σ :=
  "%HAuthenticate" ∷ ⌜ r.(etcdserverpb.InternalRaftRequest.Authenticate') = null ⌝ ∗
  "%HID" ∷ ⌜ r.(etcdserverpb.InternalRaftRequest.ID') = W64 0 ⌝ ∗
  "_" ∷ True
.

Axiom wp_EtcdServer__AuthInfoFromCtx : ∀ s γ ctx ctx_desc,
  {{{ is_pkg_init etcdserver ∗ is_EtcdServer s γ ∗ is_Context ctx ctx_desc }}}
    s @ (ptrT.id etcdserver.EtcdServer.id) @ "AuthInfoFromCtx" #ctx
  {{{ (a_ptr : loc) (err : interface.t), RET (#a_ptr, #err);
      if decide (a_ptr = null) then
        True
      else
        ∃ (a : auth.AuthInfo.t), a_ptr ↦ a
  }}}.

Theorem wp_optional (R: iProp Σ) e :
  ∀ Φ, R -∗ (R -∗ WP e {{ v, ⌜ v = execute_val ⌝ ∗ R }}) -∗ (R -∗ Φ execute_val) -∗ WP e {{ Φ }}.
Proof.
  iIntros "% HR He HΦ".
  iSpecialize ("He" with "[$]").
  iApply (wp_wand with "He"). iFrame.
  iIntros "* [-> HR]". iApply "HΦ". done.
Qed.

Lemma wp_EtcdServer__processInternalRaftRequestOnce (s : loc) γ (ctx : context.Context.t) ctx_desc req req_abs :
  {{{ is_pkg_init etcdserver ∗
      "#Hsrv" ∷ is_EtcdServer s γ ∗
      "req" ∷ own_InternalRaftRequest req req_abs ∗
      "#Hsimple" ∷ is_SimpleRequest req ∗
      "#Hctx" ∷ is_Context ctx ctx_desc
  }}}
    s @ (ptrT.id etcdserver.EtcdServer.id) @ "processInternalRaftRequestOnce" #ctx #req
  {{{ (a : loc) (err : interface.t), RET (#a, #err); True }}}.
Proof.
  wp_start. iNamed "Hpre".
  wp_apply wp_with_defer as "%defer Hdefer" . simpl subst.
  wp_auto. wp_apply (wp_EtcdServer__getAppliedIndex with "[$Hsrv]") as "%ai _".
  wp_apply (wp_EtcdServer__getCommittedIndex with "[$Hsrv]") as "%ci _".
  wp_if_destruct.
  {
    (* FIXME: declare then access init predicate of errors. *)
    admit.
  }
  wp_auto.
  iDestruct (is_EtcdServer_access with "Hsrv") as "H". iNamed "H".
  wp_auto. wp_apply (wp_Generator__Next with "[]"). { iFrame "#". }
  iIntros "%i Hid". wp_auto. wp_alloc hdr_ptr as "hdr". wp_auto.
  iNamed "Hsimple". rewrite HAuthenticate. wp_auto.
  wp_apply (wp_EtcdServer__AuthInfoFromCtx with "[$Hctx]").
  { iFrame "#". } iIntros "* Hauth". wp_auto.
  case_bool_decide.
  2:{ wp_auto. iApply "HΦ". done. }
  wp_auto. wp_bind (if: _ then _ else _)%E.
  iAssert ( ∃ hdr,
      "hdr" ∷ hdr_ptr ↦ hdr ∗
      "%hdr_id" ∷ ⌜ hdr.(etcdserverpb.RequestHeader.ID') = i ⌝)%I with "[$hdr //]" as "H".
  wp_apply (wp_optional with "[-]").
  { iNamedAccu. }
  { iNamed 1. case_bool_decide; wp_auto.
    - iSplitR; first done. iFrame.
    - rewrite decide_False //. iNamed "Hauth". iNamed "H".
      wp_auto. iSplitR; first done. iFrame. done. }
  iIntros "*". iNamed 1. iNamed "H".
  wp_auto.
  iClear "err". clear err_ptr.
  wp_auto.

  iDestruct (own_InternalRaftRequest_new_header with "[$] [$]") as "[%req_abs' req]".
  wp_apply (wp_InternalRaftRequest__Marshal with "[$r $req]").
  clear dependent err. iIntros "* Hmarshal". wp_auto.
  wp_if_destruct.
  2:{ rewrite bool_decide_false //. wp_auto. iApply "HΦ". done. }
  iEval (rewrite decide_True //) in "Hmarshal".
  iDestruct "Hmarshal" as "(req_ptr & req & %data & data_sl & %Hmarshal)".
  rewrite bool_decide_true //.
  wp_auto.
  wp_if_destruct.
  { wp_bind. (* FIXME: access errors init predicate *) admit. }
  wp_auto.
  rewrite HID.
  wp_auto.
  wp_bind.
  wp_apply (wp_wand with "[req]").
  {
    instantiate (1:=(λ v, "->" ∷ ⌜ v = #hdr.(etcdserverpb.RequestHeader.ID') ⌝ ∗
                        "req" ∷ own_InternalRaftRequest (req <| etcdserverpb.InternalRaftRequest.Header' := hdr_ptr |>) req_abs'
                    )%I).
    admit.
  }
  iIntros "*". iNamed 1. wp_auto.

  (* TODO:
     axiomatize `wait` for now. Prove it later.
     axiomatize prometheus Counter inc
     axiomatize `parseProposeCtxErr`
   *)

Admitted.

End wps.
