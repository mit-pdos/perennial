Require Export New.code.go_etcd_io.etcd.server.v3.etcdserver.
Require Export New.generatedproof.go_etcd_io.etcd.server.v3.etcdserver.
Require Export New.proof.proof_prelude.
From New.proof Require Import context log fmt time
  go_etcd_io.etcd.pkg.v3.idutil
  go_etcd_io.etcd.pkg.v3.wait
  go_etcd_io.etcd.api.v3.etcdserverpb
  go_etcd_io.raft.v3.

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
Axiom raft_gn : EtcdServer_names → raft_names.
Implicit Type γ : EtcdServer_names.

Definition waitR (id' : w64) v : iProp Σ :=
  (⌜ v = interface.nil ⌝) ∨
    ∃ res_ptr (res : apply.Result.t),
      ⌜ v = interface.mk (apply.Result.id) #res_ptr ⌝ ∗ res_ptr ↦ res.

Axiom own_ID : ∀ γ (i : w64), iProp Σ.
Axiom own_EtcdServer : ∀ (s : loc) γ, iProp Σ.
#[local] Axiom is_EtcdServer_internal : ∀ (s : loc) γ, iProp Σ.
Axiom own_EtcdServer_access : ∀ s γ,
  own_EtcdServer s γ -∗
  ∃ (reqIDGen : loc) (MaxRequestBytes : w64) w γw rn,
    "#reqIDGen" ∷ s ↦s[etcdserver.EtcdServer :: "reqIDGen"]□ reqIDGen ∗
    "#HreqIDGen" ∷ is_Generator reqIDGen (own_ID γ) ∗
    "#Cfg_MaxRequestBytes" ∷
      (struct.field_ref_f config.ServerConfig "MaxRequestBytes"
         (struct.field_ref_f etcdserver.EtcdServer "Cfg" s)) ↦□ MaxRequestBytes ∗
    "#w" ∷ s ↦s[etcdserver.EtcdServer :: "w"]□ w ∗
    "#Hinternal" ∷ is_EtcdServer_internal s γ ∗
    "#raftNode" ∷
      (struct.field_ref_f etcdserver.raftNodeConfig "Node"
         (struct.field_ref_f etcdserver.raftNode "raftNodeConfig"
            (struct.field_ref_f etcdserver.EtcdServer "r" s))) ↦□ rn ∗
    "#Hr" ∷ is_Node (raft_gn γ) rn ∗
    "Hw" ∷ own_Wait γw w waitR ∗
    "Hclose" ∷ (own_Wait γw w waitR -∗ own_EtcdServer s γ)
.

Axiom is_EtcdServer_internal_pers : ∀ s γ, Persistent (is_EtcdServer_internal s γ).
Existing Instance is_EtcdServer_internal_pers.

(* `own_EtcdServer` can't be persistent because it has a `wait.Wait` inside of it,
   and the implementation of `wait.Wait` uses `RWMutex`, so there can't be a
   persistent `is_Wait`. Moreover, the `own_Wait` depends on the value on the
   RHS of the persistent points-to for field `w`. That means that we can't even
   have a persistent `is_EtcdServer s γ` contained inside of `own_EtcdServer` to
   encapsulate all the persistent things, since an existential variable in the
   persistent part must be referred to in the exclusive part.

   This would make using helper functions like `getAppliedIndex` and
   `getCommittedIndex` annoying if their precondition were the standard
   `own_EtcdServer`. So, instead, they are given weaker preconditions that are
   persistent, and abstract away whatever knowledge they require.

   AuthInfoFromCtx is trickier, because its callstack is harder to audit.
   That being said, there is at least one RWMutex required by
   `EtcdServer.AuthInfoFromCtx -> AuthStore.AuthInfoFromCtx -> authStore.AuthInfoFromCtx ->
   authStore.IsAuthEnabled -> RWMutex.RLock`, so its precondition is the full
   `own_EtcdServer`.
 *)

Axiom wp_EtcdServer__getAppliedIndex : ∀ s γ,
  {{{ is_pkg_init etcdserver ∗ is_EtcdServer_internal s γ }}}
    s @ (ptrT.id etcdserver.EtcdServer.id) @ "getAppliedIndex" #()
  {{{ (a : w64), RET #a; True }}}.

Axiom wp_EtcdServer__getCommittedIndex : ∀ s γ,
  {{{ is_pkg_init etcdserver ∗ is_EtcdServer_internal s γ }}}
    s @ (ptrT.id etcdserver.EtcdServer.id) @ "getCommittedIndex" #()
  {{{ (a : w64), RET #a; True }}}.

Definition is_SimpleRequest r : iProp Σ :=
  "%HAuthenticate" ∷ ⌜ r.(etcdserverpb.InternalRaftRequest.Authenticate') = null ⌝ ∗
  "%HID" ∷ ⌜ r.(etcdserverpb.InternalRaftRequest.ID') = W64 0 ⌝ ∗
  "_" ∷ True
.

Axiom wp_EtcdServer__AuthInfoFromCtx : ∀ s γ ctx ctx_desc,
  {{{ is_pkg_init etcdserver ∗ own_EtcdServer s γ ∗ is_Context ctx ctx_desc }}}
    s @ (ptrT.id etcdserver.EtcdServer.id) @ "AuthInfoFromCtx" #ctx
  {{{ (a_ptr : loc) (err : interface.t), RET (#a_ptr, #err);
      own_EtcdServer s γ ∗
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
      "Hsrv" ∷ own_EtcdServer s γ ∗
      "req" ∷ own_InternalRaftRequest req req_abs ∗
      "#Hsimple" ∷ is_SimpleRequest req ∗
      "#Hctx" ∷ is_Context ctx ctx_desc
  }}}
    s @ (ptrT.id etcdserver.EtcdServer.id) @ "processInternalRaftRequestOnce" #ctx #req
  {{{ (a : loc) (err : interface.t), RET (#a, #err); own_EtcdServer s γ }}}.
Proof.
  wp_start. iNamed "Hpre".
  wp_apply wp_with_defer as "%defer Hdefer" . simpl subst.
  wp_auto.
  iDestruct (own_EtcdServer_access with "Hsrv") as "H". iNamed "H".
  wp_apply (wp_EtcdServer__getAppliedIndex with "[$Hinternal]") as "%ai _".
  wp_apply (wp_EtcdServer__getCommittedIndex with "[$Hinternal]") as "%ci _".
  wp_if_destruct.
  {
    (* FIXME: declare then access init predicate of errors. *)
    admit.
  }
  wp_apply (wp_Generator__Next with "[]"). { iFrame "#". }
  iIntros "%i Hid". wp_auto. wp_alloc hdr_ptr as "hdr". wp_auto.
  iNamed "Hsimple". rewrite HAuthenticate. wp_auto.
  iDestruct ("Hclose" with "[$]") as "Hsrv".
  wp_apply (wp_EtcdServer__AuthInfoFromCtx with "[$Hctx $Hsrv]").
  iIntros "* (Hsrv & Hauth)". wp_auto.
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
  case_bool_decide.
  2:{ wp_auto. iApply "HΦ". done. }
  iEval (rewrite decide_True //) in "Hmarshal".
  iDestruct "Hmarshal" as "(req_ptr & req & %data & data_sl & %Hmarshal)".
  wp_auto. wp_if_destruct.
  { wp_bind. (* FIXME: access errors init predicate *) admit. }
  rewrite HID. wp_auto. wp_bind.
  wp_apply (wp_wand with "[req]").
  {
    instantiate (1:=(λ v, "->" ∷ ⌜ v = #hdr.(etcdserverpb.RequestHeader.ID') ⌝ ∗
                        "req" ∷ own_InternalRaftRequest (req <| etcdserverpb.InternalRaftRequest.Header' := hdr_ptr |>) req_abs'
                    )%I).
    admit.
  }
  iIntros "*". iNamed 1.
  iDestruct (own_EtcdServer_access with "Hsrv") as "H".
  iClear "reqIDGen HreqIDGen Cfg_MaxRequestBytes w Hinternal Hr raftNode".
  clear dependent reqIDGen MaxRequestBytes w γw.
  iNamed "H".
  wp_auto. wp_apply (wp_Wait__Register with "[Hw]").
  { iFrame. admit. } (* FIXME: own_unregistered as postcondition of idutil.Generator.Next() *)
  iIntros (ch) "(Hw & Hch)". wp_auto. wp_bind. wp_apply wp_wand.
  { instantiate (1:=λ v, (∃ (t : time.Duration.t), ⌜ v = #t ⌝)%I). admit. }
  iIntros "% [% ->]".
  wp_auto. wp_apply wp_WithTimeout. { iFrame "#". } iIntros "* (Hcancel & #Hcctx)".
  wp_auto. wp_apply wp_Now as "% _".
  wp_bind.

  (* FIXME: this is loading the entire `raftNode` struct for calling the
     embedded Propose method. Really, Go does *not* copy the entire struct until
     getting to the bottom. I.e. we should read this sentence of the Go spec very strictly:
     > If x is addressable and &x's method set contains m, x.m() is shorthand for (&x).m():
     Here, s.r.Propose means (&s.r).Propose because (s.r) is addressable and
     (&s.r) contains Propose. That might make stuff work out OK.
   *)

  (* TODO:
     axiomatize prometheus Counter inc
     axiomatize `parseProposeCtxErr`
   *)
Admitted.

End wps.
