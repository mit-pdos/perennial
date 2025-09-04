Require Export New.code.go_etcd_io.etcd.server.v3.etcdserver.
Require Export New.generatedproof.go_etcd_io.etcd.server.v3.etcdserver.
Require Export New.proof.proof_prelude.
From New.proof Require Import context log fmt go_etcd_io.etcd.pkg.v3.idutil.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit proto := define_is_pkg_init True%I.
#[global] Instance : IsPkgInit traceutil := define_is_pkg_init True%I.
#[global] Instance : IsPkgInit etcdserverpb := define_is_pkg_init True%I.
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

Definition is_EtcdServer (s : loc) γ : iProp Σ :=
  ∃ (reqIDGen : loc),
    "reqIDGen" ∷ s ↦s[etcdserver.EtcdServer :: "reqIDGen"]□ reqIDGen ∗
    "_" ∷ True
.
#[global] Opaque is_EtcdServer.
#[local] Transparent is_EtcdServer.
Instance : ∀ s γ, Persistent (is_EtcdServer s γ).
Proof. apply _. Qed.

Axiom wp_EtcdServer__getAppliedIndex : ∀ s γ,
  {{{ is_pkg_init etcdserver ∗ is_EtcdServer s γ }}}
    s @ (ptrT.id etcdserver.EtcdServer.id) @ "getAppliedIndex" #()
  {{{ (a : w64), RET #a; True }}}.

Axiom wp_EtcdServer__getCommittedIndex : ∀ s γ,
  {{{ is_pkg_init etcdserver ∗ is_EtcdServer s γ }}}
    s @ (ptrT.id etcdserver.EtcdServer.id) @ "getCommittedIndex" #()
  {{{ (a : w64), RET #a; True }}}.

Lemma wp_EtcdServer__processInternalRaftRequestOnce (s : loc) γ (ctx : context.Context.t) (r : loc) :
  {{{ is_pkg_init etcdserver ∗ is_EtcdServer s γ }}}
    s @ (ptrT.id etcdserver.EtcdServer.id) @ "processInternalRaftRequestOnce" #ctx #r
  {{{ RET #(); True }}}.
Proof.
  wp_start as "#Hsrv".
  wp_apply wp_with_defer as "%defer Hdefer" . simpl subst.
  wp_auto. wp_apply (wp_EtcdServer__getAppliedIndex with "[$Hsrv]") as "%ai _".
  wp_apply (wp_EtcdServer__getCommittedIndex with "[$Hsrv]") as "%ci _".
  wp_if_destruct.
  {
    (* FIXME: declare then access init predicate of errors. *)
    admit.
  }
  wp_auto.
  iNamed "Hsrv".
  wp_auto.
  (* FIXME: verify [idutil] library. *)
Admitted.

End wps.
