Require Export New.code.go_etcd_io.etcd.server.v3.etcdserver.
Require Export New.generatedproof.go_etcd_io.etcd.server.v3.etcdserver.
Require Export New.proof.proof_prelude.
From New.proof Require Import context log.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit proto := define_is_pkg_init True%I.
#[global] Instance : IsPkgInit traceutil := define_is_pkg_init True%I.
#[global] Instance : IsPkgInit etcdserverpb := define_is_pkg_init True%I.
#[global] Instance : IsPkgInit apply.apply := define_is_pkg_init True%I.
#[global] Instance : IsPkgInit v3.auth.auth := define_is_pkg_init True%I.
#[global] Instance : IsPkgInit wait := define_is_pkg_init True%I.

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

End wps.
