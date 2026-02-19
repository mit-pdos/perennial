From New.proof.go_etcd_io.etcd.client.v3_proof Require Import base.
Require Import New.proof.go_etcd_io.etcd.api.v3.membershippb.

Section init.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : clientv3.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) mvccpb := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) mvccpb := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) etcdserverpb := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) etcdserverpb := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) zapcore := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) zapcore := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) zap := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) zap := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) clientv3 := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) clientv3 := build_get_is_pkg_init_wf.

End init.

Axiom clientv3_names : Set.

Axiom own_etcd_pointsto :
  ∀ `{!allG Σ} (γ : clientv3_names) (dq : dfrac) (k : go_string) (kv : option KeyValue.t), iProp Σ.

Global Notation "k etcd[ γ ]↦ dq kv" := (own_etcd_pointsto γ dq k kv)
  (at level 20, γ at level 50, dq custom dfrac at level 1, format "k  etcd[ γ ]↦ dq  kv").
