From New.proof.go_etcd_io.etcd.client.v3_proof Require Import base.

Section init.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} `{!GoContext}.
(* FIXME: don't want to list out ALL dependent package global addrs *)

(* FIXME: move these *)
Local Definition deps_mvccpb : iProp Σ := ltac2:(build_pkg_init_deps 'mvccpb).
#[global] Program Instance : IsPkgInit mvccpb :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_mvccpb;
  |}.

Local Definition deps_etcdserverpb : iProp Σ := ltac2:(build_pkg_init_deps 'etcdserverpb).
#[global] Program Instance : IsPkgInit etcdserverpb :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps_etcdserverpb;
  |}.

Local Definition deps : iProp Σ := ltac2:(build_pkg_init_deps 'clientv3).
#[global] Program Instance : IsPkgInit clientv3 :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

End init.

Axiom clientv3G : gFunctors → Set.
Existing Class clientv3G.
Axiom clientv3_names : Set.
Axiom clientv3_contextG : ∀ {Σ : gFunctors} {_:clientv3G Σ}, contextG Σ.
Global Existing Instance clientv3_contextG.

Axiom own_etcd_pointsto :
  ∀ `{!clientv3G Σ}(γ : clientv3_names) (dq : dfrac) (k : go_string) (kv : option KeyValue.t), iProp Σ.

Global Notation "k etcd[ γ ]↦ dq kv" := (own_etcd_pointsto γ dq k kv)
  (at level 20, γ at level 50, dq custom dfrac at level 1, format "k  etcd[ γ ]↦ dq  kv").
