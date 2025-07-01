From New.proof.go_etcd_io.etcd.client.v3_proof Require Import base.

Section init.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.
(* FIXME: don't want to list out ALL dependent package global addrs *)
Context `{!etcdserverpb.GlobalAddrs}.

(* FIXME: move these *)
#[global]
Program Instance is_pkg_init_mvccpb : IsPkgInit mvccpb :=
  ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_mvccpb.

#[global]
Program Instance is_pkg_init_etcdserverpb : IsPkgInit etcdserverpb :=
  ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_etcdserverpb.

#[global]
Program Instance is_pkg_init_clientv3 : IsPkgInit clientv3 :=
  ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_clientv3.

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
