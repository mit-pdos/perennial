From New.proof.go_etcd_io.etcd.client.v3_proof Require Import base.

Section init.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
(* FIXME: don't want to list out ALL dependent package global addrs *)

(* FIXME: move these *)
#[global] Instance : IsPkgInit mvccpb := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf mvccpb := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit etcdserverpb := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf etcdserverpb := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit clientv3 := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf clientv3 := build_get_is_pkg_init_wf.

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
