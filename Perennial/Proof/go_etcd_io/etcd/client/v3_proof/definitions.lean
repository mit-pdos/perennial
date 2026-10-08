/-
Basic definitions for the etcd `clientv3` proofs: the package-init instance
and the (axiomatized) etcd key-value points-to.

* The `mvccpb` and `etcdserverpb` package-init instances come from
  `Perennial/Proof/go_etcd_io/etcd/api/v3/*`.
* The `clientv3` package-init instance is declared only here.
* `ownEtcdPointsto` binds `{GF} [allG GF]`.
-/
import Perennial.Proof.go_etcd_io.etcd.client.v3_proof.base
import Perennial.Proof.go_etcd_io.etcd.api.v3.membershippb
import Perennial.Proof.go_etcd_io.etcd.api.v3.mvccpb
import Perennial.Proof.go_etcd_io.etcd.api.v3.etcdserverpb
import Perennial.Proof.io
import Perennial.Proof.go_etcd_io.etcd.api.v3.authpb

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace go_etcd_io.etcd.client.v3_proof

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

instance zapcore_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_uber_org.zap.zapcore :=
  define_is_pkg_init iprop(True)
instance zapcore_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_uber_org.zap.zapcore :=
  build_get_is_pkg_init_wf

instance zap_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_uber_org.zap :=
  define_is_pkg_init iprop(True)
instance zap_get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_uber_org.zap :=
  build_get_is_pkg_init_wf

instance clientv3_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.v3 :=
  define_is_pkg_init iprop(True)
instance clientv3_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.v3 :=
  build_get_is_pkg_init_wf

end init

/-- Ghost names of the etcd client state (axiomatized). -/
axiom Clientv3Names : Type

/-- Ownership of key `k` in etcd, with value `kv` (axiomatized). -/
axiom ownEtcdPointsto {GF : BundledGFunctors} [AllG GF] (γ : Clientv3Names) (dq : DFrac)
  (k : GoString) (kv : Option KeyValue) : IProp GF

/-- `k etcd[γ]↦{dq} kv` is `ownEtcdPointsto γ dq k kv`. -/
notation:50 k:51 " etcd[" γ "]↦{" dq "} " kv:50 => ownEtcdPointsto γ dq k kv
notation:50 k:51 " etcd[" γ "]↦ " kv:50 => ownEtcdPointsto γ (DFrac.own 1) k kv

end go_etcd_io.etcd.client.v3_proof

end Perennial
end
