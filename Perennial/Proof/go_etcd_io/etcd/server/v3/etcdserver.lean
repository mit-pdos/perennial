/-
Specs for etcd's `etcdserver` (the `EtcdServer` request path), mostly axiomatized.

* All axioms bind their section assumptions explicitly; the wp axioms bind
  `[package_sem : etcdserver.Assumptions]`.
* The `wait` package-init instance is the one of `pkg/v3/wait.lean`.
* There is no spec for `EtcdServer.Put`;
  `EtcdServer.wp_processInternalRaftRequestOnce` is not proved (`sorry`).
-/
import Perennial.Code.go_etcd_io.etcd.server.v3.etcdserver
import Perennial.GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver
import Perennial.Proof.ProofPrelude
import Perennial.Proof.context
import Perennial.Proof.log
import Perennial.Proof.fmt
import Perennial.Proof.time
import Perennial.Proof.go_etcd_io.etcd.pkg.v3.idutil
import Perennial.Proof.go_etcd_io.etcd.pkg.v3.wait
import Perennial.Proof.go_etcd_io.etcd.api.v3.etcdserverpb
import Perennial.Proof.go_etcd_io.raft.v3
import Perennial.Proof.go_etcd_io.etcd.api.v3.authpb
import Perennial.Proof.go_opentelemetry_io.otel.trace.embedded
import Perennial.Proof.github_com.prometheus.client_model.go

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open go_etcd_io.etcd.pkg.v3.idutil go_etcd_io.etcd.pkg.v3.wait go_etcd_io.raft.v3_proof
  go_etcd_io.etcd.api.v3.etcdserverpb

namespace go_etcd_io.etcd.server.v3.etcdserver

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : etcdserver.Assumptions]

instance proto_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.github_com.gogo.protobuf.proto :=
  define_is_pkg_init iprop(True)
instance proto_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.gogo.protobuf.proto :=
  build_get_is_pkg_init_wf

instance traceutil_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil :=
  define_is_pkg_init iprop(True)
instance apply_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply :=
  define_is_pkg_init iprop(True)
instance auth_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth :=
  define_is_pkg_init iprop(True)
instance prometheus_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus :=
  define_is_pkg_init iprop(True)
instance errors_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors :=
  define_is_pkg_init iprop(True)
instance config_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config :=
  define_is_pkg_init iprop(True)
instance trace_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_opentelemetry_io.otel.trace :=
  define_is_pkg_init iprop(True)
instance attribute_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.go_opentelemetry_io.otel.«attribute» :=
  define_is_pkg_init iprop(True)
instance features_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.features :=
  define_is_pkg_init iprop(True)
instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver :=
  define_is_pkg_init iprop(True)

end init

axiom EtcdServerNames : Type
axiom raftGn : EtcdServerNames → RaftNames

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

def waitR (_id' : w64) (v : GoInterface) : IProp GF :=
  iprop(⌜v = interface.nil⌝ ∨
    ∃ (res_ptr : Loc) (res : apply.Result),
      ⌜v = interface.mkOk apply.Result.ty #res_ptr⌝ ∗ res_ptr ↦ res)

def isSimpleRequest (r : api.v3.etcdserverpb.InternalRaftRequest) : IProp GF :=
  iprop(
  "%HAuthenticate" ∷ ⌜r.Authenticate' = null⌝ ∗
  "%HID" ∷ ⌜r.ID' = W64 0⌝ ∗
  "_" ∷ True)

end defs

axiom ownID {GF : BundledGFunctors} (γ : EtcdServerNames) (i : w64) : IProp GF
axiom ownEtcdServer {GF : BundledGFunctors} (s : Loc) (γ : EtcdServerNames) : IProp GF
axiom isEtcdServerInternal {GF : BundledGFunctors} (s : Loc) (γ : EtcdServerNames) : IProp GF

/-- `ownEtcdServer_access` (an axiom) can be used any number of
times; `isGenerator` is persistent and `idutil.Generator.wp_Next` needs no
further resource (it is proved with time receipts, see `idutil.lean`), so
`reqIDGen.Next()` can be called each time. There is no premise on
the time-receipt bound: `Next` is safe for every bound, and only the
`ownID γ i` token it returns is conditional on `receiptBound GF ≤ 2^48`. -/
axiom ownEtcdServer_access [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi]
    [FfiSemantics ext ffi] [go_gctx : GoGlobalContext] {GF : BundledGFunctors}
    [hG : HeapGS HasLC.hasLC GF] [AllG GF] [sem : go.Semantics]
    [package_sem : etcdserver.Assumptions]
    (s : Loc) (γ : EtcdServerNames) :
  ⊢ ownEtcdServer (GF := GF) s γ -∗
    ∃ (reqIDGen : Loc) (MaxRequestBytes : w64) (w : GoInterfaceOk)
      (γw : WaitParams GF) (rn : GoInterfaceOk),
      "#reqIDGen" ∷ s.[etcdserver.EtcdServer, go!"reqIDGen"] ↦□ reqIDGen ∗
      "#HreqIDGen" ∷ isGenerator reqIDGen (ownID γ) ∗
      "#Cfg_MaxRequestBytes" ∷
        s.[etcdserver.EtcdServer, go!"Cfg"].[config.ServerConfig, go!"MaxRequestBytes"] ↦□
          MaxRequestBytes ∗
      "#w" ∷ s.[etcdserver.EtcdServer, go!"w"] ↦□ (interface.ok w) ∗
      "#Hinternal" ∷ isEtcdServerInternal s γ ∗
      "#raftNode" ∷ s.[etcdserver.EtcdServer, go!"r"].[etcdserver.raftNode, go!"raftNodeConfig"]
         .[etcdserver.raftNodeConfig, go!"Node"] ↦□ (interface.ok rn) ∗
      "#Hr" ∷ is_Node (raftGn γ) rn ∗
      "Hw" ∷ ownWait γw w waitR ∗
      "Hclose" ∷ (ownWait γw w waitR -∗ ownEtcdServer s γ)

axiom isEtcdServerInternal_pers {GF : BundledGFunctors} (s : Loc) (γ : EtcdServerNames) :
  Persistent (isEtcdServerInternal (GF := GF) s γ)
attribute [instance] isEtcdServerInternal_pers

/-
`ownEtcdServer` can't be persistent because it has a `wait.Wait` inside of it,
and the implementation of `wait.Wait` uses `RWMutex`, so there can't be a
persistent `is_Wait`. Moreover, the `ownWait` depends on the value on the
RHS of the persistent points-to for field `w`. That means that we can't even
have a persistent `is_EtcdServer s γ` contained inside of `ownEtcdServer` to
encapsulate all the persistent things, since an existential variable in the
persistent part must be referred to in the exclusive part.

This would make using helper functions like `getAppliedIndex` and
`getCommittedIndex` annoying if their precondition were the standard
`ownEtcdServer`. So, instead, they are given weaker preconditions that are
persistent, and abstract away whatever knowledge they require.

AuthInfoFromCtx is trickier, because its callstack is harder to audit.
That being said, there is at least one RWMutex required by
`EtcdServer.AuthInfoFromCtx -> AuthStore.AuthInfoFromCtx -> authStore.AuthInfoFromCtx ->
authStore.IsAuthEnabled -> RWMutex.RLock`, so its precondition is the full
`ownEtcdServer`.
-/

axiom EtcdServer.wp_getAppliedIndex [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi]
    [FfiSemantics ext ffi] [go_gctx : GoGlobalContext] {hlc : HasLC} {GF : BundledGFunctors}
    [hG : HeapGS hlc GF] [sem : go.Semantics] [package_sem : etcdserver.Assumptions]
    (s : Loc) (γ : EtcdServerNames) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isEtcdServerInternal s γ }}
    (App (Val (s @!! go.GoType.PointerType etcdserver.EtcdServer.ty @!! go!"getAppliedIndex")) (Val #()))
  {{ (a : w64), RET #a; True }}

axiom EtcdServer.wp_getCommittedIndex [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi]
    [FfiSemantics ext ffi] [go_gctx : GoGlobalContext] {hlc : HasLC} {GF : BundledGFunctors}
    [hG : HeapGS hlc GF] [sem : go.Semantics] [package_sem : etcdserver.Assumptions]
    (s : Loc) (γ : EtcdServerNames) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isEtcdServerInternal s γ }}
    (App (Val (s @!! go.GoType.PointerType etcdserver.EtcdServer.ty @!! go!"getCommittedIndex")) (Val #()))
  {{ (a : w64), RET #a; True }}

axiom EtcdServer.wp_AuthInfoFromCtx [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi]
    [FfiSemantics ext ffi] [go_gctx : GoGlobalContext] {GF : BundledGFunctors}
    [hG : HeapGS HasLC.hasLC GF] [AllG GF] [sem : go.Semantics]
    [package_sem : etcdserver.Assumptions]
    (s : Loc) (γ : EtcdServerNames) (ctx : GoInterfaceOk)
    (ctx_desc : context.ContextDesc (IProp GF)) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      ownEtcdServer s γ ∗ context.isContext ctx ctx_desc }}
    (App (Val (s @!! go.GoType.PointerType etcdserver.EtcdServer.ty @!! go!"AuthInfoFromCtx"))
      (Val #(interface.ok ctx)))
  {{ (a_ptr : Loc) (err : GoInterface), RET (PairV #a_ptr #err);
      ownEtcdServer s γ ∗
      if a_ptr = null then iprop(True)
      else ∃ (a : auth.AuthInfo), a_ptr ↦ a }}

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : etcdserver.Assumptions]

theorem wp_optional (R : IProp GF) (e : Expr) :
    ⊢ ∀ Φ : val → IProp GF, R -∗
      (R -∗ WP e {{ v, ⌜v = executeVal⌝ ∗ R }}) -∗
      (R -∗ Φ executeVal) -∗ WP e {{ Φ }} := by
  iintro %Φ HR He HΦ
  ispecialize He $$ HR
  iapply wp_wand $$ He
  iintro %v ⟨%Hv, HR⟩
  subst Hv
  iapply HΦ $$ HR

/-- Takes the premise `receiptBound GF ≤ 2^48` on the time-receipt bound. It is
needed only where the token
`ownID γ id` returned by `reqIDGen.Next()` is consumed: `Next`'s postcondition
is `⌜receiptBound GF ≤ 2 ^ 48⌝ -∗ ownID γ id`, and the token stands for the
`ownUnregisteredId id` that `w.Register(id)` needs (FIXME: `ownUnregisteredId`
should be a postcondition of `idutil.Generator.Next()`; without it
`Register` may panic on a duplicate ID, as IDs wrap around after `2^48`
calls). The call to `Next` itself needs no premise. -/
theorem EtcdServer.wp_processInternalRaftRequestOnce (Hbound : receiptBound GF ≤ 2 ^ 48)
    (s : Loc) (γ : EtcdServerNames)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF))
    (req : api.v3.etcdserverpb.InternalRaftRequest) (req_abs : InternalRaftRequestC) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        "Hsrv" ∷ ownEtcdServer s γ ∗
        "req" ∷ ownInternalRaftRequest req req_abs ∗
        "#Hsimple" ∷ isSimpleRequest req ∗
        "#Hctx" ∷ context.isContext ctx ctx_desc }}
      (App (App (Val (s @!! go.GoType.PointerType etcdserver.EtcdServer.ty
          @!! go!"processInternalRaftRequestOnce")) (Val #(interface.ok ctx))) (Val #req))
    {{ (a : Loc) (err : GoInterface), RET (PairV #a #err); ownEtcdServer s γ }} := by
  -- Unprovable: calls opaque packages (prometheus, otel `SpanFromContext`, `strconv.FormatBool`) and `context.WithTimeout` (unprovable).
  -- `reqIDGen.Next()` is no longer a blocker: `idutil.Generator.wp_Next` needs only the persistent `isGenerator` from `ownEtcdServer_access` (it is proved with time receipts); `Hbound` is used only to specialize its result `⌜receiptBound GF ≤ 2 ^ 48⌝ -∗ ownID γ id` before `w.Register(id)` (whose `ownUnregisteredId` is a FIXME, see above).
  sorry -- not proved

end wps

end go_etcd_io.etcd.server.v3.etcdserver

end Perennial
end
