/-
Port of `new/proof/go_etcd_io/etcd/server/v3/etcdserver.v`.

Lean notes:
* All axioms bind their section assumptions explicitly; the wp axioms bind
  `[package_sem : etcdserver.Assumptions]`.
* The `wait` package-init instance is the one of `pkg/v3/wait.lean` (Rocq
  re-declares it here).
* `wp_EtcdServer__Put` ends in `Abort` in Rocq and is not ported;
  `wp_EtcdServer__processInternalRaftRequestOnce` is `Admitted` (its Rocq
  proof script is almost entirely commented out).
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
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
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
instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver :=
  define_is_pkg_init iprop(True)

end init

axiom EtcdServer_names : Type
axiom raft_gn : EtcdServer_names → raft_names

section defs
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

def waitR (_id' : w64) (v : interface.t) : IProp GF :=
  iprop(⌜v = interface.nil⌝ ∨
    ∃ (res_ptr : loc) (res : apply.Result.t),
      ⌜v = interface.mk_ok apply.Result #res_ptr⌝ ∗ res_ptr ↦ res)

def is_SimpleRequest (r : api.v3.etcdserverpb.InternalRaftRequest.t) : IProp GF :=
  iprop(
  "%HAuthenticate" ∷ ⌜r.Authenticate' = null⌝ ∗
  "%HID" ∷ ⌜r.ID' = W64 0⌝ ∗
  "_" ∷ True)

end defs

axiom own_ID {GF : BundledGFunctors} (γ : EtcdServer_names) (i : w64) : IProp GF
axiom own_EtcdServer {GF : BundledGFunctors} (s : loc) (γ : EtcdServer_names) : IProp GF
/-- (Rocq: `#[local] Axiom`) -/
axiom is_EtcdServer_internal {GF : BundledGFunctors} (s : loc) (γ : EtcdServer_names) : IProp GF

axiom own_EtcdServer_access [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi]
    [ffi_semantics ext ffi] [go_gctx : GoGlobalContext] {GF : BundledGFunctors}
    [hG : heapGS HasLC.hasLC GF] [allG GF] [sem : go.Semantics]
    [package_sem : etcdserver.Assumptions]
    (s : loc) (γ : EtcdServer_names) :
  ⊢ own_EtcdServer (GF := GF) s γ -∗
    ∃ (reqIDGen : loc) (MaxRequestBytes : w64) (w : interface.t_ok) (γw : wait_params GF)
      (rn : interface.t_ok),
      "#reqIDGen" ∷ s.[etcdserver.EtcdServer.t, go!"reqIDGen"] ↦□ reqIDGen ∗
      "#HreqIDGen" ∷ is_Generator reqIDGen (own_ID γ) ∗
      "#Cfg_MaxRequestBytes" ∷
        s.[etcdserver.EtcdServer.t, go!"Cfg"].[config.ServerConfig.t, go!"MaxRequestBytes"] ↦□
          MaxRequestBytes ∗
      "#w" ∷ s.[etcdserver.EtcdServer.t, go!"w"] ↦□ (interface.ok w) ∗
      "#Hinternal" ∷ is_EtcdServer_internal s γ ∗
      "#raftNode" ∷ s.[etcdserver.EtcdServer.t, go!"r"].[etcdserver.raftNode.t, go!"raftNodeConfig"]
         .[etcdserver.raftNodeConfig.t, go!"Node"] ↦□ (interface.ok rn) ∗
      "#Hr" ∷ is_Node (raft_gn γ) rn ∗
      "Hw" ∷ own_Wait γw w waitR ∗
      "Hclose" ∷ (own_Wait γw w waitR -∗ own_EtcdServer s γ)

axiom is_EtcdServer_internal_pers {GF : BundledGFunctors} (s : loc) (γ : EtcdServer_names) :
  Persistent (is_EtcdServer_internal (GF := GF) s γ)
attribute [instance] is_EtcdServer_internal_pers

/-
(Rocq:) `own_EtcdServer` can't be persistent because it has a `wait.Wait` inside of it,
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
-/

axiom wp_EtcdServer__getAppliedIndex [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi]
    [ffi_semantics ext ffi] [go_gctx : GoGlobalContext] {hlc : HasLC} {GF : BundledGFunctors}
    [hG : heapGS hlc GF] [sem : go.Semantics] [package_sem : etcdserver.Assumptions]
    (s : loc) (γ : EtcdServer_names) :
  {{ is_pkg_init (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      is_EtcdServer_internal s γ }}
    (App (Val (s @!! go.type.PointerType etcdserver.EtcdServer @!! go!"getAppliedIndex")) (Val #()))
  {{ (a : w64), RET #a; True }}

axiom wp_EtcdServer__getCommittedIndex [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi]
    [ffi_semantics ext ffi] [go_gctx : GoGlobalContext] {hlc : HasLC} {GF : BundledGFunctors}
    [hG : heapGS hlc GF] [sem : go.Semantics] [package_sem : etcdserver.Assumptions]
    (s : loc) (γ : EtcdServer_names) :
  {{ is_pkg_init (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      is_EtcdServer_internal s γ }}
    (App (Val (s @!! go.type.PointerType etcdserver.EtcdServer @!! go!"getCommittedIndex")) (Val #()))
  {{ (a : w64), RET #a; True }}

axiom wp_EtcdServer__AuthInfoFromCtx [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi]
    [ffi_semantics ext ffi] [go_gctx : GoGlobalContext] {GF : BundledGFunctors}
    [hG : heapGS HasLC.hasLC GF] [allG GF] [sem : go.Semantics]
    [package_sem : etcdserver.Assumptions]
    (s : loc) (γ : EtcdServer_names) (ctx : interface.t_ok)
    (ctx_desc : context.Context_desc.t (IProp GF)) :
  {{ is_pkg_init (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      own_EtcdServer s γ ∗ context.is_Context ctx ctx_desc }}
    (App (Val (s @!! go.type.PointerType etcdserver.EtcdServer @!! go!"AuthInfoFromCtx"))
      (Val #(interface.ok ctx)))
  {{ (a_ptr : loc) (err : interface.t), RET (PairV #a_ptr #err);
      own_EtcdServer s γ ∗
      if a_ptr = null then iprop(True)
      else ∃ (a : auth.AuthInfo.t), a_ptr ↦ a }}

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics]
variable [package_sem : etcdserver.Assumptions]

theorem wp_optional (R : IProp GF) (e : expr) :
    ⊢ ∀ Φ : val → IProp GF, R -∗
      (R -∗ WP e {{ v, ⌜v = execute_val⌝ ∗ R }}) -∗
      (R -∗ Φ execute_val) -∗ WP e {{ Φ }} := by
  iintro %Φ HR He HΦ
  ispecialize He $$ HR
  iapply wp_wand $$ He
  iintro %v ⟨%Hv, HR⟩
  subst Hv
  iapply HΦ $$ HR

theorem wp_EtcdServer__processInternalRaftRequestOnce (s : loc) (γ : EtcdServer_names)
    (ctx : interface.t_ok) (ctx_desc : context.Context_desc.t (IProp GF))
    (req : api.v3.etcdserverpb.InternalRaftRequest.t) (req_abs : InternalRaftRequestC) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        "Hsrv" ∷ own_EtcdServer s γ ∗
        "req" ∷ own_InternalRaftRequest req req_abs ∗
        "#Hsimple" ∷ is_SimpleRequest req ∗
        "#Hctx" ∷ context.is_Context ctx ctx_desc }}
      (App (App (Val (s @!! go.type.PointerType etcdserver.EtcdServer
          @!! go!"processInternalRaftRequestOnce")) (Val #(interface.ok ctx))) (Val #req))
    {{ (a : loc) (err : interface.t), RET (PairV #a #err); own_EtcdServer s γ }} := by
  -- Unprovable: calls opaque packages (prometheus, otel `SpanFromContext`, `strconv.FormatBool`) and `context.WithTimeout` (unprovable).
  sorry -- Rocq: Admitted

end wps

end go_etcd_io.etcd.server.v3.etcdserver

end Perennial
end
