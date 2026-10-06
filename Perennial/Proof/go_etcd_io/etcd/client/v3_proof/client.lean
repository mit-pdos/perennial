/-
Port of `new/proof/go_etcd_io/etcd/client/v3_proof/client.v`: axiomatized
specifications of the etcd client.

Lean notes:
* Every axiom binds its section assumptions explicitly (Lean does not add
  section variables to `axiom`s); the wp axioms bind
  `[package_sem : go_etcd_io.etcd.client.v3.Assumptions]`.
* Rocq's `clientv3G Σ` (an unbound, implicitly generalized class) is
  `[allG GF]`; `isContext` and the channel theory fix `hlc := HasLC.hasLC`.
-/
import Perennial.Proof.go_etcd_io.etcd.client.v3_proof.base
import Perennial.Proof.go_etcd_io.etcd.client.v3_proof.op
import Perennial.Proof.go_etcd_io.etcd.client.v3_proof.definitions

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace go_etcd_io.etcd.client.v3_proof

axiom isEtcdLease {GF : BundledGFunctors} [AllG GF] (γ : Clientv3Names) (l : w64) : IProp GF

axiom isEtcdLease_pers {GF : BundledGFunctors} [AllG GF] (γ : Clientv3Names) (l : w64) :
  Persistent (isEtcdLease (GF := GF) γ l)
attribute [instance] isEtcdLease_pers

axiom isClient [ext : FfiSyntax] {GF : BundledGFunctors} [AllG GF]
  (cl : Loc) (γ : Clientv3Names) : IProp GF

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]

def isClientPub (cl : Loc) (_γ : Clientv3Names) : IProp GF :=
  iprop(∃ (kv : GoInterface),
    "KV" ∷ cl.[v3.Client, go!"KV"] ↦□ kv)

end defs

axiom isClient_to_pub [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
    [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
    [sem : go.Semantics] (cl : Loc) (γ : Clientv3Names) :
  ⊢ isClient (GF := GF) cl γ -∗ isClientPub cl γ

axiom isClient_pers [ext : FfiSyntax] {GF : BundledGFunctors} [AllG GF]
  (client : Loc) (γ : Clientv3Names) : Persistent (isClient (GF := GF) client γ)
attribute [instance] isClient_pers

/-- Rocq `Axiom N : namespace`. -/
axiom N : Namespace

/-- Only specifying Do Get for now. (Rocq FIXME: wrong because a lease could
delete the value. TODO: return value.) -/
axiom Client.wp_Do_Get [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi]
    [FfiSemantics ext ffi] [go_gctx : GoGlobalContext] {GF : BundledGFunctors}
    [hG : HeapGS HasLC.hasLC GF] [AllG GF] [sem : go.Semantics]
    [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
    (key : GoString) (client : Loc) (γ : Clientv3Names) (ctx : context.Context)
    (op : v3.Op) :
  ⊢ ∀ Φ : val → IProp GF,
    (isClient client γ ∗
     isOp op (.Get { RangeRequest.default with key := key })) -∗
    (|={⊤ \ ↑N, ∅}=> ∃ dq val, key etcd[γ]↦{dq} val ∗
        (key etcd[γ]↦{dq} val ={∅, ⊤ \ ↑N}=∗ Φ #())) -∗
    WP (App (App (Val (client @!! v3.Client.ty @!! go!"Do")) (Val #ctx)) (Val #op)) {{ Φ }}

axiom Client.wp_GetLogger [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi]
    [FfiSemantics ext ffi] [go_gctx : GoGlobalContext] {GF : BundledGFunctors}
    [hG : HeapGS HasLC.hasLC GF] [AllG GF] [sem : go.Semantics]
    [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
    (client : Loc) (γ : Clientv3Names) :
  {{ isClient (GF := GF) client γ }}
    (App (Val (client @!! go.GoType.PointerType v3.Client.ty @!! go!"GetLogger")) (Val #()))
  {{ (lg : Loc), RET #lg; True }}

axiom Client.wp_Ctx [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi]
    [FfiSemantics ext ffi] [go_gctx : GoGlobalContext] {GF : BundledGFunctors}
    [hG : HeapGS HasLC.hasLC GF] [AllG GF] [sem : go.Semantics]
    [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
    (client : Loc) (γ : Clientv3Names) :
  {{ isClient (GF := GF) client γ }}
    (App (Val (client @!! go.GoType.PointerType v3.Client.ty @!! go!"Ctx")) (Val #()))
  {{ (ctx : GoInterfaceOk) (s : context.ContextDesc (IProp GF)), RET #(interface.ok ctx);
      context.isContext ctx s }}

axiom Client.wp_Grant [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi]
    [FfiSemantics ext ffi] [go_gctx : GoGlobalContext] {GF : BundledGFunctors}
    [hG : HeapGS HasLC.hasLC GF] [AllG GF] [sem : go.Semantics]
    [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
    (client : Loc) (γ : Clientv3Names) (ctx : context.Context) (ttl : w64) :
  {{ isClient (GF := GF) client γ }}
    (App (App (Val (client @!! go.GoType.PointerType v3.Client.ty @!! go!"Grant")) (Val #ctx)) (Val #ttl))
  {{ (resp_ptr : Loc) (resp : v3.LeaseGrantResponse) (err : GoError),
      RET (PairV #resp_ptr #err);
      resp_ptr ↦ resp ∗
      if err = interface.nil then isEtcdLease γ resp.ID' else iprop(True) }}

axiom Client.wp_KeepAlive [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi]
    [FfiSemantics ext ffi] [go_gctx : GoGlobalContext] {GF : BundledGFunctors}
    [hG : HeapGS HasLC.hasLC GF] [AllG GF] [sem : go.Semantics]
    [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
    (client : Loc) (γ : Clientv3Names) (ctx : GoInterfaceOk) (id : w64) :
  -- The precondition requires that this is only called on a `Grant`ed lease.
  {{ isClient (GF := GF) client γ ∗ isEtcdLease γ id }}
    (App (App (Val (client @!! go.GoType.PointerType v3.Client.ty @!! go!"KeepAlive"))
      (Val #(interface.ok ctx))) (Val #id))
  {{ (kch : GoChan) (err : GoError), RET (PairV #kch #err);
      if err = interface.nil then
        ∃ γkch,
        isChan kch γkch Loc ∗
        -- Persistent ability to do receives, including when `kch` is closed;
        -- could wrap this in a definition
        □ (∀ Φ : Loc → Bool → IProp GF, (∀ v ok, Φ v ok) -∗ recvAu γkch Loc Φ)
      else iprop(True) }}

end go_etcd_io.etcd.client.v3_proof

end Perennial
end
