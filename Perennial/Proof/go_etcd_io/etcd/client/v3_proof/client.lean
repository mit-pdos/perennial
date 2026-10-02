/-
Port of `new/proof/go_etcd_io/etcd/client/v3_proof/client.v`: axiomatized
specifications of the etcd client.

Lean notes:
* Every axiom binds its section assumptions explicitly (Lean does not add
  section variables to `axiom`s); the wp axioms bind
  `[package_sem : go_etcd_io.etcd.client.v3.Assumptions]`.
* Rocq's `clientv3G Σ` (an unbound, implicitly generalized class) is
  `[allG GF]`; `is_Context` and the channel theory fix `hlc := HasLC.hasLC`.
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

axiom is_etcd_lease {GF : BundledGFunctors} [allG GF] (γ : clientv3_names) (l : w64) : IProp GF

axiom is_etcd_lease_pers {GF : BundledGFunctors} [allG GF] (γ : clientv3_names) (l : w64) :
  Persistent (is_etcd_lease (GF := GF) γ l)
attribute [instance] is_etcd_lease_pers

axiom is_Client [ext : ffi_syntax] {GF : BundledGFunctors} [allG GF]
  (cl : loc) (γ : clientv3_names) : IProp GF

section defs
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics]

def is_Client_pub (cl : loc) (_γ : clientv3_names) : IProp GF :=
  iprop(∃ (kv : interface.t),
    "KV" ∷ cl.[v3.Client.t, go!"KV"] ↦□ kv)

end defs

axiom is_Client_to_pub [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
    [go_gctx : GoGlobalContext] {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
    [sem : go.Semantics] (cl : loc) (γ : clientv3_names) :
  ⊢ is_Client (GF := GF) cl γ -∗ is_Client_pub cl γ

axiom is_Client_pers [ext : ffi_syntax] {GF : BundledGFunctors} [allG GF]
  (client : loc) (γ : clientv3_names) : Persistent (is_Client (GF := GF) client γ)
attribute [instance] is_Client_pers

/-- Rocq `Axiom N : namespace`. -/
axiom N : Namespace

/-- Only specifying Do Get for now. (Rocq FIXME: wrong because a lease could
delete the value. TODO: return value.) -/
axiom wp_Client__Do_Get [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi]
    [ffi_semantics ext ffi] [go_gctx : GoGlobalContext] {GF : BundledGFunctors}
    [hG : heapGS HasLC.hasLC GF] [allG GF] [sem : go.Semantics]
    [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
    (key : go_string) (client : loc) (γ : clientv3_names) (ctx : context.Context.t)
    (op : v3.Op.t) :
  ⊢ ∀ Φ : val → IProp GF,
    (is_Client client γ ∗
     is_Op op (.Get { RangeRequest.default with key := key })) -∗
    (|={⊤ \ ↑N, ∅}=> ∃ dq val, key etcd[γ]↦{dq} val ∗
        (key etcd[γ]↦{dq} val ={∅, ⊤ \ ↑N}=∗ Φ #())) -∗
    WP (App (App (Val (client @!! v3.Client @!! go!"Do")) (Val #ctx)) (Val #op)) {{ Φ }}

axiom wp_Client__GetLogger [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi]
    [ffi_semantics ext ffi] [go_gctx : GoGlobalContext] {GF : BundledGFunctors}
    [hG : heapGS HasLC.hasLC GF] [allG GF] [sem : go.Semantics]
    [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
    (client : loc) (γ : clientv3_names) :
  {{ is_Client (GF := GF) client γ }}
    (App (Val (client @!! go.type.PointerType v3.Client @!! go!"GetLogger")) (Val #()))
  {{ (lg : loc), RET #lg; True }}

axiom wp_Client__Ctx [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi]
    [ffi_semantics ext ffi] [go_gctx : GoGlobalContext] {GF : BundledGFunctors}
    [hG : heapGS HasLC.hasLC GF] [allG GF] [sem : go.Semantics]
    [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
    (client : loc) (γ : clientv3_names) :
  {{ is_Client (GF := GF) client γ }}
    (App (Val (client @!! go.type.PointerType v3.Client @!! go!"Ctx")) (Val #()))
  {{ (ctx : interface.t_ok) (s : context.Context_desc.t (IProp GF)), RET #(interface.ok ctx);
      context.is_Context ctx s }}

axiom wp_Client__Grant [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi]
    [ffi_semantics ext ffi] [go_gctx : GoGlobalContext] {GF : BundledGFunctors}
    [hG : heapGS HasLC.hasLC GF] [allG GF] [sem : go.Semantics]
    [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
    (client : loc) (γ : clientv3_names) (ctx : context.Context.t) (ttl : w64) :
  {{ is_Client (GF := GF) client γ }}
    (App (App (Val (client @!! go.type.PointerType v3.Client @!! go!"Grant")) (Val #ctx)) (Val #ttl))
  {{ (resp_ptr : loc) (resp : v3.LeaseGrantResponse.t) (err : error.t),
      RET (PairV #resp_ptr #err);
      resp_ptr ↦ resp ∗
      if err = interface.nil then is_etcd_lease γ resp.ID' else iprop(True) }}

axiom wp_Client__KeepAlive [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi]
    [ffi_semantics ext ffi] [go_gctx : GoGlobalContext] {GF : BundledGFunctors}
    [hG : heapGS HasLC.hasLC GF] [allG GF] [sem : go.Semantics]
    [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
    (client : loc) (γ : clientv3_names) (ctx : interface.t_ok) (id : w64) :
  -- The precondition requires that this is only called on a `Grant`ed lease.
  {{ is_Client (GF := GF) client γ ∗ is_etcd_lease γ id }}
    (App (App (Val (client @!! go.type.PointerType v3.Client @!! go!"KeepAlive"))
      (Val #(interface.ok ctx))) (Val #id))
  {{ (kch : chan.t) (err : error.t), RET (PairV #kch #err);
      if err = interface.nil then
        ∃ γkch,
        is_chan kch γkch loc ∗
        -- Persistent ability to do receives, including when `kch` is closed;
        -- could wrap this in a definition
        □ (∀ Φ : loc → Bool → IProp GF, (∀ v ok, Φ v ok) -∗ recv_au γkch loc Φ)
      else iprop(True) }}

end go_etcd_io.etcd.client.v3_proof

end Perennial
end
