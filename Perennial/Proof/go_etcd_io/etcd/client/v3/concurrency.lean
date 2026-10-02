/-
Port of `new/proof/go_etcd_io/etcd/client/v3/concurrency.v`.

Lean notes:
* Rocq's `concurrencyG Σ` (an unbound, implicitly generalized class) is
  `[allG GF]`; the broadcast idiom fixes `hlc := HasLC.hasLC`.
* The `zapcore`/`zap` package-init instances are the ones of
  `client/v3_proof/definitions.lean`.
-/
import Perennial.Code.go_etcd_io.etcd.client.v3.concurrency
import Perennial.GeneratedProof.go_etcd_io.etcd.client.v3.concurrency
import Perennial.Proof.ProofPrelude
import Perennial.Proof.go_etcd_io.etcd.client.v3
import Perennial.Proof.context
import Perennial.Proof.sync
import Perennial.Proof.time
import Perennial.Proof.math
import Perennial.Proof.errors
import Perennial.Proof.fmt
import Perennial.Proof.strings
import Perennial.Golang.Theory.Chan.Idioms.Broadcast

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open go_etcd_io.etcd.client.v3_proof

namespace go_etcd_io.etcd.client.v3.concurrency

section init
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : concurrency.Assumptions]

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency :=
  build_get_is_pkg_init_wf

end init

section proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics]
variable [package_sem : concurrency.Assumptions]

local notation "pkg" => pkg_id.go_etcd_io.etcd.client.v3.concurrency

def is_Session_def (s : loc) (γ : clientv3_names) (lease : v3.LeaseID.t) : IProp GF :=
  iprop(∃ (cl : loc) (donec : chan.t) (γdonec : chan_names),
    "#client" ∷ s.[Session.t, go!"client"] ↦□ cl ∗
    "#id" ∷ s.[Session.t, go!"id"] ↦□ lease ∗
    "#Hclient" ∷ is_Client cl γ ∗
    "#Hlease" ∷ is_etcd_lease γ lease ∗
    "#donec" ∷ s.[Session.t, go!"donec"] ↦□ donec ∗
    -- One can keep calling receive, and the only thing they might get back is a
    -- "closed" value.
    "#Hdonec" ∷ own_broadcast_chan donec γdonec iprop(True) .Unknown)
/-- (Rocq: `Opaque is_Session`) -/
@[irreducible] def is_Session (s : loc) (γ : clientv3_names) (lease : v3.LeaseID.t) : IProp GF :=
  is_Session_def s γ lease
theorem is_Session_unseal : @is_Session = @is_Session_def := by funext; with_unfolding_all rfl

instance is_Session_pers (s : loc) (γ : clientv3_names) (lease : v3.LeaseID.t) :
    Persistent (is_Session (GF := GF) s γ lease) := by
  rw [is_Session_unseal]; unfold is_Session_def; infer_instance

set_option maxHeartbeats 400000 in
theorem wp_NewSession (client : loc) (γetcd : clientv3_names) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗
        "#His_client" ∷ is_Client client γetcd }}
      (App (App (Val (@! NewSession)) (Val #client)) (Val #slice.nil))
    {{ (s : loc) (err : error.t), RET (PairV #s #err);
        if err = interface.nil then ∃ lease, is_Session s γetcd lease
        else iprop(True) }} := by
  wp_start as #His_client
  wp_auto
  trace_state
  sorry

theorem wp_Session__Lease (s : loc) (γ : clientv3_names) (lease : v3.LeaseID.t) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ is_Session s γ lease }}
      (App (Val (s @!! go.type.PointerType Session @!! go!"Lease")) (Val #()))
    {{ RET #lease; True }} := by
  wp_start as Hs
  rw [is_Session_unseal]
  iNamed Hs
  wp_auto
  wp_end

theorem wp_Session__Done (s : loc) (γ : clientv3_names) (lease : v3.LeaseID.t) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ is_Session s γ lease }}
      (App (Val (s @!! go.type.PointerType Session @!! go!"Done")) (Val #()))
    {{ (ch : chan.t) (γch : chan_names), RET #ch;
        own_broadcast_chan ch γch iprop(True) .Unknown }} := by
  wp_start as Hs
  rw [is_Session_unseal]
  iNamed Hs
  wp_auto
  wp_end

end proof

end go_etcd_io.etcd.client.v3.concurrency

end Perennial
end
