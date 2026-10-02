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
set_option goose.wp.extras true

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
  wp_apply wp_Client__GetLogger $$ [$His_client] as %lg -
  wp_apply wp_Client__Ctx $$ [$His_client] as %ctx %ctx_desc #Hcontext
  wp_for
  rw [show (zero_val sessionOptions.t).leaseID' = W64 0 from rfl]
  wp_auto
  wp_apply wp_Client__Grant $$ [$His_client] as %resp_ptr %resp %err ⟨Hresp, Hl⟩
  cases err with
  | ok err =>
    -- got an error; early return
    wp_auto
    iapply HΦ
    simp only [reduceCtorEq, ↓reduceIte]
    itrivial
  | nil =>
  -- no error from Grant() call
  wp_auto
  simp only [↓reduceIte]
  icases Hl with #Hlease0
  wp_apply context.wp_WithCancel iprop(True) $$ [] as %ctx' %done' %cancel ⟨#Hcancel, #Hctx⟩
  · iframe #
  wp_auto
  wp_apply wp_Client__KeepAlive $$ [$His_client $Hlease0] as %kch %err Hkch
  cases err with
  | ok err =>
    -- error
    wp_auto
    wp_apply Hcancel
    iapply HΦ
    simp only [reduceCtorEq, ↓reduceIte]
    itrivial
  | nil =>
  simp only [↓reduceIte]
  icases Hkch with ⟨%γkch, #Hkch, #Hkrecv⟩
  wp_auto
  wp_if_destruct
  · -- NOTE (Rocq): if `clientv3.lessor.KeepAlive` returns `nil` for its error, it is
    -- guaranteed to return a non-nil chan, so this case is impossible.
    ihave %hbad := is_chan_not_null $$ Hkch
    exact absurd rfl hbad
  wp_apply chan.wp_make1 (V := Unit) as %donec %γdonec ⟨#Hdonec_is, %_, Hdonec⟩
  ipersist cancel
  ipersist donec
  ipersist keepAlive
  imod alloc_broadcast_chan iprop(True) γdonec donec $$ Hdonec_is Hdonec with Hdonec_open
  ihave #Hdonec_unk := own_broadcast_chan_Unknown _ _ _ _ $$ Hdonec_open
  iStructNamed «$r0»
  ipersist client
  ipersist id
  ipersist donec
  wp_apply wp_fork $$ [Hdonec_open]
  · wp_auto
    wp_apply wp_with_defer as %defer defer
    wp_for
    wp_apply chan.wp_receive kch γkch $$ Hkch
    iintro -
    iapply Hkrecv
    iintro %v %ok
    wp_auto
    -- (`wp_if_destruct` fails here with "unknown free variable")
    cases ok
    · wp_auto
      wp_for_post
      wp_apply wp_broadcast_chan_close $$ [$Hdonec_open] as -
      · iframe #; imodintro; itrivial
      wp_apply Hcancel
      itrivial
    · wp_auto
      wp_for_post
      iframe
  iapply HΦ
  simp only [↓reduceIte]
  iexists resp.ID'
  rw [is_Session_unseal]; unfold is_Session_def
  iframe #

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
