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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : concurrency.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency :=
  build_get_is_pkg_init_wf

end init

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : concurrency.Assumptions]

local notation "pkg" => pkg_id.go_etcd_io.etcd.client.v3.concurrency

def isSessionDef (s : Loc) (γ : Clientv3Names) (lease : v3.LeaseID) : IProp GF :=
  iprop(∃ (cl : Loc) (donec : GoChan) (γdonec : ChanNames),
    "#client" ∷ s.[Session, go!"client"] ↦□ cl ∗
    "#id" ∷ s.[Session, go!"id"] ↦□ lease ∗
    "#Hclient" ∷ isClient cl γ ∗
    "#Hlease" ∷ isEtcdLease γ lease ∗
    "#donec" ∷ s.[Session, go!"donec"] ↦□ donec ∗
    -- One can keep calling receive, and the only thing they might get back is a
    -- "closed" value.
    "#Hdonec" ∷ ownBroadcastChan donec γdonec iprop(True) .Unknown)
/-- (Rocq: `Opaque isSession`) -/
@[irreducible] def isSession (s : Loc) (γ : Clientv3Names) (lease : v3.LeaseID) : IProp GF :=
  isSessionDef s γ lease
theorem isSession_unseal : @isSession = @isSessionDef := by funext; with_unfolding_all rfl

instance isSession_pers (s : Loc) (γ : Clientv3Names) (lease : v3.LeaseID) :
    Persistent (isSession (GF := GF) s γ lease) := by
  rw [isSession_unseal]; unfold isSessionDef; infer_instance

set_option maxHeartbeats 400000 in
theorem wp_NewSession (client : Loc) (γetcd : Clientv3Names) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗
        "#His_client" ∷ isClient client γetcd }}
      (App (App (Val (@! NewSession)) (Val #client)) (Val #slice.nil))
    {{ (s : Loc) (err : GoError), RET (PairV #s #err);
        if err = interface.nil then ∃ lease, isSession s γetcd lease
        else iprop(True) }} := by
  wp_start as #His_client
  wp_auto
  wp_apply Client.wp_GetLogger $$ [$His_client] as %lg -
  wp_apply Client.wp_Ctx $$ [$His_client] as %ctx %ctx_desc #Hcontext
  wp_for
  wp_apply Client.wp_Grant $$ [$His_client] as %resp_ptr %resp %err ⟨Hresp, Hl⟩
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
  wp_apply context.wp_WithCancel iprop(True) $$ [] as %ctx' %γctx' %cancel ⟨#Hcancel, #Hctx⟩
  · iframe #
  wp_auto
  wp_apply Client.wp_KeepAlive $$ [$His_client $Hlease0] as %kch %err Hkch
  cases err with
  | ok err =>
    -- error
    wp_auto
    wp_apply Hcancel
    · imodintro; itrivial
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
    ihave %hbad := isChan_not_null $$ Hkch
    exact absurd rfl hbad
  wp_apply chan.wp_make1 (V := Unit) as %donec %γdonec ⟨#Hdonec_is, %_, Hdonec⟩
  ipersist cancel
  ipersist donec
  ipersist keepAlive
  imod alloc_broadcast_chan iprop(True) γdonec donec $$ Hdonec_is Hdonec with Hdonec_open
  ihave #Hdonec_unk := ownBroadcastChan_Unknown _ _ _ _ $$ Hdonec_open
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
    cases ok
    · wp_auto
      wp_for_post
      wp_apply wp_broadcast_chan_close $$ [$Hdonec_open] as -
      · iframe #; imodintro; itrivial
      wp_apply Hcancel
      · imodintro; itrivial
      itrivial
    · wp_auto
      wp_for_post
      iframe
  iapply HΦ
  simp only [↓reduceIte]
  iexists resp.ID'
  rw [isSession_unseal]; unfold isSessionDef
  iframe #

theorem Session.wp_Lease (s : Loc) (γ : Clientv3Names) (lease : v3.LeaseID) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ isSession s γ lease }}
      (App (Val (s @!! go.GoType.PointerType Session.ty @!! go!"Lease")) (Val #()))
    {{ RET #lease; True }} := by
  wp_start as Hs
  rw [isSession_unseal]
  iNamed Hs
  wp_auto
  wp_end

theorem Session.wp_Done (s : Loc) (γ : Clientv3Names) (lease : v3.LeaseID) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ isSession s γ lease }}
      (App (Val (s @!! go.GoType.PointerType Session.ty @!! go!"Done")) (Val #()))
    {{ (ch : GoChan) (γch : ChanNames), RET #ch;
        ownBroadcastChan ch γch iprop(True) .Unknown }} := by
  wp_start as Hs
  rw [isSession_unseal]
  iNamed Hs
  wp_auto
  wp_end

end proof

end go_etcd_io.etcd.client.v3.concurrency

end Perennial
end
