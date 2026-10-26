/-
The proof of `etcd_session.waitSession`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.waitSession
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Spec.errors.New

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session

set_option goose.wp.extras true

set_option maxHeartbeats 800000 in
theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.waitSession.wp_proof
    (wp_Mutex_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Mutex_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_New : errors.New.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.waitSession.spec
      (GF := GF) (hG := hG) :=
    fun {A'} [ZeroVal A'] [TypedPointsto (GF := GF) A'] [Pos.Countable A'] {A}
      [IntoValTyped (GF := GF) A' A] cancel γcancel Pcancel => by
  wp_start as #Hcancel
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg $$ []
  · iPkgInit
  ihave #Hmu := isInv_access $$ Hpkg
  wp_pures
  wp_alloc cancel_ptr as Hcancel_ptr
  wp_auto_lc 2
  wp_apply wp_Mutex_Lock $$ [$Hmu] as ⟨Hlocked, Hown⟩
  icases Hown with ⟨%ch, %γch, sessionc, #Hsessionc, #Hsessionc_is⟩
  wp_auto
  wp_apply wp_Mutex_Unlock $$ [$Hmu $Hlocked sessionc]
  · inext; iexists ch, γch; iframe; iframe #
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γch
    isplit
    · ipureintro; rfl
    isplit
    · iexact Hsessionc_is
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hsessionc
    iintro ⟨_, _⟩
    wp_auto
    wp_end
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists A', inferInstance, inferInstance, inferInstance, inferInstance, cancel, γcancel
    isplit
    · ipureintro; rfl
    isplit
    · iapply is_bag_is_chan $$ Hcancel
    iapply bag_recv_au _ _ _ _ $$ [$Hlc1 $Hlc2] Hcancel
    inext
    iintro %v Hv
    wp_auto
    wp_apply wp_New as %e _
    wp_end
    iexists v
    iexact Hv
  · iapply BigAndL.bigAndL_nil.2
    itrivial

end proof

end Perennial
