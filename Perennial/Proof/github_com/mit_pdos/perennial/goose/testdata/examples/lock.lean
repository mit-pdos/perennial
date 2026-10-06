/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/lock.v`:
a lock implemented with a buffered channel of capacity 1 (the lock channel idiom).
-/
import Perennial.Proof.ProofPrelude
import Perennial.Golang.Theory.Chan
import Perennial.Golang.Theory.Chan.Idioms.Lock
import Perennial.Golang.Theory.Chan.Idioms.Bag
import Perennial.Proof.strings
import Perennial.Proof.time
import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : lock.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock :=
  build_get_is_pkg_init_wf

end init

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics] [package_sem : lock.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock

def isLock (γ : LockChannelNames) (l : Lock) (R : IProp GF) : IProp GF :=
  iprop("#Hlock_chan" ∷ isLockChannel Unit γ l.ch' R)

instance isLock_persistent (γ : LockChannelNames) (l : Lock) (R : IProp GF) :
    Persistent (isLock γ l R) := by
  unfold isLock; infer_instance

set_option goose.wp.extras true

theorem wp_NewLock (R : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ ▷ R }}
      (App (Val (@! NewLock)) (Val #()))
    {{ (γ : LockChannelNames) (l : Lock), RET #l; isLock γ l R }} := by
  wp_start as HR
  iapply wp_fupd
  wp_apply chan.wp_make2 (V := Unit) $$ [] as %ch %γch ⟨#Hchan, %Hcap, Hoc⟩
  · ipureintro; decide
  imod start_lock_channel (V := Unit) ch R γch Hcap $$ Hchan Hoc HR with ⟨%γlock, #Hislock⟩
  imodintro
  iapply HΦ
  unfold isLock
  iexact Hislock

theorem Lock.wp_Lock (γ : LockChannelNames) (l : Lock) (R : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ isLock γ l R }}
      (App (Val (l @!! Lock.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); R }} := by
  wp_start as #Hl
  unfold isLock
  wp_auto
  wp_apply wp_lock_channel_lock (t := go.GoType.StructType []) γ l.ch' () R $$ Hl as HR
  iapply HΦ $$ HR

theorem Lock.wp_Unlock (γ : LockChannelNames) (l : Lock) (R : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ isLock γ l R ∗ R }}
      (App (Val (l @!! Lock.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hl, HR⟩
  unfold isLock
  wp_auto
  wp_apply wp_lock_channel_unlock (t := go.GoType.StructType []) γ l.ch' R $$ [$Hl $HR] as %v -
  iapply HΦ
  itrivial

theorem Lock.wp_TryLock (γ : LockChannelNames) (l : Lock) (R : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ isLock γ l R }}
      (App (Val (l @!! Lock.ty @!! go!"TryLock")) (Val #()))
    {{ (b : Bool), RET #b; if b then R else True }} := by
  wp_start as #Hl
  unfold isLock
  wp_auto_lc 1
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_singleton.2
    simp only [chan.nonblockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, l.ch', γ.lchanName, ()
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · iapply isLockChannel_is_chan $$ Hl
    iapply lock_channel_nonblocking_send_au $$ Hl Hlc1
    iintro HR
    wp_auto
    iapply HΦ $$ %true
    simp only [↓reduceIte]
    iexact HR
  · wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial

theorem Lock.wp_LockWithTimeout (γ : LockChannelNames) (l : Lock) (R : IProp GF)
    (d : time.Duration) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ isLock γ l R }}
      (App (Val (l @!! Lock.ty @!! go!"LockWithTimeout")) (Val #d))
    {{ (b : Bool), RET #b; if b then R else True }} := by
  wp_start as #Hl
  unfold isLock
  wp_auto
  wp_apply +noauto time.wp_After
  iintro %after_ch %γafter #Hafter
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, l.ch', γ.lchanName, ()
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · iapply isLockChannel_is_chan $$ Hl
    iapply lock_channel_send_au $$ Hl Hlc1
    inext
    iintro HR
    wp_auto
    iapply HΦ $$ %true
    simp only [↓reduceIte]
    iexact HR
  iapply BigAndL.bigAndL_singleton.2
  simp only [chan.blockingClausePre]
  iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, after_ch, γafter
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply is_bag_is_chan $$ Hafter
  iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hafter
  inext
  iintro %t -
  wp_auto
  iapply HΦ
  simp only [Bool.false_eq_true, ↓reduceIte]
  itrivial

end proof

end github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock

end Perennial
