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
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics] [package_sem : lock.Assumptions]

instance is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock :=
  build_get_is_pkg_init_wf

end init

section proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics] [package_sem : lock.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock

def is_Lock (γ : lock_channel_names) (l : Lock.t) (R : IProp GF) : IProp GF :=
  iprop("#Hlock_chan" ∷ is_lock_channel Unit γ l.ch' R)

instance is_Lock_persistent (γ : lock_channel_names) (l : Lock.t) (R : IProp GF) :
    Persistent (is_Lock γ l R) := by
  unfold is_Lock; infer_instance

set_option goose.wp.extras true

theorem wp_NewLock (R : IProp GF) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ ▷ R }}
      (App (Val (@! NewLock)) (Val #()))
    {{ (γ : lock_channel_names) (l : Lock.t), RET #l; is_Lock γ l R }} := by
  wp_start as HR
  wp_apply chan.wp_make2 (V := Unit) $$ [] as %ch %γch ⟨#Hchan, %Hcap, Hoc⟩
  · ipureintro; decide
  imod start_lock_channel (V := Unit) (t := go.type.StructType []) ch R γch Hcap $$ Hchan Hoc HR
    with ⟨%γlock, #Hislock⟩
  wp_auto
  iapply HΦ
  unfold is_Lock
  iexact Hislock

theorem wp_Lock__Lock (γ : lock_channel_names) (l : Lock.t) (R : IProp GF) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ is_Lock γ l R }}
      (App (Val (#l @!! Lock @!! go!"Lock")) (Val #()))
    {{ RET #(); R }} := by
  wp_start as #Hl
  unfold is_Lock
  wp_auto
  wp_apply wp_lock_channel_lock (t := go.type.StructType []) γ l.ch' () R $$ Hl as HR
  iapply HΦ $$ HR

theorem wp_Lock__Unlock (γ : lock_channel_names) (l : Lock.t) (R : IProp GF) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ is_Lock γ l R ∗ R }}
      (App (Val (#l @!! Lock @!! go!"Unlock")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hl, HR⟩
  unfold is_Lock
  wp_auto
  wp_apply wp_lock_channel_unlock (t := go.type.StructType []) γ l.ch' R $$ [$Hl $HR] as %v -
  iapply HΦ
  itrivial

theorem wp_Lock__TryLock (γ : lock_channel_names) (l : Lock.t) (R : IProp GF) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ is_Lock γ l R }}
      (App (Val (#l @!! Lock @!! go!"TryLock")) (Val #()))
    {{ (b : Bool), RET #b; if b then R else True }} := by
  wp_start as #Hl
  unfold is_Lock
  wp_auto_lc 1
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · simp only [BigAndL.bigAndL_cons, BigAndL.bigAndL_nil, chan.nonblocking_clause_pre]
    sorry
  · wp_auto
    iapply HΦ
    itrivial

theorem wp_Lock__LockWithTimeout (γ : lock_channel_names) (l : Lock.t) (R : IProp GF)
    (d : time.Duration.t) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ is_Lock γ l R }}
      (App (Val (#l @!! Lock @!! go!"LockWithTimeout")) (Val #d))
    {{ (b : Bool), RET #b; if b then R else True }} := by
  wp_start as #Hl
  unfold is_Lock
  wp_auto
  sorry

end proof

end github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock

end Perennial
