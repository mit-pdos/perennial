/-
The proof of `lock.Lock.TryLock`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.Lock__TryLock

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock

set_option goose.wp.extras true

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.Lock.TryLock.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.Lock.TryLock.spec
      (GF := GF) (hG := hG) := fun γ l R => by
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

end proof

end Perennial
