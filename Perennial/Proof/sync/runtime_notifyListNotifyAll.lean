/-
The proof of `sync.runtime_notifyListNotifyAll`.
-/
module

public import Perennial.Spec.sync.runtime_notifyListNotifyAll
public import Perennial.Spec.sync.atomic.LoadUint32
public import Perennial.Spec.sync.atomic.CompareAndSwapUint32

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem sync.runtime_notifyListNotifyAll.wp_proof
    (wp_LoadUint32 : sync.atomic.LoadUint32.spec (GF := GF) (hG := hG))
    (wp_CompareAndSwapUint32 : sync.atomic.CompareAndSwapUint32.spec (GF := GF) (hG := hG)) :
    sync.runtime_notifyListNotifyAll.spec (GF := GF) (hG := hG) := by
  intro l
  wp_start as #Hl
  wp_auto
  wp_for
  wp_apply_core sync.wp_notifyList_load_notify wp_LoadUint32 l _ $$ [] Hl
  · iPkgInit
  iintro %n
  wp_auto
  wp_apply_core sync.wp_notifyList_load_wait wp_LoadUint32 l _ $$ [] Hl
  · iPkgInit
  iintro %w
  wp_auto
  wp_if_destruct
  · -- no waiter (`l.notify = l.wait`): return
    wp_for_post
    iapply HΦ
    itrivial
  · wp_apply_core sync.wp_notifyList_cas_notify wp_CompareAndSwapUint32 l _ _ _ $$ [] Hl
    · iPkgInit
    iintro %b
    wp_if_destruct
    · -- `l.notify` changed meanwhile: try again
      wp_for_post
      iframe
    · wp_for_post
      iapply HΦ
      itrivial

end proof

end Perennial
