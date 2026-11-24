/-
The proof of `sync.runtime_notifyListWait`.
-/
module

public import Perennial.Spec.sync.runtime_notifyListWait
public import Perennial.Spec.sync.atomic.LoadUint32

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

theorem sync.runtime_notifyListWait.wp_proof
    (wp_LoadUint32 : sync.atomic.LoadUint32.spec (GF := GF) (hG := hG)) :
    sync.runtime_notifyListWait.spec (GF := GF) (hG := hG) := by
  intro l t
  wp_start as #Hl
  wp_auto
  wp_for
  wp_apply_core sync.wp_notifyList_load_notify wp_LoadUint32 l _ $$ [] Hl
  · iPkgInit
  iintro %n
  wp_auto
  cleanup_bool_decide
  by_cases h : sint.Z (W32 0) ≤ sint.Z (t - n)
  · -- ticket `t` not yet notified (`int32(t - l.notify) >= 0`): spin
    simp only [h, decide_true, ↓reduceIte]
    wp_auto
    wp_for_post
    iframe
  · -- notified: return
    simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    itrivial

end proof

end Perennial
