/-
The proof of `sync.runtime_notifyListAdd`.
-/
module

public import Perennial.Spec.sync.runtime_notifyListAdd
public import Perennial.Spec.sync.atomic.AddUint32

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

theorem sync.runtime_notifyListAdd.wp_proof
    (wp_AddUint32 : sync.atomic.AddUint32.spec (GF := GF) (hG := hG)) :
    sync.runtime_notifyListAdd.spec (GF := GF) (hG := hG) := by
  intro l
  wp_start as #Hl
  wp_auto
  wp_apply_core sync.wp_notifyList_add_wait wp_AddUint32 l (W32 1) _ $$ [] Hl
  · iPkgInit
  iintro %w
  wp_auto
  wp_end

end proof

end Perennial
