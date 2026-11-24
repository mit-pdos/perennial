/-
The proof of `sync.runtime_notifyListAdd`.
-/
module

public import Perennial.Spec.sync.runtime_notifyListAdd
public import Perennial.Spec.internal.gomodel.ChooseUint64

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
    (wp_ChooseUint64 : internal.gomodel.ChooseUint64.spec (GF := GF) (hG := hG)) :
    sync.runtime_notifyListAdd.spec (GF := GF) (hG := hG) := by
  intro l l_v dq
  wp_start as Hl
  wp_auto
  wp_apply wp_ChooseUint64 as %x _
  wp_end

end proof

end Perennial
