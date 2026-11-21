/-
The proof of `time.unixTime`.
-/
module

public import Perennial.Spec.time.unixTime

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

theorem time.unixTime.wp_proof :
    time.unixTime.spec (GF := GF) (hG := hG) := by
  intro sec nsec
  wp_start
  ihave #Hi := isInit_access $$ Hpkg
  icases Hi with ⟨⟨%sn, #Hsn⟩, ⟨%loc, #Hloc⟩, -⟩
  wp_auto
  wp_end

end proof

end Perennial
