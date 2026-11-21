/-
The proof of `time.Time.Location`.
-/
module

public import Perennial.Spec.time.Time__Location

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

theorem time.Time.Location.wp_proof :
    time.Time.Location.spec (GF := GF) (hG := hG) := by
  intro t
  wp_start
  ihave #Hi := isInit_access $$ Hpkg
  icases Hi with ⟨-, -, ⟨%utc, #Hutc⟩, -⟩
  wp_auto
  repeat' (first | wp_if_destruct | wp_auto)
  all_goals wp_end
end proof

end Perennial
