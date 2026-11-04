/-
The proof of `sync.OnceValues`.
-/
module

public import Perennial.Spec.sync.OnceValues

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

theorem sync.OnceValues.wp_proof :
    sync.OnceValues.spec (GF := GF) (hG := hG) := by
  intro T1' _ _ T1 _ T2' _ _ T2 _ f
  wp_start
  wp_auto
  wp_end

end proof

end Perennial
