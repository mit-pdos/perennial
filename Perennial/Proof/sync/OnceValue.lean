/-
The proof of `sync.OnceValue`.
-/
module

public import Perennial.Spec.sync.OnceValue

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

theorem sync.OnceValue.wp_proof :
    sync.OnceValue.spec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ f
  wp_start
  wp_auto
  wp_end

end proof

end Perennial
