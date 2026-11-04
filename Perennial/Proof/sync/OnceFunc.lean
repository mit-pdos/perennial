/-
The proof of `sync.OnceFunc`.
-/
module

public import Perennial.Spec.sync.OnceFunc

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

theorem sync.OnceFunc.wp_proof :
    sync.OnceFunc.spec (GF := GF) (hG := hG) := by
  intro f
  wp_start
  wp_auto
  wp_end

end proof

end Perennial
