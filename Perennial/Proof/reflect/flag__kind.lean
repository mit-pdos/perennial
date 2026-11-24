/-
The proof of `reflect.flag.kind`.
-/
module

public import Perennial.Spec.reflect.flag__kind

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : reflect.Assumptions]

theorem reflect.flag.kind.wp_proof :
    reflect.flag.kind.spec (GF := GF) (hG := hG) := fun f => by
  wp_start
  wp_auto
  done

end proof

end Perennial
