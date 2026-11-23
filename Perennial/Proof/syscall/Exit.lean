/-
The proof of `syscall.Exit` (its trusted model, `AngelicExit`).
-/
module

public import Perennial.Spec.syscall.Exit

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : syscall.Assumptions]

theorem syscall.Exit.wp_proof :
    syscall.Exit.spec (GF := GF) (hG := hG) := fun code => by
  wp_start
  iapply wp_AngelicExit

end proof

end Perennial
