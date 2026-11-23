/-
`syscall.Exit`'s spec.
-/
module

public import Perennial.Proof.syscall.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : syscall.Assumptions]

/-- `Exit(code)` does not return: the process ends (`TrustedCode/syscall.lean`). -/
abbrev syscall.Exit.spec : Prop :=
  ∀ (code : w64),
    {{ (True : IProp GF) }}
      (App (Val (@! Exit)) (Val #code))
    {{ RET #(); False }}

end spec

end Perennial
