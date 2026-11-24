/-
`os.Exit`'s spec.
-/
module

public import Perennial.Proof.internal.testlog.Base
public import Perennial.Proof.syscall.Base
public import Perennial.GeneratedProof.os

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
variable [package_sem : os.Assumptions]

/-- `Exit(code)` does not return (`syscall.Exit`); `Exit(0)` does not panic, since
`internal/testlog`'s flag is false (its `isPkgInit`). -/
abbrev os.Exit.spec : Prop :=
  ∀ (code : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.testlog }}
      (App (Val (@! Exit)) (Val #code))
    {{ RET #(); False }}

end spec

end Perennial
