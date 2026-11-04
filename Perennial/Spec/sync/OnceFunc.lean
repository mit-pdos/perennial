/-
`sync.OnceFunc`'s spec.
-/
module

public import Perennial.Proof.sync.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- `OnceFunc(f)` returns a function. It only allocates the state the function keeps: what
calling the function does is not specified here. -/
abbrev sync.OnceFunc.spec : Prop :=
  ∀ (f : GoFunc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync }}
      (App (Val #(functions OnceFunc [])) (Val #f))
    {{ (g : GoFunc), RET #g; True }}

end spec

end Perennial
