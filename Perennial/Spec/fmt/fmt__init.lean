/-
`fmt.(*fmt).init`'s spec.
-/
module

public import Perennial.Proof.fmt.PrintDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

/-- `f.init(b)`: the `fmt` at `f` writes to the buffer at `b`, with no flag, width or precision. -/
abbrev fmt.fmt.init.spec : Prop :=
  ∀ (f b : Loc) (v : fmt.fmt),
    {{ (f ↦ v : IProp GF) }}
      (App (Val (f @!! go.GoType.PointerType fmt.fmt.ty @!! go!"init")) (Val #b))
    {{ RET #(); fmtOwn f b noFlags (W64 0) (W64 0) }}

end spec

end Perennial
