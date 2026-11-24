/-
`fmt.(*fmt).clearflags`'s spec.
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

/-- `f.clearflags()`: no flag, width or precision. -/
abbrev fmt.fmt.clearflags.spec : Prop :=
  ∀ (f b : Loc) (F : fmtFlags) (wid prec : w64),
    {{ fmtOwn (GF := GF) f b F wid prec }}
      (App (Val (f @!! go.GoType.PointerType fmt.fmt.ty @!! go!"clearflags")) (Val #()))
    {{ RET #(); fmtOwn f b noFlags (W64 0) (W64 0) }}

end spec

end Perennial
