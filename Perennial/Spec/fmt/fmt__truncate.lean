/-
`fmt.(*fmt).truncate`'s spec.
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

/-- `f.truncate(p)` without a precision: `p`. -/
abbrev fmt.fmt.truncate.spec : Prop :=
  ∀ (f b : Loc) (F : fmtFlags) (wid prec : w64) (sl : GoSlice),
    F.precPresent' = false →
    {{ fmtOwn (GF := GF) f b F wid prec }}
      (App (Val (f @!! go.GoType.PointerType fmt.fmt.ty @!! go!"truncate")) (Val #sl))
    {{ RET #sl; fmtOwn f b F wid prec }}

end spec

end Perennial
