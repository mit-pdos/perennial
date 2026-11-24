/-
`fmt.(*fmt).writePadding`'s spec.
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

/-- `f.writePadding(n)` for `n ≤ 0`: writes nothing (the verified subset never pads). -/
abbrev fmt.fmt.writePadding.spec : Prop :=
  ∀ (f b : Loc) (F : fmtFlags) (wid prec n : w64),
    sint.Z n ≤ 0 →
    {{ fmtOwn (GF := GF) f b F wid prec }}
      (App (Val (f @!! go.GoType.PointerType fmt.fmt.ty @!! go!"writePadding")) (Val #n))
    {{ RET #(); fmtOwn f b F wid prec }}

end spec

end Perennial
