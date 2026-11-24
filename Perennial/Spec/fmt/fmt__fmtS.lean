/-
`fmt.(*fmt).fmtS`'s spec.
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

/-- `f.fmtS(s)` without a width or precision: appends `s`. -/
abbrev fmt.fmt.fmtS.spec : Prop :=
  ∀ (f b : Loc) (F : fmtFlags) (wid prec : w64) (bs s : GoString),
    F.precPresent' = false → (F.widPresent' = false ∨ wid = W64 0) →
    {{ fmtOwn (GF := GF) f b F wid prec ∗ bufferOwn b bs }}
      (App (Val (f @!! go.GoType.PointerType fmt.fmt.ty @!! go!"fmtS")) (Val #s))
    {{ RET #(); fmtOwn f b F wid prec ∗ bufferOwn b (bs ++ s) }}

end spec

end Perennial
