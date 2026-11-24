/-
`fmt.(*fmt).fmtBoolean`'s spec.
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

/-- `f.fmtBoolean(v)` without a width: appends `true` or `false`. -/
abbrev fmt.fmt.fmtBoolean.spec : Prop :=
  ∀ (f b : Loc) (F : fmtFlags) (wid prec : w64) (bs : GoString) (v : Bool),
    F.widPresent' = false ∨ wid = W64 0 →
    {{ fmtOwn (GF := GF) f b F wid prec ∗ bufferOwn b bs }}
      (App (Val (f @!! go.GoType.PointerType fmt.fmt.ty @!! go!"fmtBoolean")) (Val #v))
    {{ RET #(); fmtOwn f b F wid prec ∗
        bufferOwn b (bs ++ if v then go!"true" else go!"false") }}

end spec

end Perennial
