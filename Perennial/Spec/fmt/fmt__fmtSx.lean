/-
`fmt.(*fmt).fmtSx`'s spec.
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

/-- `f.fmtSx(s, digits)` without a width, precision, `#` or ` `: appends the hexadecimal of `s`. -/
abbrev fmt.fmt.fmtSx.spec : Prop :=
  ∀ (f b : Loc) (F : fmtFlags) (wid prec : w64) (bs s : GoString) (upper : Bool),
    F.precPresent' = false → F.widPresent' = false → F.sharp' = false → F.space' = false →
    s.length < 2 ^ 62 →
    {{ fmtOwn (GF := GF) f b F wid prec ∗ bufferOwn b bs }}
      (App (App (Val (f @!! go.GoType.PointerType fmt.fmt.ty @!! go!"fmtSx")) (Val #s)) (Val #(hexDigits upper)))
    {{ RET #(); fmtOwn f b F wid prec ∗ bufferOwn b (bs ++ bytesHex upper s) }}

end spec

end Perennial
