/-
`fmt.(*fmt).fmtSbx`'s spec.
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

/-- `f.fmtSbx(s, p, digits)` without a width, precision, `#` or ` `: appends the hexadecimal
(`digits` lowercase or uppercase) of the bytes `ys` of `p`, or of `s` if `p` is `nil`. -/
abbrev fmt.fmt.fmtSbx.spec : Prop :=
  ∀ (f b : Loc) (F : fmtFlags) (wid prec : w64) (bs s : GoString) (sl : GoSlice) (ys : GoString)
    (q : DFrac) (upper : Bool),
    F.precPresent' = false → F.widPresent' = false → F.sharp' = false → F.space' = false →
    {{ fmtOwn (GF := GF) f b F wid prec ∗ bufferOwn b bs ∗ sl ↦*{q} ys }}
      (App (App (App (Val (f @!! go.GoType.PointerType fmt.fmt.ty @!! go!"fmtSbx")) (Val #s)) (Val #sl))
        (Val #(hexDigits upper)))
    {{ RET #(); fmtOwn f b F wid prec ∗
        bufferOwn b (bs ++ bytesHex upper (if sl = slice.nil then s else ys)) ∗ sl ↦*{q} ys }}

end spec

end Perennial
