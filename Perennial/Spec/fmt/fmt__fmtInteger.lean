/-
`fmt.(*fmt).fmtInteger`'s spec.
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

/-- `f.fmtInteger(u, base, isSigned, verb, digits)` in base 10 or 16 (`digits` Go's `ldigits`, or
`udigits` for uppercase hexadecimal), with no flag but `zero`, and either a width (at most `10^6`,
the precision field 0) for zero padding, or a precision (at most `10^6`, no width, the width field
0): appends `widthPad base upper w z` (`w` the width of zero padding, 0 if none), or
`precPad base upper P z` for the precision `P`, `z` being `u` as a signed or unsigned integer. A
width without `zero` (padding with spaces), a width with a precision, and the flags `#`, `+`, `-`,
` ` are not in the spec. -/
abbrev fmt.fmt.fmtInteger.spec : Prop :=
  ∀ (f b : Loc) (F : fmtFlags) (wid prec : w64) (bs : GoString) (u base : w64) (isSigned : Bool)
    (verb : w32) (upper : Bool),
    (base = W64 10 ∨ base = W64 16) → verb ≠ W32 79 →
    F.sharp' = false → F.plus' = false → F.space' = false → F.minus' = false →
    (F.precPresent' = true → F.widPresent' = false ∧ wid = W64 0 ∧ 0 ≤ sint.Z prec ∧
      sint.Z prec ≤ 1000000) →
    (F.widPresent' = true → F.zero' = true ∧ 0 ≤ sint.Z wid ∧ sint.Z wid ≤ 1000000 ∧
      prec = W64 0) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ fmtOwn (GF := GF) f b F wid prec ∗ intbufOwn f ∗ bufferOwn b bs }}
      (App (App (App (App (App (Val (f @!! go.GoType.PointerType fmt.fmt.ty @!! go!"fmtInteger")) (Val #u)) (Val #base))
        (Val #isSigned)) (Val #verb)) (Val #(hexDigits upper)))
    {{ RET #(); fmtOwn f b F wid prec ∗ intbufOwn f ∗
        bufferOwn b (bs ++ (if F.precPresent' then
            precPad (uint.nat base) upper (sint.nat prec) (if isSigned then sint.Z u else uint.Z u)
          else widthPad (uint.nat base) upper (if F.widPresent' then sint.nat wid else 0)
            (if isSigned then sint.Z u else uint.Z u))) }}

end spec

end Perennial
