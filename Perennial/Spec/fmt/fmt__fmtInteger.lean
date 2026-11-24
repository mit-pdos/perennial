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

/-- `f.fmtInteger(u, base, isSigned, verb, ldigits)` in base 10 or 16, with no flag but `zero`
and a width (at most `10^6`) for zero padding, and no precision: appends `intOut base w z`, `z`
being `u` as a signed or unsigned integer and `w` the width of zero padding (0 if none). A width
without `zero` (padding with spaces) and the flags `#`, `+`, `-`, ` ` are not in the spec. -/
abbrev fmt.fmt.fmtInteger.spec : Prop :=
  ∀ (f b : Loc) (F : fmtFlags) (wid prec : w64) (bs : GoString) (u base : w64) (isSigned : Bool)
    (verb : w32),
    (base = W64 10 ∨ base = W64 16) → verb ≠ W32 79 →
    F.sharp' = false → F.plus' = false → F.space' = false → F.minus' = false →
    F.precPresent' = false →
    (F.widPresent' = true → F.zero' = true ∧ 0 ≤ sint.Z wid ∧ sint.Z wid ≤ 1000000) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ fmtOwn (GF := GF) f b F wid prec ∗ bufferOwn b bs }}
      (App (App (App (App (App (Val (f @!! go.GoType.PointerType fmt.fmt.ty @!! go!"fmtInteger")) (Val #u)) (Val #base))
        (Val #isSigned)) (Val #verb)) (Val #(hexDigits false)))
    {{ RET #(); fmtOwn f b F wid prec ∗
        bufferOwn b (bs ++ intOut (uint.nat base) (if F.widPresent' then sint.nat wid else 0)
          (if isSigned then sint.Z u else uint.Z u)) }}

end spec

end Perennial
