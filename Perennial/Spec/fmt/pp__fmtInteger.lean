/-
`fmt.(*pp).fmtInteger`'s spec.
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

/-- `p.fmtInteger(v, isSigned, verb)` for the directive `%verb` or `%0Nverb` (`dirFlags zw`,
`dirWid zw`), `verb` one of `d v x`: appends the decimal (`d`, `v`) or the hexadecimal (`x`) of
`v` as a signed or unsigned integer, zero-padded to `N`. -/
abbrev fmt.pp.fmtInteger.spec : Prop :=
  ∀ (p : Loc) (x : GoInterface) (bs : GoString) (zw : Option Nat) (v : w64) (isSigned : Bool)
    (verb : w8),
    (verb = verb_d ∨ verb = verb_v ∨ verb = verb_x) → ZeroWidthOk zw →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ isPrinterA p x bs (dirFlags zw) (dirWid zw) (W64 0) }}
      (App (App (App (Val (p @!! go.GoType.PointerType pp.ty @!! go!"fmtInteger")) (Val #v)) (Val #isSigned))
        (Val #(W32 (uint.nat verb))))
    {{ RET #(); isPrinterA p x (bs ++ intOut (if verb = verb_x then 16 else 10) (zw.getD 0)
          (if isSigned then sint.Z v else uint.Z v)) (dirFlags zw) (dirWid zw) (W64 0) }}

end spec

end Perennial
