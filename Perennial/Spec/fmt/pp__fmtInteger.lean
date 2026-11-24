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

/-- `p.fmtInteger(v, isSigned, verb)` for the integer directive `%verb`, `%0Nverb` or `%.Pverb`
(`Mod.IntOk`; the flags, width and precision `doPrintf` sets for it, `Mod.flags`, `Mod.wid`,
`Mod.precW`): appends the decimal (`d`, `v`) or the hexadecimal (`x`, `X` in uppercase) of `v` as
a signed or unsigned integer, zero-padded to the width or the precision (`Mod.intOut`). -/
abbrev fmt.pp.fmtInteger.spec : Prop :=
  ∀ (p : Loc) (x : GoInterface) (bs : GoString) (md : Mod) (v : w64) (isSigned : Bool)
    (verb : w8),
    md.IntOk verb →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ isPrinterA p x bs md.flags md.wid md.precW }}
      (App (App (App (Val (p @!! go.GoType.PointerType pp.ty @!! go!"fmtInteger")) (Val #v)) (Val #isSigned))
        (Val #(W32 (uint.nat verb))))
    {{ RET #(); isPrinterA p x (bs ++ md.intOut verb (if isSigned then sint.Z v else uint.Z v))
        md.flags md.wid md.precW }}

end spec

end Perennial
