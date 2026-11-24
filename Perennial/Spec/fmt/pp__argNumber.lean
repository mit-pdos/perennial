/-
`fmt.(*pp).argNumber`'s spec.
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

/-- `p.argNumber(argNum, format, i, numArgs)` where `format[i]` is not `[` (or `i` is past the end):
no argument index, `(argNum, i, false)`. -/
abbrev fmt.pp.argNumber.spec : Prop :=
  ∀ (p : Loc) (argNum : w64) (format : GoString) (i numArgs : w64),
    0 ≤ sint.Z i → (format[sint.nat i]? ≠ some (W8 91)) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt }}
      (App (App (App (App (Val (p @!! go.GoType.PointerType pp.ty @!! go!"argNumber")) (Val #argNum)) (Val #format))
        (Val #i)) (Val #numArgs))
    {{ RET (PairV (PairV #argNum #i) #false); True }}

end spec

end Perennial
