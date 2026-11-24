/-
`fmt.newPrinter`'s spec.
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

/-- `newPrinter()`: a printer (one from the pool `ppFree`, or a new one) with an empty buffer. -/
abbrev fmt.newPrinter.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt }}
      (App (Val (@! newPrinter)) (Val #()))
    {{ (p : Loc), RET #p; ∃ x : GoInterface, isPrinterA p x [] noFlags (W64 0) (W64 0) }}

end spec

end Perennial
