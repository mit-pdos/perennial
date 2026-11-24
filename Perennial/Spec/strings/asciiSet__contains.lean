/-
`strings.asciiSet__contains`'s spec.
-/
module

public import Perennial.Proof.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- `(*asciiSet).contains(c)`: whether the set `*aset` has `c` (`strings.asciiSetHas`). -/
abbrev strings.asciiSet.contains.spec : Prop :=
  ∀ (aset : Loc) (v : GoArray w32 8) (dq : DFrac) (c : w8),
    {{ (typedPointsto (GF := GF) aset v dq) }}
      (App (Val (aset @!! go.GoType.PointerType strings.asciiSet.ty @!! go!"contains")) (Val #c))
    {{ RET #(strings.asciiSetHas v c); typedPointsto (GF := GF) aset v dq }}

end spec

end Perennial
