/-
`unicode/utf8.RuneCount`'s spec.
-/
module

public import Perennial.Proof.unicode.utf8.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : unicode.utf8.Assumptions]

/-- `RuneCount(p)` of ASCII bytes `ys`: their number. -/
abbrev unicode.utf8.RuneCount.spec : Prop :=
  ∀ (sl : GoSlice) (ys : GoString) (q : DFrac),
    (∀ c ∈ ys, uint.Z c < 128) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.unicode.utf8 ∗ sl ↦*{q} ys }}
      (App (Val (@! RuneCount)) (Val #sl))
    {{ RET #(W64 ys.length); sl ↦*{q} ys }}

end spec

end Perennial
