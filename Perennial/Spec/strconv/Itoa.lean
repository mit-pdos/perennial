/-
`strconv.Itoa`'s spec.
-/
module

public import Perennial.Proof.strconv.Base
public import Perennial.Proof.internal.strconv.FormatBasics

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strconv.Assumptions]

/-- `strconv.Itoa(i)`: `FormatInt(i, 10)`, the decimal form of `i`. -/
abbrev strconv.Itoa.spec : Prop :=
  ∀ (i : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strconv }}
      (App (Val (@! Itoa)) (Val #i))
    {{ RET #(internal.strconv.fmtInt i (W64 10)); True }}

end spec

end Perennial
