/-
`strconv.IsPrint`'s spec.
-/
module

public import Perennial.Proof.strconv.Base

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

/-- `IsPrint(r)`: whether `r` is printable, which it decides by searching the package's tables;
here, some boolean (the tables' contents are not kept, only their lengths). -/
abbrev strconv.IsPrint.spec : Prop :=
  ∀ (r : w32),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strconv }}
      (App (Val (@! IsPrint)) (Val #r))
    {{ (b : Bool), RET #b; True }}

end spec

end Perennial
