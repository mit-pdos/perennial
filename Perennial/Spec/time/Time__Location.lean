/-
`time.Time.Location`'s spec.
-/
module

public import Perennial.Proof.time.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- `t.Location()`: `t`'s location, or the global `UTC` when it has none (a nil `loc`). It reads
the global `UTC`, hence the package's `isPkgInit`. -/
abbrev time.Time.Location.spec : Prop :=
  ∀ (t : time.Time),
    {{ isPkgInit (PROP := IProp GF) pkg_id.time }}
      (App (Val (t @!! time.Time.ty @!! go!"Location")) (Val #()))
    {{ (l : Loc), RET #l; ⌜t.loc' ≠ Loc.null → l = t.loc'⌝ }}

end spec

end Perennial
