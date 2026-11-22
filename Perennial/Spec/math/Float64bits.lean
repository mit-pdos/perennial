/-
`math.Float64bits`'s spec.
-/
module

public import Perennial.Proof.math.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.Assumptions]

/-- `math.Float64bits(f)`: `f`'s bits, which are its representation (`*(*uint64)(unsafe.Pointer(&f))`). -/
abbrev math.Float64bits.spec : Prop :=
  ∀ (f : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.math }}
      (App (Val (@! Float64bits)) (Val #f))
    {{ RET #f; True }}

end spec

end Perennial
