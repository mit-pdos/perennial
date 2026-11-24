/-
`math/rand.Int63`'s spec.
-/
module

public import Perennial.Proof.math.rand.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.rand.Assumptions]

/-- `rand.Int63()`: a non-negative `int64` (Go's documentation: "a non-negative pseudo-random 63-bit
integer as an int64"; the top-level source, safe for concurrent use). -/
abbrev math.rand.Int63.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.math.rand }}
    (App (Val (@! Int63)) (Val #()))
  {{ (x : w64), RET #x; ⌜0 ≤ sint.Z x⌝ }}

end spec

end Perennial
