/-
`internal.bytealg.IndexString`'s spec.
-/
module

public import Perennial.Proof.internal.bytealg.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

/-- `bytealg.IndexString(a, b)`: the first index of `b` in `a`, or `-1`, for a `b` of at least 2
and at most `MaxLen` bytes (its documented precondition; outside it the Go model,
`goose/model/overlay/internal/bytealg/index_native.go`, does not terminate). The caller gives
`MaxLen`'s value `m` (from `bytealg`'s `isPkgInit`, `internal.bytealg.isInit`). -/
abbrev internal.bytealg.IndexString.spec : Prop :=
  ∀ (a b : GoString) (m : w64),
    {{ (globalAddr MaxLen ↦□ m : IProp GF) ∗ ⌜2 ≤ b.length ∧ (b.length : Int) ≤ sint.Z m⌝ }}
      (App (App (Val (@! IndexString)) (Val #a)) (Val #b))
    {{ RET #(W64 (internal.bytealg.index a b)); True }}

end spec

end Perennial
