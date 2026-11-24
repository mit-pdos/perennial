/-
`strings.Count`'s spec.
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

/-- `strings.Count(s, substr)`, for a non-empty `substr`: the number of non-overlapping
occurrences of `substr` in `s`, one less than the fields of `split s substr`. -/
abbrev strings.Count.spec : Prop :=
  ∀ (s substr : GoString),
  substr ≠ [] →
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (App (Val (@! Count)) (Val #s)) (Val #substr))
    {{ RET #(W64 (((split s substr).length - 1 : Nat) : Int)); True }}

end spec

end Perennial
