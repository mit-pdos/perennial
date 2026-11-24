/-
`internal.bytealg.MakeNoZero`'s spec.
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

/-- `bytealg.MakeNoZero(n)`, for `n ≥ 0`: a fresh byte slice of length `n` with arbitrary contents
(gc does not zero it), whose whole capacity it owns. It reads no package variable, so it needs no
initialized package. -/
abbrev internal.bytealg.MakeNoZero.spec : Prop :=
  ∀ (n : w64),
    {{ (⌜0 ≤ sint.Z n⌝ : IProp GF) }}
      (App (Val (@! MakeNoZero)) (Val #n))
    {{ (s : GoSlice) (bs : List w8), RET #s;
        s ↦* bs ∗ ownSliceCap w8 s (DFrac.own 1) ∗ ⌜bs.length = sint.nat n⌝ }}

end spec

end Perennial
