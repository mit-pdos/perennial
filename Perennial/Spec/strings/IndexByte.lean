/-
`strings.IndexByte`'s spec.
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

/-- `strings.IndexByte(s, c)`: the first index of `c` in `s`, or `-1`. -/
abbrev strings.IndexByte.spec : Prop :=
  ∀ (s : GoString) (c : w8),
    {{ (True : IProp GF) }}
      (App (App (Val (@! IndexByte)) (Val #s)) (Val #c))
    {{ RET #(W64 (internal.bytealg.indexByte s c)); True }}

end spec

end Perennial
