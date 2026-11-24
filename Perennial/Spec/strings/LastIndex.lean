/-
`strings.LastIndex`'s spec.
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

/-- `strings.LastIndex(s, substr)`: the last index of `substr` in `s`, or `-1` (`len(s)` for an
empty `substr`). It reads no package variable, so it needs no initialized package. -/
abbrev strings.LastIndex.spec : Prop :=
  ∀ (s substr : GoString),
    {{ (True : IProp GF) }}
      (App (App (Val (@! LastIndex)) (Val #s)) (Val #substr))
    {{ RET #(W64 (strings.lastIndex s substr)); True }}

end spec

end Perennial
