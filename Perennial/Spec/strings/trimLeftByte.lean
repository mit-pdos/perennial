/-
`strings.trimLeftByte`'s spec.
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

/-- `trimLeftByte(s, c)`: `s` without its longest prefix of bytes `c`. -/
abbrev strings.trimLeftByte.spec : Prop :=
  ∀ (s : GoString) (c : w8),
    {{ (True : IProp GF) }}
      (App (App (Val (@! trimLeftByte)) (Val #s)) (Val #c))
    {{ RET #(s.dropWhile (fun b => decide (b = c))); True }}

end spec

end Perennial
