/-
`strings.trimLeftASCII`'s spec.
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

/-- `trimLeftASCII(s, as)`: `s` without its longest prefix of bytes of the set `*aset`. -/
abbrev strings.trimLeftASCII.spec : Prop :=
  ∀ (s : GoString) (aset : Loc) (v : GoArray w32 8) (dq : DFrac),
    {{ (typedPointsto (GF := GF) aset v dq) }}
      (App (App (Val (@! trimLeftASCII)) (Val #s)) (Val #aset))
    {{ RET #(s.dropWhile (strings.asciiSetHas v)); typedPointsto (GF := GF) aset v dq }}

end spec

end Perennial
