/-
`bytes.NewBuffer`'s spec.
-/
module

public import Perennial.Proof.bytes.BufferBasics

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : bytes.Assumptions]

/-- `bytes.NewBuffer(buf)`: a fresh `*Buffer` whose unread content is `buf`'s bytes; it takes
`buf` with its capacity (Go: "The new Buffer takes ownership of buf", and writes grow into its
capacity). -/
abbrev bytes.NewBuffer.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8),
    {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (Val (@! bytes.NewBuffer)) (Val #b))
    {{ (l : Loc), RET #l; bytes.ownBuffer l bs }}

end spec

end Perennial
