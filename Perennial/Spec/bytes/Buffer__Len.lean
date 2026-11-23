/-
`bytes.Buffer.Len`'s spec.
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

/-- `b.Len()`: the number of unread bytes, `len(b.buf) - b.off`; it only reads `b`. -/
abbrev bytes.Buffer.Len.spec : Prop :=
  ∀ (l : Loc) (b : bytes.Buffer) (dq : DFrac),
    {{ (l ↦{dq} b : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType bytes.Buffer.ty @!! go!"Len")) (Val #()))
    {{ RET #(b.buf'.len - b.off'); l ↦{dq} b }}

end spec

end Perennial
